import Solution.Secp256k1ScalarMul.Step
import Solution.Secp256k1ScalarMul.ToBytes
import Solution.Secp256k1ScalarMul.ScalarMulTheorems
import Challenge.Utils.ComputableWitnessLemmas

/-!
# secp256k1 variable-base scalar multiplication — reference circuit

The top-level reference gadget: naive MSB-first double-and-add over the
scalar bits, using the complete addition gadget for both the doubling (a
self-add) and the conditional add, and a materialized mux (`Mux`) on the
bit — a direct transcription of `Specs.ShortWeierstrass.scalarMul`:

  for each bit:  acc ← acc + acc;  acc ← if bit then acc + P else acc

The accumulator is a flagged point starting at the point at infinity, and the
output carries an is-infinity flag, so the circuit satisfies the *total* spec
(`Specs.Secp256k1ScalarMul.Spec`) for every sequence of bits — no
excluded scalars.

## Output format

The output is byte-encoded, SEC1/RSA-interface style: each coordinate is 32
**big-endian** bytes (`x[0]` is the most significant byte), plus a boolean
is-infinity flag. The coordinate bytes are masked to zero when the flag is
set, so every group element has exactly one wire encoding. All output wires
are fresh witness variables (affine, degree 1): the bytes come from
`ToBytes`, the mask and the flag from `Mux` — no high-degree selection
expressions are exposed.

This is deliberately simple and inefficient (two complete additions and a
point mux per bit, ≈ 512 complete adds); it is a baseline, not a golfed
solution.


The big-integer layer (`Theorems`, `Normalize`, `LessThan`, `Equal`,
`EqViaCarries`, `MulMod`) is copied from the RSA solution (solutions must be
independent, so it is duplicated rather than imported) with the namespace
renamed; those files carry their full original proofs.
-/

namespace Solution.Secp256k1ScalarMul
namespace ScalarMul

/-- Inputs of `ScalarMul`: the scalar as bits (most significant first) and
the affine coordinates of the base point. -/
structure Inputs (F : Type) where
  bits : Vector F Specs.Secp256k1.scalarBits
  px : Emu F
  py : Emu F
deriving ProvableStruct

/-- The loop body allocates a constant number of cells (one `Step`
subcircuit). Passed to `Circuit.foldlRange` explicitly because the default
synthesis tactic times out unfolding the nested gadget tree (cf. the same
pattern in Clean's `SHA256Schedule`). -/
private def constantLength (input : Var Inputs (F circomPrime)) :
    Circuit.ConstantLength
      (fun (x : Var FlaggedPoint (F circomPrime) × Fin Specs.Secp256k1.scalarBits) =>
        subcircuit Step.circuit
          { acc := x.1, px := input.px, py := input.py, bit := input.bits[x.2] }) where
  localLength := 31959
  localLength_eq _ _ := by
    simp [circuit_norm, Step.circuit, Step.elaborated,
      CompleteAdd.circuit, CompleteAdd.elaborated, CompleteAdd.main,
      DivOrZero.circuit, DivOrZero.elaborated, DivOrZero.main,
      IsZeroFe.circuit, IsZeroFe.elaborated, IsZeroFe.main,
      AddMod.circuit, AddMod.elaborated, AddMod.main,
      SubMod.circuit, SubMod.elaborated, SubMod.main,
      MulMod.circuit, MulMod.elaborated, MulMod.witnessedMul,
      Normalize.circuit, Normalize.elaborated, Normalize.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main,
      Equal.circuit, Equal.elaborated, Equal.main,
      EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      Mux.circuit, Mux.elaborated, Mux.main, Gadgets.IsZeroField.circuit,
      secpParams, Gadgets.ToBits.rangeCheck, numLimbs, limbBits]

/-- Constant zero byte vector. -/
def zeroBytes : Var (fields coordBytes) (F circomPrime) :=
  Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime))

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  -- double-and-add over the bits
  let acc ← Circuit.foldlRange Specs.Secp256k1.scalarBits infConst
    (fun acc i =>
      subcircuit Step.circuit
        { acc := acc, px := input.px, py := input.py, bit := input.bits[i] })
    (constantLength input)

  -- byte-decompose the coordinates (little-endian from `ToBytes`)
  let xb ← subcircuit ToBytes.circuit acc.x
  let yb ← subcircuit ToBytes.circuit acc.y

  -- mask the bytes to zero when the result is the point at infinity
  let xm ← subcircuit (Mux.circuit (M := fields coordBytes))
    { selector := acc.isInf, ifTrue := zeroBytes, ifFalse := xb }
  let ym ← subcircuit (Mux.circuit (M := fields coordBytes))
    { selector := acc.isInf, ifTrue := zeroBytes, ifFalse := yb }

  -- expose big-endian byte order (index 0 = most significant byte)
  return {
    x := Vector.ofFn fun i : Fin coordBytes => xm[coordBytes - 1 - i.val]'(by omega)
    y := Vector.ofFn fun i : Fin coordBytes => ym[coordBytes - 1 - i.val]'(by omega)
    isInf := acc.isInf
  }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

/-- Preconditions: the scalar entries are bits, and the base point has
canonical coordinates and lies on the curve. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin Specs.Secp256k1.scalarBits, IsBool (input.bits[i])) ∧
  Fe.Valid input.px ∧ Fe.Valid input.py ∧
  Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
    { x := decodeFe input.px, y := decodeFe input.py }

/-- Postcondition: the output encoding is well-formed and the decoded
input/output pair satisfies the trusted total spec
(`Specs.Secp256k1ScalarMul.Spec`). -/
def Spec (input : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  out.Valid ∧
    Specs.Secp256k1ScalarMul.Spec (input.bits.map ZMod.val)
      { x := decodeFe input.px, y := decodeFe input.py }
      (decodeOutput out)

set_option maxRecDepth 8192 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_steps, h_tbx, h_tby, h_muxx, h_muxy⟩ := h_holds
  obtain ⟨h_bits, h_px, h_py⟩ := h_input
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange] at h_steps
  simp only [circuit_norm] at h_steps
  simp only [step_localLength, step_output, fin_foldl_eq_accVar] at h_steps
  simp only [step_localLength, step_output, fin_foldl_eq_accVar, toBytes_localLength,
    toBytes_output, mux_localLength, mux_output] at h_tbx h_tby h_muxx h_muxy
  norm_num [Specs.Secp256k1.scalarBits] at h_tbx h_tby h_muxx h_muxy
  simp only [secpParams, numLimbs, limbBits, Specs.Secp256k1.scalarBits, coordBytes,
    List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT,
    reduceIte, reduceDIte, fin_foldl_goal_eq_accVar]
  obtain ⟨hbits_bool, hpx_valid, hpy_valid, honcurve⟩ := h_assumptions
  obtain ⟨hbool, hfx, hfy, -, hdec256⟩ :=
    fold_invariant i₀ env input_bits input_px input_py input_var_bits h_bits
      hbits_bool hpx_valid hpy_valid honcurve h_steps 256 (le_refl 256)
  unfold ToBytes.circuit ToBytes.Assumptions ToBytes.Spec at h_tbx h_tby
  unfold Mux.circuit Mux.Assumptions Mux.Spec at h_muxx h_muxy
  dsimp only [] at h_tbx h_tby h_muxx h_muxy
  obtain ⟨hxb_bytes, hxb_val⟩ := h_tbx hfx.1
  obtain ⟨hyb_bytes, hyb_val⟩ := h_tby hfy.1
  have hmx := h_muxx hbool
  have hmy := h_muxy hbool
  exact ⟨⟨output_valid i₀ env zeroBytes rfl hbool hfx hfy hxb_bytes hxb_val
        hyb_bytes hyb_val hmx hmy,
      output_spec i₀ env input_bits input_px input_py zeroBytes hbool hdec256
        hxb_val hyb_val hmx hmy⟩,
    fun i => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

set_option maxRecDepth 8192 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start
  obtain ⟨h_bits, h_px, h_py⟩ := h_input
  obtain ⟨hbits_bool, hpx_valid, hpy_valid, honcurve⟩ := h_assumptions
  obtain ⟨h_steps, -, -, -, -⟩ := h_env
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange] at h_steps
  simp only [circuit_norm] at h_steps
  simp only [step_localLength, step_output, fin_foldl_eq_accVar] at h_steps
  have h_inv := fold_invariant i₀ env.toEnvironment input_bits input_px input_py
    input_var_bits h_bits hbits_bool hpx_valid hpy_valid honcurve h_steps
  obtain ⟨hbool, hfx, hfy, -, -⟩ := h_inv 256 (le_refl 256)
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · -- Step assumptions at each fold index
    simp only [foldlAcc_eq_accVar]
    obtain ⟨ib, ifx, ify, icurve, -⟩ := h_inv i.val (le_of_lt i.isLt)
    have hbit : IsBool (Expression.eval env.toEnvironment input_var_bits[i.val]) := by
      have h := hbits_bool i
      rwa [← h_bits, Vector.getElem_map] at h
    exact ⟨⟨ib, ifx, ify, icurve⟩, hbit, hpx_valid, hpy_valid, honcurve⟩
  · -- ToBytes assumptions (x)
    unfold ToBytes.circuit ToBytes.Assumptions
    dsimp only []
    simp only [step_localLength, step_output, fin_foldl_eq_accVar]
    exact hfx.1
  · -- ToBytes assumptions (y)
    unfold ToBytes.circuit ToBytes.Assumptions
    dsimp only []
    simp only [step_localLength, step_output, fin_foldl_eq_accVar]
    exact hfy.1
  · -- Mux assumptions (x mask)
    unfold Mux.circuit Mux.Assumptions
    dsimp only []
    simp only [step_localLength, step_output, fin_foldl_eq_accVar]
    exact hbool
  · -- Mux assumptions (y mask)
    unfold Mux.circuit Mux.Assumptions
    dsimp only []
    simp only [step_localLength, step_output, fin_foldl_eq_accVar]
    exact hbool

set_option maxRecDepth 8192 in
/-- The reference scalar-multiplication circuit: naive double-and-add with
complete additions, total on every bit string, with big-endian byte outputs. -/
def circuit : FormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated; Assumptions; Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h

/-! ## Computable witnesses -/

/-- The output of the double-and-add fold at the top-level offset is the full
`accVar` accumulator, `accVar offset scalarBits`. The step output offsets do not
depend on the running accumulator, so the fold degenerates to `accVar`. -/
lemma foldl_output_eq_accVar (offset : ℕ)
    (bits : Vector (Expression (F circomPrime)) Specs.Secp256k1.scalarBits)
    (px py : Emu (Expression (F circomPrime))) :
    (Circuit.foldlRange Specs.Secp256k1.scalarBits infConst
      (fun acc (i : Fin Specs.Secp256k1.scalarBits) =>
        subcircuit Step.circuit
          { acc := acc, px := px, py := py, bit := bits[i] })
      (constantLength { bits := bits, px := px, py := py })).output offset
      = accVar offset Specs.Secp256k1.scalarBits := by
  rw [Circuit.foldlRange.output_eq]
  simp only [circuit_norm]
  simp only [step_output, step_localLength]
  exact fin_foldl_eq_accVar offset Specs.Secp256k1.scalarBits

attribute [local irreducible] main

/-- Stability of a `ToBytes` subcircuit output, stated in the `circuit.output`
form that appears after `circuit_norm` normalizes a `subcircuit` output. Crosses
to `ToBytes.eval_output_of_agreesBelow` once via the cheap `elaborated.output_eq`
so `exact` need not `whnf` the whole `ToBytes.main`. -/
private lemma toBytes_output_stable (X : Var Emu (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : o + 288 ≤ k) :
    eval env (ToBytes.circuit.output X o) = eval env' (ToBytes.circuit.output X o) := by
  have h := ToBytes.eval_output_of_agreesBelow X (offset := o) h_agree (by
    rw [toBytes_localLength]; exact hk)
  rw [ToBytes.elaborated.output_eq X o] at h
  exact h

set_option maxRecDepth 8192 in
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  apply Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  show Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
    input env env' offset ((main input).operations offset)
  have hstep : ∀ (X : Var Step.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit Step.circuit X).localLength o = 31959 := fun _ _ => rfl
  have htb : ∀ (X : Var Emu (F circomPrime)) (o : ℕ),
      (subcircuit ToBytes.circuit X).localLength o = 288 := fun _ _ => rfl
  have hmux : ∀ (X : Var (Mux.Inputs (fields coordBytes)) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := fields coordBytes)) X).localLength o = 32 := fun _ _ => rfl
  have hfold : ∀ (o : ℕ),
      (Circuit.foldlRange Specs.Secp256k1.scalarBits infConst
        (fun acc (i : Fin Specs.Secp256k1.scalarBits) =>
          subcircuit Step.circuit
            { acc := acc, px := input.px, py := input.py, bit := input.bits[i] })
        (constantLength input)).localLength o = 8181504 := by
    intro o
    simp only [Circuit.foldlRange.localLength_eq, Specs.Secp256k1.scalarBits, hstep, Nat.reduceMul]
    rw [dif_pos (show (256 : ℕ) > 0 by norm_num)]
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.foldlRange_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hstep, htb, hmux, hfold, and_true]
  obtain ⟨bits, px, py⟩ := input
  dsimp only []
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- loop body: Step at each fold index
    intro i
    rw [foldlAcc_eq_accVar_main offset px py bits i]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) Step.circuit _ _ _ ?_ Step.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    have hacc := eval_accVar_of_agreesBelow offset i.val
      (ProverEnvironment.agreesBelow_of_le h_agree hle)
    simp only [circuit_norm, Inputs.mk.injEq] at h_in
    obtain ⟨hbits, hpx, hpy⟩ := h_in
    have hbit : Expression.eval e.toEnvironment bits[i.val] =
        Expression.eval e'.toEnvironment bits[i.val] := by
      have := Vector.ext_iff.mp hbits i.val i.isLt
      simpa only [Vector.getElem_map] using this
    simp only [circuit_norm, Step.Inputs.mk.injEq, FlaggedPoint.mk.injEq] at hacc ⊢
    exact ⟨⟨hacc.1, hacc.2.1, hacc.2.2⟩, hpx, hpy, hbit⟩
  · -- ToBytes on acc.x
    rw [foldl_output_eq_accVar offset bits px py]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ToBytes.circuit _ (accVar offset Specs.Secp256k1.scalarBits).x
      (offset + 8181504) ?_ ToBytes.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    exact eval_accVar_x_of_agreesBelow offset Specs.Secp256k1.scalarBits
      (ProverEnvironment.agreesBelow_of_le h_agree (by simp only [Specs.Secp256k1.scalarBits]; omega))
  · -- ToBytes on acc.y
    rw [foldl_output_eq_accVar offset bits px py]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ToBytes.circuit _ (accVar offset Specs.Secp256k1.scalarBits).y
      (offset + 8181504 + 288) ?_ ToBytes.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    exact eval_accVar_y_of_agreesBelow offset Specs.Secp256k1.scalarBits
      (ProverEnvironment.agreesBelow_of_le h_agree (by simp only [Specs.Secp256k1.scalarBits]; omega))
  · -- Mux on the x bytes
    rw [foldl_output_eq_accVar offset bits px py]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := fields coordBytes)) _
      { selector := (accVar offset Specs.Secp256k1.scalarBits).isInf, ifTrue := zeroBytes,
        ifFalse := (subcircuit ToBytes.circuit (accVar offset Specs.Secp256k1.scalarBits).x).output
          (offset + 8181504) }
      (offset + 8181504 + 288 + 288) ?_ (Mux.computableWitnesses (M := fields coordBytes)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Mux.Inputs.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · exact eval_accVar_isInf_of_agreesBelow offset Specs.Secp256k1.scalarBits
        (ProverEnvironment.agreesBelow_of_le h_agree (by simp only [Specs.Secp256k1.scalarBits]; omega))
    · apply Vector.ext; intro j hj; simp [zeroBytes, Expression.eval]
    · have hxb := toBytes_output_stable (accVar offset Specs.Secp256k1.scalarBits).x
        (o := offset + 8181504) h_agree (by omega)
      simp only [circuit_norm] at hxb ⊢
      exact hxb
  · -- Mux on the y bytes
    rw [foldl_output_eq_accVar offset bits px py]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := fields coordBytes)) _
      { selector := (accVar offset Specs.Secp256k1.scalarBits).isInf, ifTrue := zeroBytes,
        ifFalse := (subcircuit ToBytes.circuit (accVar offset Specs.Secp256k1.scalarBits).y).output
          (offset + 8181504 + 288) }
      (offset + 8181504 + 288 + 288 + 32) ?_ (Mux.computableWitnesses (M := fields coordBytes)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Mux.Inputs.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · exact eval_accVar_isInf_of_agreesBelow offset Specs.Secp256k1.scalarBits
        (ProverEnvironment.agreesBelow_of_le h_agree (by simp only [Specs.Secp256k1.scalarBits]; omega))
    · apply Vector.ext; intro j hj; simp [zeroBytes, Expression.eval]
    · have hyb := toBytes_output_stable (accVar offset Specs.Secp256k1.scalarBits).y
        (o := offset + 8181504 + 288) h_agree (by omega)
      simp only [circuit_norm] at hyb ⊢
      exact hyb

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end ScalarMul
end Solution.Secp256k1ScalarMul

