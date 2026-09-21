import Solution.Bls12381G1ScalarMul.Step
import Solution.Bls12381G1ScalarMul.ToBytes
import Solution.Bls12381G1ScalarMul.ScalarMulTheorems
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
(`Specs.Bls12381G1ScalarMul.Spec`) for every sequence of bits — no
excluded scalars.

## Output format

The output is byte-encoded, SEC1/RSA-interface style: each coordinate is 48
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

namespace Solution.Bls12381G1ScalarMul
namespace ScalarMul

/-- Inputs of `ScalarMul`: the scalar as bits (most significant first) and
the affine coordinates of the base point. -/
structure Inputs (F : Type) where
  bits : Vector F Specs.Bls12381G1.scalarBits
  px : Emu F
  py : Emu F
deriving ProvableStruct

/-- The loop body allocates a constant number of cells (one `Step`
subcircuit). Passed to `Circuit.foldlRange` explicitly because the default
synthesis tactic times out unfolding the nested gadget tree (cf. the same
pattern in Clean's `SHA256Schedule`). -/
@[reducible] private def constantLength (input : Var Inputs (F circomPrime)) :
    Circuit.ConstantLength
      (fun (x : Var FlaggedPoint (F circomPrime) × Fin Specs.Bls12381G1.scalarBits) =>
        subcircuit Step.circuit
          { acc := x.1, px := input.px, py := input.py, bit := input.bits[x.2] }) where
  localLength := 49099
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
  let acc ← Circuit.foldlRange Specs.Bls12381G1.scalarBits infConst
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

set_option maxRecDepth 8192 in
/-- The elaborated data is pinned to closed forms: the total local length as a
numeral, and the output as the two masked byte blocks (read big-endian) plus the
fold accumulator's is-infinity flag. Left to `elaborate_circuit`, both carry the
loop's offset arithmetic symbolically (`scalarBits`, `numLimbs`, `secpParams.B`,
`secpParams.W` never collapse), and the struct-eval simprocs then validate their
rewrites by `isDefEq` on that unreduced tree, which explodes. -/
instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit_with {
    localLength _ := 12521205
    output _ i₀ := {
      x := Vector.ofFn fun i : Fin coordBytes =>
        var { index := i₀ + 12520245 + 432 + 432 + (47 - i.val) }
      y := Vector.ofFn fun i : Fin coordBytes =>
        var { index := i₀ + 12520245 + 432 + 432 + 48 + (47 - i.val) }
      isInf := var { index := i₀ + 12520232 + 12 } }
  } using by
    -- `secpParams` is unfolded through its two numeric fields: unfolding the whole
    -- structure drags in its `by decide` proof fields and blows the whnf budget.
    have hB : secpParams.B = limbBits := rfl
    have hW : secpParams.W = 69 := rfl
    refine ⟨fun a => rfl, fun a i₀ => ?_, ?_⟩
    · simp only [circuit_norm]
      simp only [hB, hW, numLimbs, limbBits, Specs.Bls12381G1.scalarBits, coordBytes,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, reduceIte,
        fin_foldl_goal_eq_accVar, accVar_isInf]
      exact ⟨trivial, trivial, trivial⟩
    · intro a ha; exact ha

/-- Preconditions: the scalar entries are bits, and the base point has
canonical coordinates and lies on the curve. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin Specs.Bls12381G1.scalarBits, IsBool (input.bits[i])) ∧
  Fe.Valid input.px ∧ Fe.Valid input.py ∧
  Specs.ShortWeierstrass.OnCurve Specs.Bls12381G1.curve
    { x := decodeFe input.px, y := decodeFe input.py } ∧
  -- the G1 group has a nontrivial cofactor, so the base point must be
  -- assumed to lie in the prime-order subgroup (the output does too)
  Specs.Bls12381G1.InSubgroup (.affine
    { x := decodeFe input.px, y := decodeFe input.py })

/-- Postcondition: the output encoding is well-formed and the decoded
input/output pair satisfies the trusted total spec
(`Specs.Bls12381G1ScalarMul.Spec`). -/
def Spec (input : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  out.Valid ∧
    Specs.Bls12381G1ScalarMul.Spec (input.bits.map ZMod.val)
      { x := decodeFe input.px, y := decodeFe input.py }
      (decodeOutput out)

/-- A boolean field element has `val < 2`. -/
lemma val_lt_two_of_isBool {x : F circomPrime} (h : IsBool x) : x.val < 2 := by
  rcases h with h0 | h1
  · rw [h0]; simp
  · rw [h1, show (1 : F circomPrime) = ((1 : ℕ) : F circomPrime) from rfl,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by decide)]
    norm_num

set_option maxRecDepth 8192 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [step_localLength, step_output_mk]
  obtain ⟨h_steps, h_tbx, h_tby, h_muxx, h_muxy⟩ := h_holds
  obtain ⟨h_bits, h_px, h_py⟩ := h_input
  simp only [flaggedPointVar_mk] at h_steps h_tbx h_tby h_muxx h_muxy ⊢
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange] at h_steps
  simp only [circuit_norm] at h_steps
  simp only [step_localLength, step_output, fin_foldl_eq_accVar] at h_steps
  -- `varFromOffset` on a `ProvableStruct` no longer iota-reduces through `eval`,
  -- so decompose it explicitly; otherwise the loop-body spec stays wrapped in
  -- `fromComponents (eval.go …)` and every later unification has to grind
  -- through it.
  simp only [circuit_norm, explicit_provable_type] at h_steps
  simp only [eval_flaggedPoint_mk] at h_steps
  simp only [step_localLength, step_output, fin_foldl_eq_accVar, toBytes_localLength,
    toBytes_output, mux_localLength, mux_output] at h_tbx h_tby h_muxx h_muxy
  simp only [eval_flaggedPoint_mk, Mux.circuit, Mux.Assumptions, Mux.Spec] at h_muxx h_muxy
  norm_num [Specs.Bls12381G1.scalarBits] at h_tbx h_tby h_muxx h_muxy
  simp only [secpParams, numLimbs, limbBits, Specs.Bls12381G1.scalarBits, coordBytes,
    List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT,
    reduceIte, reduceDIte, fin_foldl_goal_eq_accVar]
  rw [env_get_eq_accVar_isInf env i₀]
  obtain ⟨hbits_bool, hpx_valid, hpy_valid, honcurve, hsub⟩ := h_assumptions
  obtain ⟨hbool, hfx, hfy, -, hdec256⟩ :=
    fold_invariant i₀ env input_bits input_px input_py input_var_bits h_bits
      hbits_bool hpx_valid hpy_valid honcurve
      -- `eval` of the loop output is left as `fromComponents (eval.go …)` by
      -- `circuit_norm` (the components list no longer iota-reduces on a
      -- non-constructor), so bridge it to the record form field-wise instead of
      -- letting the unifier grind through it.
      (fun i hA => by
        have h := h_steps i hA
        convert h using 2 <;> simp only [circuit_norm, explicit_provable_type])
      255 (le_refl 255)
  unfold ToBytes.circuit ToBytes.Assumptions ToBytes.Spec at h_tbx h_tby
  dsimp only [] at h_tbx h_tby
  obtain ⟨hxb_bytes, hxb_val⟩ := h_tbx hfx.1
  obtain ⟨hyb_bytes, hyb_val⟩ := h_tby hfy.1
  -- the `Mux` input struct stays in its `fromComponents` form; feed/read the
  -- spec through the structural bridges instead of unfolding it
  have hmx := h_muxx hbool
  have hmy := h_muxy hbool
  have hbits_arr : Specs.ShortWeierstrass.IsBitArray
      (Vector.map ZMod.val input_bits) := by
    intro i
    simpa using val_lt_two_of_isBool (hbits_bool i)
  exact ⟨⟨output_valid i₀ env zeroBytes rfl hbool hfx hfy hxb_bytes hxb_val
        hyb_bytes hyb_val hmx hmy,
      output_spec i₀ env input_bits input_px input_py zeroBytes hbool hdec256
        hxb_val hyb_val hmx hbits_arr honcurve hsub hmy⟩,
    fun i => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

set_option maxRecDepth 8192 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [step_localLength, step_output_mk]
  obtain ⟨h_bits, h_px, h_py⟩ := h_input
  obtain ⟨hbits_bool, hpx_valid, hpy_valid, honcurve, -⟩ := h_assumptions
  obtain ⟨h_steps, -, -, -, -⟩ := h_env
  simp only [flaggedPointVar_mk] at h_steps ⊢
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange] at h_steps
  simp only [circuit_norm] at h_steps
  simp only [step_localLength, step_output, fin_foldl_eq_accVar] at h_steps
  -- see the note in `soundness`: decompose `varFromOffset` on the loop output so
  -- the per-step spec is a record literal again
  simp only [circuit_norm, explicit_provable_type] at h_steps
  simp only [eval_flaggedPoint_mk] at h_steps
  have h_inv := fold_invariant i₀ env.toEnvironment input_bits input_px input_py
    input_var_bits h_bits hbits_bool hpx_valid hpy_valid honcurve
    (fun i hA => by
      have h := h_steps i hA
      convert h using 2 <;> simp only [circuit_norm, explicit_provable_type])
  obtain ⟨hbool, hfx, hfy, -, -⟩ := h_inv 255 (le_refl 255)
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · -- Step assumptions at each fold index
    simp only [foldlAcc_eq_accVar]
    obtain ⟨ib, ifx, ify, icurve, -⟩ := h_inv i.val (le_of_lt i.isLt)
    have hbit : IsBool (Expression.eval env.toEnvironment input_var_bits[i.val]) := by
      have h := hbits_bool i
      rwa [← h_bits, Vector.getElem_map] at h
    simp only [eval_flaggedPoint_mk]
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
    simp only [step_localLength, step_output, fin_foldl_eq_accVar, eval_flaggedPoint_mk,
      Mux.circuit, Mux.Assumptions]
    exact hbool
  · -- Mux assumptions (y mask)
    simp only [step_localLength, step_output, fin_foldl_eq_accVar, eval_flaggedPoint_mk,
      Mux.circuit, Mux.Assumptions]
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
    (bits : Vector (Expression (F circomPrime)) Specs.Bls12381G1.scalarBits)
    (px py : Emu (Expression (F circomPrime))) :
    (Circuit.foldlRange Specs.Bls12381G1.scalarBits infConst
      (fun acc (i : Fin Specs.Bls12381G1.scalarBits) =>
        subcircuit Step.circuit
          { acc := acc, px := px, py := py, bit := bits[i] })
      (constantLength { bits := bits, px := px, py := py })).output offset
      = accVar offset Specs.Bls12381G1.scalarBits := by
  rw [Circuit.foldlRange.output_eq]
  simp only [circuit_norm]
  simp only [step_output, step_localLength]
  exact fin_foldl_eq_accVar offset Specs.Bls12381G1.scalarBits

attribute [local irreducible] main

/-- Stability of a `ToBytes` subcircuit output, stated in the `circuit.output`
form that appears after `circuit_norm` normalizes a `subcircuit` output. Crosses
to `ToBytes.eval_output_of_agreesBelow` once via the cheap `elaborated.output_eq`
so `exact` need not `whnf` the whole `ToBytes.main`. -/
private lemma toBytes_output_stable (X : Var Emu (F circomPrime)) {o k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : o + 432 ≤ k) :
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
      (subcircuit Step.circuit X).localLength o = 49099 := fun _ _ => rfl
  have htb : ∀ (X : Var Emu (F circomPrime)) (o : ℕ),
      (subcircuit ToBytes.circuit X).localLength o = 432 := fun _ _ => rfl
  have hmux : ∀ (X : Var (Mux.Inputs (fields coordBytes)) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := fields coordBytes)) X).localLength o = 48 := fun _ _ => rfl
  have hfold : ∀ (o : ℕ),
      (Circuit.foldlRange Specs.Bls12381G1.scalarBits infConst
        (fun acc (i : Fin Specs.Bls12381G1.scalarBits) =>
          subcircuit Step.circuit
            { acc := acc, px := input.px, py := input.py, bit := input.bits[i] })
        (constantLength input)).localLength o = 12520245 := by
    intro o
    simp only [Circuit.foldlRange.localLength_eq, Specs.Bls12381G1.scalarBits, hstep, Nat.reduceMul]
    rw [dif_pos (show (255 : ℕ) > 0 by norm_num)]
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
    exact Step.eval_inputs_mk hacc (by simp only [circuit_norm]; exact hpx)
      (by simp only [circuit_norm]; exact hpy) hbit
  · -- ToBytes on acc.x
    rw [foldl_output_eq_accVar offset bits px py]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ToBytes.circuit _ (accVar offset Specs.Bls12381G1.scalarBits).x
      (offset + 12520245) ?_ ToBytes.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    exact eval_accVar_x_of_agreesBelow offset Specs.Bls12381G1.scalarBits
      (ProverEnvironment.agreesBelow_of_le h_agree (by simp only [Specs.Bls12381G1.scalarBits]; omega))
  · -- ToBytes on acc.y
    rw [foldl_output_eq_accVar offset bits px py]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) ToBytes.circuit _ (accVar offset Specs.Bls12381G1.scalarBits).y
      (offset + 12520245 + 432) ?_ ToBytes.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    exact eval_accVar_y_of_agreesBelow offset Specs.Bls12381G1.scalarBits
      (ProverEnvironment.agreesBelow_of_le h_agree (by simp only [Specs.Bls12381G1.scalarBits]; omega))
  · -- Mux on the x bytes
    rw [foldl_output_eq_accVar offset bits px py]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := fields coordBytes)) _
      { selector := (accVar offset Specs.Bls12381G1.scalarBits).isInf, ifTrue := zeroBytes,
        ifFalse := (subcircuit ToBytes.circuit (accVar offset Specs.Bls12381G1.scalarBits).x).output
          (offset + 12520245) }
      (offset + 12520245 + 432 + 432) ?_ (Mux.computableWitnesses (M := fields coordBytes)) env env'
    intro k e e' hle h_agree h_in
    refine Mux.eval_inputs_mk ?_ ?_ ?_
    · exact eval_accVar_isInf_of_agreesBelow offset Specs.Bls12381G1.scalarBits
        (ProverEnvironment.agreesBelow_of_le h_agree (by simp only [Specs.Bls12381G1.scalarBits]; omega))
    · simp only [circuit_norm]
      apply Vector.ext; intro j hj; simp [zeroBytes, Expression.eval]
    · exact toBytes_output_stable (accVar offset Specs.Bls12381G1.scalarBits).x
        (o := offset + 12520245) h_agree (by omega)
  · -- Mux on the y bytes
    rw [foldl_output_eq_accVar offset bits px py]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := fields coordBytes)) _
      { selector := (accVar offset Specs.Bls12381G1.scalarBits).isInf, ifTrue := zeroBytes,
        ifFalse := (subcircuit ToBytes.circuit (accVar offset Specs.Bls12381G1.scalarBits).y).output
          (offset + 12520245 + 432) }
      (offset + 12520245 + 432 + 432 + 48) ?_ (Mux.computableWitnesses (M := fields coordBytes)) env env'
    intro k e e' hle h_agree h_in
    refine Mux.eval_inputs_mk ?_ ?_ ?_
    · exact eval_accVar_isInf_of_agreesBelow offset Specs.Bls12381G1.scalarBits
        (ProverEnvironment.agreesBelow_of_le h_agree (by simp only [Specs.Bls12381G1.scalarBits]; omega))
    · simp only [circuit_norm]
      apply Vector.ext; intro j hj; simp [zeroBytes, Expression.eval]
    · exact toBytes_output_stable (accVar offset Specs.Bls12381G1.scalarBits).y
        (o := offset + 12520245 + 432) h_agree (by omega)

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

end ScalarMul
end Solution.Bls12381G1ScalarMul

