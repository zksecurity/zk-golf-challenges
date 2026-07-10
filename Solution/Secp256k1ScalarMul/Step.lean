import Solution.Secp256k1ScalarMul.CompleteAdd
import Challenge.Utils.ComputableWitnessLemmas

/-!
# One double-and-add step — `Step`

`FormalCircuit` for a single left-to-right double-and-add step, the loop body
of `ScalarMul`: double the accumulator (a self-add), add the base point, and
select by the scalar bit. Its specification is exactly the trusted spec's
`Specs.ShortWeierstrass.step` on decoded values.

Extracting the body as its own gadget keeps the `Circuit.foldl` loop body a
single `subcircuit` call, so the fold's `ConstantLength`/`ConstantOutput`
synthesis stays trivial (inlining the three subcircuits blows the heartbeat
budget).

-/

namespace Solution.Secp256k1ScalarMul
namespace Step

/-- Inputs of `Step`: the accumulator, the base-point coordinates, and the
current scalar bit. -/
structure Inputs (F : Type) where
  acc : FlaggedPoint F
  px : Emu F
  py : Emu F
  bit : F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let { acc, px, py, bit } := input
  let base : Var FlaggedPoint (F circomPrime) :=
    { x := px, y := py,
      isInf := ((0 : F circomPrime) : Expression (F circomPrime)) }
  let doubled ← subcircuit CompleteAdd.circuit { P := acc, Q := acc }
  let added ← subcircuit CompleteAdd.circuit { P := doubled, Q := base }
  subcircuit (Mux.circuit (M := FlaggedPoint))
    { selector := bit, ifTrue := added, ifFalse := doubled }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

/-- Preconditions: the accumulator is a well-formed flagged point, the bit is
boolean, and the base point has canonical coordinates and lies on the curve. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.acc.Valid ∧ IsBool input.bit ∧
  Fe.Valid input.px ∧ Fe.Valid input.py ∧
  Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
    { x := decodeFe input.px, y := decodeFe input.py }

/-- Postcondition: the output is well-formed and decodes to the trusted
spec's `step` on the decoded inputs. -/
def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.Valid ∧
    decodePoint out =
      Specs.ShortWeierstrass.step Specs.Secp256k1.curve
        { x := decodeFe input.px, y := decodeFe input.py }
        (decodePoint input.acc) (input.bit.val)

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hacc, hbit, hpx, hpy, honcurve⟩ := h_assumptions
  obtain ⟨hdbl, hadd, hmux⟩ := h_holds
  obtain ⟨hdblv, hdble⟩ := hdbl hacc
  have hbase : FlaggedPoint.Valid
      { x := input_px, y := input_py, isInf := (0 : F circomPrime) } :=
    ⟨Or.inl rfl, hpx, hpy, fun _ => honcurve⟩
  obtain ⟨haddv, hadde⟩ := hadd ⟨hdblv, hbase⟩
  have hmux' := hmux hbit
  rw [hmux']
  have hbased : decodePoint
      { x := input_px, y := input_py, isInf := (0 : F circomPrime) } =
      .affine { x := decodeFe input_px, y := decodeFe input_py } := by
    simp only [decodePoint, if_neg (zero_ne_one (α := F circomPrime))]
  rcases hbit with h0 | h1
  · rw [h0, if_neg (zero_ne_one (α := F circomPrime)), ZMod.val_zero]
    simp only [Specs.ShortWeierstrass.step, if_neg (zero_ne_one (α := ℕ))]
    exact ⟨hdblv, hdble⟩
  · rw [h1, if_pos rfl, ZMod.val_one]
    simp only [Specs.ShortWeierstrass.step, if_true]
    exact ⟨haddv, by rw [hadde, hdble, hbased]⟩

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hacc, hbit, hpx, hpy, honcurve⟩ := h_assumptions
  obtain ⟨hdbl, -⟩ := h_env
  obtain ⟨hdblv, -⟩ := hdbl hacc
  exact ⟨hacc, ⟨hdblv, ⟨Or.inl rfl, hpx, hpy, fun _ => honcurve⟩⟩, hbit⟩

/-- The `Step` formal circuit: one double-and-add iteration. -/
def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main; elaborated; Assumptions; Spec; soundness; completeness

/-! ## Computable witnesses

`Step` chains two `CompleteAdd` subcircuits (the doubling and the base-point
addition) and one `FlaggedPoint` `Mux` (the bit selection). Every witness
generator is a deterministic function of the parent input and the prior
subcircuit outputs, so the whole circuit is computable. Each subcircuit is
discharged through its own `computableWitnesses` theorem; the two `CompleteAdd`
outputs feeding the second addition and the final mux are propagated with
`CompleteAdd.eval_output_of_agreesBelow` at the concrete block offsets
(`doubled` at `offset`, `added` at `offset + 15975`, the mux output at
`offset + 31950`). -/

/-- Stability of a `CompleteAdd` subcircuit output, stated in the `circuit.output`
(elaborated) form that appears after `circuit_norm` normalizes a `subcircuit`
output in the goal. `CompleteAdd.eval_output_of_agreesBelow` is stated with
`(main input).output`; bridging the two via `exact` would force an expensive
`whnf` of the whole `CompleteAdd.main`, so we cross the gap once here with the
cheap `elaborated.output_eq`. -/
private lemma completeAdd_output_stable (X : Var CompleteAdd.Inputs (F circomPrime))
    {o k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : o + 15975 ≤ k) :
    eval env (CompleteAdd.circuit.output X o) = eval env' (CompleteAdd.circuit.output X o) := by
  have h := CompleteAdd.eval_output_of_agreesBelow X (offset := o) h_agree hk
  rw [CompleteAdd.elaborated.output_eq X o] at h
  exact h

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨acc, px, py, bit⟩ := input
  -- the two `CompleteAdd` blocks have constant local length, so block offsets stay concrete
  have hca : ∀ (X : Var CompleteAdd.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit CompleteAdd.circuit X).localLength o = 15975 := fun _ _ => rfl
  -- the constructed base point and the doubling output at their concrete offsets
  let base : Var FlaggedPoint (F circomPrime) :=
    { x := px, y := py, isInf := ((0 : F circomPrime) : Expression (F circomPrime)) }
  let doubled : Var FlaggedPoint (F circomPrime) :=
    (subcircuit CompleteAdd.circuit { P := acc, Q := acc }).output offset
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    hca]
  refine ⟨?_, ?_, ?_⟩
  -- 1. doubled ← CompleteAdd { acc, acc } : both operands are the raw accumulator
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) CompleteAdd.circuit _ _ _ ?_ CompleteAdd.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨haccx, haccy, hacci⟩, _, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢
    rw [CompleteAdd.Inputs.mk.injEq]
    exact ⟨by rw [FlaggedPoint.mk.injEq]; exact ⟨haccx, haccy, hacci⟩,
      by rw [FlaggedPoint.mk.injEq]; exact ⟨haccx, haccy, hacci⟩⟩
  -- 2. added ← CompleteAdd { doubled, base } : P is the doubling output, Q the base point
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) CompleteAdd.circuit _ _ _ ?_ CompleteAdd.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, _, _⟩, hpx, hpy, _⟩ := h_in
    simp only [circuit_norm] at ⊢
    rw [CompleteAdd.Inputs.mk.injEq]
    refine ⟨?_, ?_⟩
    · -- P = doubled (CompleteAdd output at offset)
      have hd := completeAdd_output_stable { P := acc, Q := acc } (o := offset) h_agree (by omega)
      simp only [circuit_norm] at hd
      exact hd
    · -- Q = base = { px, py, 0 }
      rw [FlaggedPoint.mk.injEq]
      exact ⟨hpx, hpy, rfl⟩
  -- 3. out ← Mux { bit, added, doubled } : selector is the raw bit, both branches are
  --    prior CompleteAdd outputs
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := FlaggedPoint)) _ _ _ ?_
      (Mux.computableWitnesses (M := FlaggedPoint)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, _, _⟩, _, _, hbit⟩ := h_in
    simp only [circuit_norm] at ⊢
    rw [Mux.Inputs.mk.injEq]
    refine ⟨hbit, ?_, ?_⟩
    · -- ifTrue = added (CompleteAdd output at offset + 15975)
      have ha := completeAdd_output_stable { P := doubled, Q := base } (o := offset + 15975)
        h_agree (by omega)
      simp only [circuit_norm] at ha
      exact ha
    · -- ifFalse = doubled (CompleteAdd output at offset)
      have hd := completeAdd_output_stable { P := acc, Q := acc } (o := offset) h_agree (by omega)
      simp only [circuit_norm] at hd
      exact hd

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

/-- A fresh `FlaggedPoint` witness block reads only its own `size FlaggedPoint`
cells, so it is stable across environments agreeing below `off + size FlaggedPoint`. -/
private lemma fpVar_stable {off k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : off + size FlaggedPoint ≤ k) :
    eval env ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))))
      = eval env' ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime)))) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint),
    CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  exact h_agree (off + i) (by omega)

/-- The output of `Step.main` is the final `FlaggedPoint` `Mux` witness block (the
selected point), allocated at `offset + 31950` (after the two `CompleteAdd`
blocks) and reading only its `size FlaggedPoint = 9` cells. Environments agreeing
below any `k ≥ offset + 31959` (the full local length) evaluate the output
identically. Consumed by `ScalarMul`. -/
lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 31959 ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  rw [elaborated.output_eq input offset]
  have hsz : size FlaggedPoint = 9 := rfl
  exact fpVar_stable (off := offset + 31950) h_agree (by rw [hsz]; omega)

end Step
end Solution.Secp256k1ScalarMul
