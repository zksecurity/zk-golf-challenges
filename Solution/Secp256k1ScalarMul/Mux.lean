import Solution.Secp256k1ScalarMul.Params
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Materializing mux/select — `Mux`

`FormalCircuit` selecting between two values of any provable type by a
boolean selector, like Clean's `Gadgets.Conditional`, but with the result
**materialized into fresh witness cells**: one rank-1 row
`out_i = sel·(t_i − f_i) + f_i` per element.

Clean's `Conditional` returns the selection as *expressions*, which have
degree `deg(sel) + max(deg t, deg f)`; chaining muxes and feeding the results
into multiplicative gadgets would produce non-rank-1 rows. `Mux`'s outputs
are plain variables (affine, degree 1), so they can be consumed anywhere —
in particular, every gadget output in this solution stays affine.

Soundness and completeness are fully proved.
-/

namespace Solution.Secp256k1ScalarMul
namespace Mux

section
variable {M : TypeMap} [ProvableType M]

/-- Inputs of `Mux`: a boolean selector and the two candidate values. -/
structure Inputs (M : TypeMap) (F : Type) where
  selector : F
  ifTrue : M F
  ifFalse : M F
deriving ProvableStruct

def main (input : Var (Inputs M) (F circomPrime)) :
    Circuit (F circomPrime) (Var M (F circomPrime)) := do
  let { selector, ifTrue, ifFalse } := input
  let t := toElements ifTrue
  let f := toElements ifFalse

  -- witness the selected value
  let out ← ProvableType.witness (α := M) fun env =>
    let inputValue : Inputs M (F circomPrime) := eval env input
    if inputValue.selector = 1 then inputValue.ifTrue else inputValue.ifFalse

  -- one rank-1 row per element: out_i = sel·(t_i − f_i) + f_i
  let outE := toElements (M := M) out
  let constraints := Vector.ofFn fun i : Fin (size M) =>
    selector * (t[i] - f[i]) + f[i] - outE[i]
  Circuit.forEach constraints assertZero

  return out

instance elaborated : ElaboratedCircuit (F circomPrime) (Inputs M) M main := by
  elaborate_circuit

/-- Precondition: the selector is boolean. -/
def Assumptions (input : Inputs M (F circomPrime)) : Prop :=
  IsBool input.selector

/-- Postcondition: the output is the selected value. -/
def Spec (input : Inputs M (F circomPrime)) (out : M (F circomPrime)) : Prop :=
  out = if input.selector = 1 then input.ifTrue else input.ifFalse

theorem soundness : Soundness (F circomPrime) main Assumptions (Spec (M := M)) := by
  circuit_proof_start
  rcases input with ⟨selector, ifTrue, ifFalse⟩
  simp only [Inputs.mk.injEq] at h_input
  obtain ⟨h_selector, h_ifTrue, h_ifFalse⟩ := h_input
  simp only at h_assumptions
  rw [ProvableType.ext_iff]
  intro i hi
  have h := h_holds ⟨i, hi⟩
  simp only [Vector.getElem_ofFn, Expression.eval,
    ProvableType.getElem_eval_toElements, h_selector, h_ifTrue, h_ifFalse] at h
  rcases h_assumptions with h0 | h1
  · rw [h0] at h
    rw [h0, if_neg (zero_ne_one (α := F circomPrime))]
    rw [zero_mul, zero_add, neg_one_mul, add_neg_eq_zero] at h
    exact h.symm
  · rw [h1] at h
    rw [h1, if_pos rfl]
    rw [one_mul, neg_one_mul, neg_one_mul, add_neg_eq_zero, neg_add_cancel_right] at h
    exact h.symm

theorem completeness :
    Completeness (Input := Inputs M) (Output := M) (F circomPrime) main Assumptions := by
  circuit_proof_start
  rcases input with ⟨selector, ifTrue, ifFalse⟩
  simp only [Inputs.mk.injEq] at h_input
  obtain ⟨h_selector, h_ifTrue, h_ifFalse⟩ := h_input
  simp only at h_assumptions
  intro i
  have henv := h_env i
  simp only [Vector.getElem_ofFn, Expression.eval, varFromOffset,
    ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  rw [henv, h_selector]
  rcases h_assumptions with h0 | h1
  · rw [h0, if_neg (zero_ne_one (α := F circomPrime))]
    rw [← ProvableType.getElem_eval_toElements input_var.ifFalse i i.isLt]
    ring
  · rw [h1, if_pos rfl]
    rw [← ProvableType.getElem_eval_toElements input_var.ifTrue i i.isLt]
    ring

/-- The `Mux` formal circuit: materialized boolean selection. -/
def circuit : FormalCircuit (F circomPrime) (Inputs M) M where
  main; elaborated; Assumptions; Spec := Spec (M := M); soundness; completeness

theorem computableWitnesses : (circuit (M := M)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  rcases input with ⟨selector, ifTrue, ifFalse⟩
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    rw [h_input]
  · intro _
    trivial

theorem computableWitness : ∀ n (input : Var (Inputs M) (F circomPrime)),
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := (circuit (M := M)).base) computableWitnesses

/-- The output of `Mux.main` is the selected-value witness, allocated first at
`offset` and reading only the `size M` cells `[offset, offset + size M)`.
Environments agreeing below any `k ≥ offset + size M` evaluate the output
identically. Consumed by `CompleteAdd`/`Step`, which chain mux outputs into
later subcircuits. -/
lemma eval_output_of_agreesBelow (input : Var (Inputs M) (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + size M ≤ k) :
    eval env ((main (M := M) input).output offset)
      = eval env' ((main (M := M) input).output offset) := by
  have hout : (main (M := M) input).output offset = varFromOffset M offset := rfl
  rw [hout, CircuitType.eval_expression_prover_to_verifier,
    CircuitType.eval_expression_prover_to_verifier, ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements (varFromOffset M offset) i hi,
    ← ProvableType.getElem_eval_toElements (varFromOffset M offset) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  exact h_agree (offset + i) (by omega)

end
end Mux
end Solution.Secp256k1ScalarMul
