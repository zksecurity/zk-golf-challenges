import Solution.Bls12381G1ScalarMul.Params
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

namespace Solution.Bls12381G1ScalarMul
namespace Mux

section
variable {M : TypeMap} [ProvableType M]

/-- Inputs of `Mux`: a boolean selector and the two candidate values. -/
structure Inputs (M : TypeMap) (F : Type) where
  selector : F
  ifTrue : M F
  ifFalse : M F
deriving ProvableStruct

/-- Witness-IR program for the selected value: one `.ite` per element of `M`,
conditioned on the (shared) field-equality test `selector = 1`. -/
def selectIR (selector : Expression (F circomPrime)) (t f : M (Expression (F circomPrime))) :
    M (Witgen.FExpr (F circomPrime)) :=
  fromElements <| Vector.ofFn fun i : Fin (size M) =>
    Witgen.FExpr.ite (Witgen.BExpr.feq (.expr selector) (.const 1))
      (.expr (toElements t)[i]) (.expr (toElements f)[i])

/-- Bridge for `selectIR`: the witnessed value is the selected one. -/
theorem eval_selectIR (selector : Expression (F circomPrime))
    (t f : M (Expression (F circomPrime))) (ctx : Witgen.Ctx (F circomPrime)) :
    Witgen.eval ctx (selectIR (M := M) selector t f)
      = if Expression.eval ctx.env.toEnvironment selector = 1
        then eval ctx.env.toEnvironment t else eval ctx.env.toEnvironment f := by
  rw [Witgen.eval, ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.toElements_fromElements, Vector.getElem_map, selectIR,
    ProvableType.toElements_fromElements, Vector.getElem_ofFn]
  by_cases hs : Expression.eval ctx.env.toEnvironment selector = 1 <;>
    simp only [circuit_norm, hs, if_true, if_false,
      ProvableType.getElem_eval_toElements]

/-- `selectIR` packaged as the `witness` payload: the witness program's `eval`,
element by element. -/
theorem eval_ofFExprs_selectIR (selector : Expression (F circomPrime))
    (t f : M (Expression (F circomPrime))) (env : ProverEnvironment (F circomPrime)) :
    (Witgen.WitgenIR.ofFExprs (toElements (selectIR (M := M) selector t f))).eval env
      = toElements (Witgen.eval ({ env := env } : Witgen.Ctx (F circomPrime))
          (selectIR (M := M) selector t f)) := by
  refine Vector.ext fun i hi => ?_
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs _ _ i hi, Witgen.eval,
    ProvableType.toElements_fromElements, Vector.getElem_map]

/-- `selectIR` reads the gadget input only, so agreeing inputs give agreeing
witnesses (the `computableWitnesses` obligation). -/
theorem eval_selectIR_congr (selector : Expression (F circomPrime))
    (t f : M (Expression (F circomPrime))) {env env' : ProverEnvironment (F circomPrime)}
    (hs : Expression.eval env.toEnvironment selector
      = Expression.eval env'.toEnvironment selector)
    (ht : eval env.toEnvironment t = eval env'.toEnvironment t)
    (hf : eval env.toEnvironment f = eval env'.toEnvironment f) :
    (Witgen.WitgenIR.ofFExprs (toElements (selectIR (M := M) selector t f))).eval env
      = (Witgen.WitgenIR.ofFExprs (toElements (selectIR (M := M) selector t f))).eval env' := by
  rw [eval_ofFExprs_selectIR, eval_ofFExprs_selectIR, eval_selectIR, eval_selectIR, hs, ht, hf]

def main (input : Var (Inputs M) (F circomPrime)) :
    Circuit (F circomPrime) (Var M (F circomPrime)) := do
  let selector := input.selector
  let t := toElements input.ifTrue
  let f := toElements input.ifFalse

  -- witness the selected value
  let out ← witness (F := F circomPrime) (value := M) (var := Var M)
    (selectIR selector input.ifTrue input.ifFalse)

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
  -- the input struct arrives destructured, `h_input` as its three components
  obtain ⟨h_selector, h_ifTrue, h_ifFalse⟩ := h_input
  rw [ProvableType.ext_iff]
  intro i hi
  have h := h_holds ⟨i, hi⟩
  simp only [ProvableType.getElem_eval_toElements, h_ifTrue, h_ifFalse] at h
  rcases h_assumptions with h0 | h1
  · rw [h0] at h
    rw [h0, if_neg (zero_ne_one (α := F circomPrime))]
    rw [zero_mul, zero_add] at h
    exact (sub_eq_zero.mp h).symm
  · rw [h1] at h
    rw [h1, if_pos rfl]
    rw [one_mul] at h
    have h' := sub_eq_zero.mp h
    rw [← h']; ring

theorem completeness :
    Completeness (Input := Inputs M) (Output := M) (F circomPrime) main Assumptions := by
  circuit_proof_start
  -- the input struct arrives destructured, `h_input` as its three components
  obtain ⟨h_selector, h_ifTrue, h_ifFalse⟩ := h_input
  intro i
  rw [ProvableType.getElem_eval_toElements (varFromOffset M i₀) i.val i.isLt,
    ProvableType.getElem_eval_toElements input_var_ifTrue i.val i.isLt,
    ProvableType.getElem_eval_toElements input_var_ifFalse i.val i.isLt,
    h_env, eval_selectIR, h_selector, h_ifTrue, h_ifFalse]
  rcases h_assumptions with h0 | h1
  · rw [h0, if_neg (zero_ne_one (α := F circomPrime))]
    ring
  · rw [h1, if_pos rfl]
    ring

/-- The `Mux` formal circuit: materialized boolean selection. -/
def circuit : FormalCircuit (F circomPrime) (Inputs M) M where
  main; elaborated; Assumptions; Spec := Spec (M := M); soundness; completeness

/-- Pack per-field agreement into an `eval`-agreement on a literal `Inputs`
struct (the components list no longer iota-reduces on its own). -/
lemma eval_inputs_mk {s : Var field (F circomPrime)} {t f : Var M (F circomPrime)}
    {e e' : ProverEnvironment (F circomPrime)}
    (hs : Expression.eval e.toEnvironment s = Expression.eval e'.toEnvironment s)
    (ht : eval e t = eval e' t) (hf : eval e f = eval e' f) :
    eval e ({ selector := s, ifTrue := t, ifFalse := f } : Var (Inputs M) (F circomPrime))
      = eval e' ({ selector := s, ifTrue := t, ifFalse := f } : Var (Inputs M) (F circomPrime)) := by
  simp only [circuit_norm] at ht hf ⊢
  simp only [hs, ht, hf]
  exact ⟨trivial, trivial, trivial⟩

/-- Feed a boolean selector into the `Mux` assumptions when the input struct
appears in its `fromComponents` form. `eval` no longer iota-reduces a
`ProvableStruct` literal, so match the components chain structurally instead of
letting the unifier reduce it. -/
lemma assumptions_of_isBool {s : F circomPrime} {t f : M (F circomPrime)} (h : IsBool s) :
    (circuit (M := M)).Assumptions
      (fromComponents (.cons s (.cons t (.cons f .nil)))) := by
  simp only [circuit, Assumptions, Inputs.fromComponents_cons]
  exact h

/-- Read off the `Mux` spec when the input struct appears in its
`fromComponents` form (companion to `assumptions_of_isBool`). -/
lemma spec_apply {s : F circomPrime} {t f out : M (F circomPrime)}
    (h : (circuit (M := M)).Spec
      (fromComponents (.cons s (.cons t (.cons f .nil)))) out) :
    out = if s = 1 then t else f := by
  simp only [circuit, Spec, Inputs.fromComponents_cons] at h
  exact h

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
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    simp only [circuit_norm, Inputs.mk.injEq] at h_input
    exact eval_selectIR_congr _ _ _ h_input.1 h_input.2.1 h_input.2.2
  all_goals first
    | trivial
    | (intro _; trivial)

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
  have hout : (main (M := M) input).output offset = varFromOffset M offset := by
    simp only [main, circuit_norm]
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
end Solution.Bls12381G1ScalarMul
