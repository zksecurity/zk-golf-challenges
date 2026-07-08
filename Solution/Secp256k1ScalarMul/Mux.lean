import Solution.Secp256k1ScalarMul.Params

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
    let s := Expression.eval env.toEnvironment selector
    let tv := t.map (Expression.eval env.toEnvironment)
    let fv := f.map (Expression.eval env.toEnvironment)
    fromElements (M := M) (if s = 1 then tv else fv)

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
  · rw [h0, if_neg (zero_ne_one (α := F circomPrime)), Vector.getElem_map]
    ring
  · rw [h1, if_pos rfl, Vector.getElem_map]
    ring

/-- The `Mux` formal circuit: materialized boolean selection. -/
def circuit : FormalCircuit (F circomPrime) (Inputs M) M where
  main; elaborated; Assumptions; Spec := Spec (M := M); soundness; completeness

end
end Mux
end Solution.Secp256k1ScalarMul
