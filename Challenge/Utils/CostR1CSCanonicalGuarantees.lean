import Challenge.Utils.CostR1CSCanonical

/-!
# Guarantees about the ordered identity-C obligation: statements to review

Reviewer-facing companion to `CostR1CSCanonicalSpec.lean`. Each theorem below
*states* a guarantee; the proofs are single references into the kernel-checked
machinery (plus one short induction and two sanity examples, marked as such).
**If this file compiles, the stated guarantees hold**: a Lean theorem
statement cannot compile with a wrong proof, modulo the standard axiom check
(`#print axioms` on the solution's final theorems returns
`[propext, Classical.choice, Quot.sound]`).

This file is *not* imported by the challenge contract (whose trusted closure
is the Spec alone); it exists so the guarantees can be read without their
proofs.
-/

namespace Challenge.CostR1CS

variable {F : Type} [Field F] {α : Type}

/-! ### 1 · Direct reading: row `t` pins variable `n + t` -/

/-- The assert expressions of a flat operation list, in emission order.
"row `t`" below means `(assertExprs ops)[t]`. -/
def assertExprs : List (FlatOperation F) → List (Expression F)
  | [] => []
  | .assert e :: ops => e :: assertExprs ops
  | _ :: ops => assertExprs ops

section
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid

/-- The one inductive proof in this file (kernel-checked; skip on review):
converts the recursive pin-counter definition into its direct reading. -/
theorem flatOperationsIsCid.pin {k : ℕ} {ops : List (FlatOperation F)}
    (h : flatOperationsIsCid k ops) :
    ∀ t (e : Expression F), (assertExprs ops)[t]? = some e → isCidentityRowAt (k + t) e := by
  induction ops generalizing k with
  | nil => intro t e ht; simp [assertExprs] at ht
  | cons op ops ih =>
    cases op with
    | witness m c => exact fun t e ht => ih h t e ht
    | assert e' =>
      intro t e ht
      cases t with
      | zero =>
        simp only [assertExprs, List.getElem?_cons_zero, Option.some.injEq] at ht
        simpa [← ht] using h.1
      | succ t =>
        simp only [assertExprs, List.getElem?_cons_succ] at ht
        rw [show k + (t + 1) = (k + 1) + t by omega]
        exact ih h.2 t e ht
    | lookup l => exact h.elim
    | interact i => exact h.elim

end

/-- **Guarantee (direct reading).** For a certified circuit run at offset `n`,
the `t`-th constraint row is literally `var (n+t) − A·B` for some affine
`A, B`, with no permutation of the prescribed `C`-side variable sequence. -/
theorem IsCidCirc.row_pins {c : Circuit F α} (h : IsCidCirc c) (n t : ℕ)
    {e : Expression F}
    (ht : (assertExprs (Operations.toFlat (c.operations n)))[t]? = some e) :
    isCidentityRowAt (n + t) e :=
  (h n).pin t e ht

/-! ### 2 · Refinement: canonical ⊆ general -/

/-- **Guarantee (row refinement).** Every canonical row is a single R1CS row
in the sense of the general challenge (`isR1CSRow`, at most one affine×affine
product). -/
theorem guarantee_row_refines {k : ℕ} {e : Expression F}
    (h : isCidentityRowAt k e) : isR1CSRow e :=
  h.isR1CSRow

/-- **Guarantee (obligation refinement).** Any solution of the canonical
obligation also satisfies the general `isR1CS` obligation: the canonical
obligation is a strict strengthening of general R1CS certification. -/
theorem guarantee_obligation_refines {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {main : Var Input F → Circuit F (Var Output F)}
    (h : isR1CS_Cidentity main) : isR1CS main :=
  h.isR1CS

/-! ### 3 · Bookkeeping agreement -/

/-- **Guarantee (two-level agreement).** The ops-level working certificate the
proofs compose with (`operationsIsCid`, which threads the counter through
nested subcircuit blocks) agrees exactly with the trusted flat definition;
the machinery's alternative bookkeeping cannot drift from the Spec. -/
theorem guarantee_iff_ops {c : Circuit F α} :
    IsCidCirc c ↔ ∀ n, operationsIsCid n (c.operations n) :=
  isCidCirc_iff_ops

/-! ### 4 · Sanity: the predicate accepts and rejects -/

section
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid

/-- **Sanity (accepts).** A correctly pinned product row at the right index. -/
example : flatOperationsIsCid 7
    [.assert ((Expression.var ⟨7⟩ : Expression F) - Expression.var ⟨3⟩ * Expression.var ⟨5⟩)] :=
  ⟨isCidentityRowAt_var_sub_mul (Affine.var _) (Affine.var _), trivial⟩

/-- **Sanity (rejects, not vacuous).** A row pinning the *wrong* variable
(`var 1` where the counter demands `var 0`) is refused. -/
example : ¬ flatOperationsIsCid 0
    [.assert ((Expression.var ⟨1⟩ : Expression F) - Expression.var ⟨0⟩ * 1)] := by
  rintro ⟨⟨A, B, -, -, hEq⟩, -⟩
  -- both sides are `add (var _) (mul (const (-1)) _)`; the pinned vars disagree
  injection hEq with h1 h2
  injection h1 with hv
  injection hv with hi
  exact Nat.one_ne_zero hi

end

end Challenge.CostR1CS
