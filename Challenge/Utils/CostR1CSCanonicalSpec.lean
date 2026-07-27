import Challenge.Utils.CostR1CS

/-!
# Ordered identity-C obligation: the trusted statement

**This file is the complete trusted surface of the `gf2-sha256-compress-canonical`
R1CS-shape obligation.** It contains exactly four definitions and no theorems.
Everything else (`CostR1CSCanonical.lean`, the solution's certificates) is
kernel-checked machinery: a wrong proof there cannot get past Lean's kernel,
but a wrong *definition here* would change what is being claimed, so this file
is what a reviewer must read.

The obligation: the `t`-th constraint row of the circuit, in emission
(`toFlat`) order, must have its `C`-side be *exactly* the variable `n₀ + t`
(where `n₀ = size Input` is where witness allocation starts). This prescribes
the ordered sequence of `C`-side variables directly, rather than accepting an
arbitrary selection or permutation.

Only pre-existing definitions are referenced: `Affine`, `FlatOperation`,
`Operations.toFlat`, and `Circuit.operations`. These form the same trusted base
as the general R1CS certification and the cost model.
-/

namespace Challenge.CostR1CS

variable {F : Type} [Field F] {α : Type}

/-- One canonical constraint row *at pin index `k`*: `e = var k − A·B` with
`A, B` affine. The `C`-side is exactly the variable `k`; `k` is an argument,
not existentially quantified: the row's output slot is prescribed.

There is deliberately **no separate linear case**: a copy or sum row must be
written as an explicit product `var k − A·1` (`B` the constant one, which is
affine). Every row of this challenge is therefore literally one rank-1 product
pinned to its prescribed variable; the linear form is not a special case of the
*obligation*, only a particular choice of `B`. -/
def isCidentityRowAt (k : ℕ) (e : Expression F) : Prop :=
  ∃ (A B : Expression F), Affine A ∧ Affine B ∧
    e = (Expression.var ⟨k⟩ : Expression F) - A * B

/-- The pin counter over a flat operation list: the counter names the
`C`-variable of the *next* assert. Witnesses leave it unchanged, every assert
must pin the current counter and advances it by one, and `lookup`/`interact`
operations are rejected outright. -/
def flatOperationsIsCid : ℕ → List (FlatOperation F) → Prop
  | _, [] => True
  | k, .witness _ _ :: ops => flatOperationsIsCid k ops
  | k, .assert e :: ops => isCidentityRowAt k e ∧ flatOperationsIsCid (k + 1) ops
  | _, .lookup _ :: _ => False
  | _, .interact _ :: _ => False

/-- Ordered identity-C certificate for a circuit.

A Clean circuit is a program run at a *starting offset* `n`: the first witness
it allocates receives variable index `n`, the next `n+1`, and so on;
`c.operations n` is the operation list it emits when run there, and
`Operations.toFlat` flattens nested subcircuit blocks into the primitive
`witness`/`assert` sequence **in emission order**, the same order the cost
model counts constraints and the order any R1CS backend enumerates rows.

The certificate starts the pin counter at that same `n`: the `t`-th assert of
the flat list must pin exactly variable `n + t`. Witness operations leave this
counter unchanged. Quantifying over *all* offsets is what makes the property
compositional; a subcircuit runs at whatever shifted offset its context
dictates, and its certificate applies there unchanged. The challenge consumes
the single instantiation `n = size Input` (inputs occupy variables
`0 .. size Input − 1`). -/
def IsCidCirc (c : Circuit F α) : Prop :=
  ∀ n, flatOperationsIsCid n (Operations.toFlat (c.operations n))

/-- Top-level obligation: for every affine symbolic input, each constraint's
`C`-side follows the prescribed variable sequence and the circuit produces
affine outputs. -/
def isR1CS_Cidentity {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (main : Var Input F → Circuit F (Var Output F)) : Prop :=
  ∀ input : Var Input F, AffineProvable input → IsCidCirc (main input) ∧ AffineOutput (main input)

/- These definitions pattern-match on the operation list. Whnf-normalizing an
application at a *concrete* circuit therefore forces the scrutinee to a head
constructor; i.e., it actually runs the circuit do-block and materializes all
~48k operations as one term (minutes of elaboration, and unbounded in
general). Marking the predicates `irreducible` makes the elaborator treat such
applications as stuck atoms, so unification falls back to structural
comparison, which is the right and instant behaviour here.

This is an elaboration hint, not semantics: the kernel ignores reducibility
attributes and unfolds freely when checking the final proof terms, so the
attribute cannot change what these definitions mean or what is provable; it
can only make proofs harder to *construct*, never easier to fake. The
machinery file re-enables reducibility locally: its base lemmas unfold the
definitions only on abstract `cons`/`nil` lists, where matching is trivial. -/
attribute [irreducible] isCidentityRowAt flatOperationsIsCid

end Challenge.CostR1CS
