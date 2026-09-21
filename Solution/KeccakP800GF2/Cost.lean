import Solution.KeccakP800GF2.Round
import Challenge.Utils.CostR1CSCanonical
import Challenge.Utils.WitgenIR

namespace Solution.KeccakP800GF2

open Challenge.Instances.KeccakP800GF2.Interface
open Challenge.F2Bits
open Challenge.CostR1CS
open Round

namespace Cost

theorem costIs_main (r : Specs.KeccakP800.RoundIndex) (s : StateVar) :
    CostIs (Round.main r s) ⟨800, 800⟩ := by
  unfold Round.main
  have hcount : (⟨800, 0⟩ + (⟨800 * 0, 800 * 1⟩ + ⟨0, 0⟩) : Count)
      = ⟨800, 800⟩ := by
    show (⟨_, _⟩ : Count) = _
    congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector permutationBits _) fun products => ?_
  refine CostIs.bind (CostIs.forEach fun i n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (r : Specs.KeccakP800.RoundIndex) (s : StateVar) :
    CostIs (subcircuit (Round.circuit r) s) ⟨800, 800⟩ :=
  CostIs.subcircuit (fun n => costIs_main r s n)

theorem bit_affine {s : StateVar} (hs : AffineW s) (x y z : ℕ) :
    Affine (Specs.KeccakP800.bit s x y z) :=
  hs _ (Specs.KeccakP800.bitIndex x y z).isLt

theorem columnParity_affine {s : StateVar} (hs : AffineW s) (x z : ℕ) :
    Affine (Specs.KeccakP800.columnParity s x z) := by
  unfold Specs.KeccakP800.columnParity
  apply Affine.add
  · apply Affine.add
    · apply Affine.add
      · apply Affine.add
        · exact bit_affine hs x 0 z
        · exact bit_affine hs x 1 z
      · exact bit_affine hs x 2 z
    · exact bit_affine hs x 3 z
  · exact bit_affine hs x 4 z

theorem theta_affine {s : StateVar} (hs : AffineW s) :
    AffineW (Specs.KeccakP800.theta s) := by
  intro i hi
  change Affine ((Specs.KeccakP800.theta s)[i]'hi)
  unfold Specs.KeccakP800.theta
  rw [Vector.getElem_ofFn]
  apply Affine.add
  · apply Affine.add
    · exact bit_affine hs (Specs.KeccakP800.xOf ⟨i, hi⟩)
        (Specs.KeccakP800.yOf ⟨i, hi⟩) (Specs.KeccakP800.zOf ⟨i, hi⟩)
    · exact columnParity_affine hs (Specs.KeccakP800.xOf ⟨i, hi⟩ + 4)
        (Specs.KeccakP800.zOf ⟨i, hi⟩)
  · exact columnParity_affine hs (Specs.KeccakP800.xOf ⟨i, hi⟩ + 1)
      (Specs.KeccakP800.zOf ⟨i, hi⟩ + 31)

theorem rhoPi_affine {s : StateVar} (hs : AffineW s) :
    AffineW (Specs.KeccakP800.rhoPi s) := by
  intro i hi
  change Affine ((Specs.KeccakP800.rhoPi s)[i]'hi)
  unfold Specs.KeccakP800.rhoPi
  rw [Vector.getElem_ofFn]
  exact bit_affine hs _ _ _

theorem preChi_affine {s : StateVar} (hs : AffineW s) : AffineW (preChi s) := by
  unfold preChi
  exact rhoPi_affine (theta_affine hs)

theorem chiFromProducts_affine {pre products : StateVar}
    (hpre : AffineW pre) (hproducts : AffineW products) :
    AffineW (chiFromProducts pre products) := by
  intro i hi
  change Affine ((chiFromProducts pre products)[i]'hi)
  unfold chiFromProducts
  rw [Vector.getElem_ofFn]
  apply Affine.add
  · exact bit_affine hpre _ _ _
  · exact hproducts _ hi

theorem roundOut_affine (r : Specs.KeccakP800.RoundIndex)
    {pre products : StateVar} (hpre : AffineW pre) (hproducts : AffineW products) :
    AffineW (roundOut r pre products) := by
  intro i hi
  change Affine ((roundOut r pre products)[i]'hi)
  unfold roundOut Specs.KeccakP800.iota
  rw [Vector.getElem_ofFn]
  dsimp only
  split
  · apply Affine.add
    · exact bit_affine (chiFromProducts_affine hpre hproducts) _ _ _
    · unfold Specs.KeccakP800.roundConstantBit
      split <;> exact Affine.const _
  · exact bit_affine (chiFromProducts_affine hpre hproducts) _ _ _

theorem wv_getElem {n : ℕ} (out : Witgen.VExpr (F p2) n)
    (w i : ℕ) (h : i < n) :
    ((Circuit.witnessVector n out).output w)[i]'h = Expression.var ⟨w + i⟩ := by
  rw [show (Circuit.witnessVector n out).output w = varFromOffset (fields n) w from rfl]
  simp only [varFromOffset, size, explicit_provable_type, Vector.getElem_mapRange]

section

attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

set_option maxRecDepth 8000 in
theorem isCidentity_ops (r : Specs.KeccakP800.RoundIndex) (s : StateVar)
    (hs : AffineW s) : ∀ n, operationsIsCid n ((Round.main r s).operations n) := by
  intro n
  unfold Round.main
  rw [Circuit.bind_operations_eq, operationsIsCid_append,
    CostIs.witnessVector permutationBits _ n]
  refine ⟨operationsIsCid_witnessVector permutationBits _ _ _, ?_⟩
  rw [Circuit.bind_operations_eq, operationsIsCid_append,
    (CostIs.forEach fun i m => CostIs.assertZero _ m) _]
  refine ⟨?_, operationsIsCid_pure _ _ _⟩
  rw [Circuit.forEach.operations_eq]
  refine operationsIsCid_flatten_ofFn (L := 1)
    (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
  simp only [Vector.getElem_finRange]
  simp only [Nat.mul_one]
  refine ⟨?_, trivial⟩
  rw [wv_getElem]
  unfold chiProduct
  exact isCidentityRowAt_var_sub_mul
    (Affine.add (Affine.const _) (preChi_affine hs _ (Specs.KeccakP800.bitIndex _ _ _).isLt))
    (preChi_affine hs _ (Specs.KeccakP800.bitIndex _ _ _).isLt)

end

theorem isCidentity_main (r : Specs.KeccakP800.RoundIndex) (s : StateVar)
    (hs : AffineW s) : IsCidCirc (Round.main r s) :=
  IsCidCirc.of_ops (isCidentity_ops r s hs)

theorem isCidentity_sub (r : Specs.KeccakP800.RoundIndex) (s : StateVar)
    (hs : AffineW s) : IsCidCirc (subcircuit (Round.circuit r) s) :=
  IsCidCirc.subcircuit (isCidentity_ops r s hs)

/-- Each round is balanced: 800 constraints = 800 allocations. -/
theorem balanced_sub (r : Specs.KeccakP800.RoundIndex) (s : StateVar) :
    Balanced (subcircuit (Round.circuit r) s) :=
  Balanced.of_costIs (costIs_sub r s) fun n => by
    simp [circuit_norm, subcircuit, Round.circuit, Round.elaborated]
    rfl

theorem affineW_subOut (r : Specs.KeccakP800.RoundIndex) (s : StateVar)
    (hs : AffineW s) (n : ℕ) : AffineW ((subcircuit (Round.circuit r) s).output n) := by
  simp only [circuit_norm, subcircuit, Round.circuit, Round.elaborated]
  exact roundOut_affine r (preChi_affine hs) (affineW_mapRange_var _)

/-! ## Witness-IR certificates

Same skeleton as `costIs_main` / `isCidentity_ops` above, but every non-witness
operation is discharged by its own combinator and the single witness site by the IR
entry point it was built with (`Circuit.witnessVector` over the inlined literal vector
of `chiProduct` expressions in `Round.main`). -/

section WitgenIR

open Challenge.WitgenIR

-- Keep the IR predicates opaque while *applying* the certificates: otherwise the
-- unifier whnf's `operationsUseIR` on the round's 800 flattened rows and times out.
attribute [local irreducible] operationsUseIR flatOperationsUseIR IsIR

theorem usesIR_main (r : Specs.KeccakP800.RoundIndex) (s : StateVar) :
    UsesIRCirc (Round.main r s) := by
  unfold Round.main
  exact UsesIRCirc.bind (UsesIRCirc.witnessVector permutationBits _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.forEach fun _ n => UsesIRCirc.assertZero _ n) fun _ =>
      UsesIRCirc.pure _

theorem usesIR_sub (r : Specs.KeccakP800.RoundIndex) (s : StateVar) :
    UsesIRCirc (subcircuit (Round.circuit r) s) :=
  UsesIRCirc.subcircuit (fun n => usesIR_main r s n)

end WitgenIR

theorem affineW_input_state {input : Var Input (F p2)} (hinput : AffineProvable input) :
    AffineW input.state := by
  obtain ⟨s⟩ := input
  intro i hi
  have hsz : size Input = permutationBits := rfl
  have h := hinput i (by omega)
  simp only [circuit_norm, explicit_provable_type] at h
  exact h

/-- An `Output` whose `state` field is entrywise affine is affine as a provable
value. -/
theorem affineProvable_output {out : Var Output (F p2)} (h : AffineW out.state) :
    AffineProvable out := by
  obtain ⟨st⟩ := out
  intro i hi
  have hsz : size Output = permutationBits := rfl
  simp only [circuit_norm, explicit_provable_type]
  exact h i (by omega)

end Cost

end Solution.KeccakP800GF2
