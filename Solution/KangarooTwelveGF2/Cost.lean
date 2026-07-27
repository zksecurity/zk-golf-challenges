import Solution.KangarooTwelveGF2.Round
import Challenge.Utils.CostR1CSCanonical

namespace Solution.KangarooTwelveGF2

open Challenge.Instances.KangarooTwelveGF2.Interface
open Challenge.F2Bits
open Challenge.CostR1CS
open Round

namespace Cost

theorem costIs_main (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar) :
    CostIs (Round.main r s) ⟨1600, 1600⟩ := by
  unfold Round.main
  have hcount : (⟨1600, 0⟩ + (⟨1600 * 0, 1600 * 1⟩ + ⟨0, 0⟩) : Count)
      = ⟨1600, 1600⟩ := by
    show (⟨_, _⟩ : Count) = _
    congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector permutationBits _) fun products => ?_
  refine CostIs.bind (CostIs.forEach fun i n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar) :
    CostIs (subcircuit (Round.circuit r) s) ⟨1600, 1600⟩ :=
  CostIs.subcircuit (fun n => costIs_main r s n)

theorem bit_affine {s : StateVar} (hs : AffineW s) (x y z : ℕ) :
    Affine (Specs.KangarooTwelve.bit s x y z) :=
  hs _ (Specs.KangarooTwelve.bitIndex x y z).isLt

theorem columnParity_affine {s : StateVar} (hs : AffineW s) (x z : ℕ) :
    Affine (Specs.KangarooTwelve.columnParity s x z) := by
  unfold Specs.KangarooTwelve.columnParity
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
    AffineW (Specs.KangarooTwelve.theta s) := by
  intro i hi
  change Affine ((Specs.KangarooTwelve.theta s)[i]'hi)
  unfold Specs.KangarooTwelve.theta
  rw [Vector.getElem_ofFn]
  apply Affine.add
  · apply Affine.add
    · exact bit_affine hs (Specs.KangarooTwelve.xOf ⟨i, hi⟩)
        (Specs.KangarooTwelve.yOf ⟨i, hi⟩) (Specs.KangarooTwelve.zOf ⟨i, hi⟩)
    · exact columnParity_affine hs (Specs.KangarooTwelve.xOf ⟨i, hi⟩ + 4)
        (Specs.KangarooTwelve.zOf ⟨i, hi⟩)
  · exact columnParity_affine hs (Specs.KangarooTwelve.xOf ⟨i, hi⟩ + 1)
      (Specs.KangarooTwelve.zOf ⟨i, hi⟩ + 63)

theorem rhoPi_affine {s : StateVar} (hs : AffineW s) :
    AffineW (Specs.KangarooTwelve.rhoPi s) := by
  intro i hi
  change Affine ((Specs.KangarooTwelve.rhoPi s)[i]'hi)
  unfold Specs.KangarooTwelve.rhoPi
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

theorem roundOut_affine (r : Fin Specs.KangarooTwelve.rounds)
    {pre products : StateVar} (hpre : AffineW pre) (hproducts : AffineW products) :
    AffineW (roundOut r pre products) := by
  intro i hi
  change Affine ((roundOut r pre products)[i]'hi)
  unfold roundOut Specs.KangarooTwelve.iota
  rw [Vector.getElem_ofFn]
  dsimp only
  split
  · apply Affine.add
    · exact bit_affine (chiFromProducts_affine hpre hproducts) _ _ _
    · unfold Specs.KangarooTwelve.roundConstantBit
      split <;> exact Affine.const _
  · exact bit_affine (chiFromProducts_affine hpre hproducts) _ _ _

theorem wv_getElem {n : ℕ} (c : ProverEnvironment (F p2) → Vector (F p2) n)
    (w i : ℕ) (h : i < n) :
    ((Circuit.witnessVector n c).output w)[i]'h = Expression.var ⟨w + i⟩ := by
  rw [show (Circuit.witnessVector n c).output w = varFromOffset (fields n) w from rfl]
  simp only [varFromOffset, instProvableTypeFields, size, Vector.getElem_mapRange]

section

attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

set_option maxRecDepth 8000 in
theorem isCidentity_ops (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar)
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
    (Affine.add (Affine.const _) (preChi_affine hs _ (Specs.KangarooTwelve.bitIndex _ _ _).isLt))
    (preChi_affine hs _ (Specs.KangarooTwelve.bitIndex _ _ _).isLt)

end

theorem isCidentity_main (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar)
    (hs : AffineW s) : IsCidCirc (Round.main r s) :=
  IsCidCirc.of_ops (isCidentity_ops r s hs)

theorem isCidentity_sub (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar)
    (hs : AffineW s) : IsCidCirc (subcircuit (Round.circuit r) s) :=
  IsCidCirc.subcircuit (isCidentity_ops r s hs)

/-- Each round is balanced: 1600 constraints = 1600 allocations. -/
theorem balanced_sub (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar) :
    Balanced (subcircuit (Round.circuit r) s) :=
  Balanced.of_costIs (costIs_sub r s) fun n => by
    simp [circuit_norm, subcircuit, Round.circuit, Round.elaborated]
    rfl

theorem affineW_subOut (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar)
    (hs : AffineW s) (n : ℕ) : AffineW ((subcircuit (Round.circuit r) s).output n) := by
  simp only [circuit_norm, subcircuit, Round.circuit, Round.elaborated]
  exact roundOut_affine r (preChi_affine hs) (affineW_mapRange_var _)

theorem affineW_input_state {input : Var Input (F p2)} (hinput : AffineProvable input) :
    AffineW input.state := by
  intro i hi
  have hsz : size Input = permutationBits := rfl
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz, hi] using
    hinput i (by omega)

end Cost

end Solution.KangarooTwelveGF2
