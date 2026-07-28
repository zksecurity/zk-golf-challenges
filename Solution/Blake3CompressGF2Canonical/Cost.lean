import Solution.Blake3CompressGF2Canonical.Circuit
import Challenge.Utils.CostR1CSCanonical

/-!
# Cost and ordered identity-C certificates

All composite gadgets are balanced: every allocation is pinned by exactly one
constraint in allocation order. The base proofs below cover the canonical
ripple-carry adder and the two vector-pin sizes; every other certificate is
obtained by balanced composition.
-/

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.Instances.Blake3CompressGF2Canonical.Interface.Blake3Bits
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Solution.Blake3CompressGF2Canonical

namespace Add32Canon

open Add32 (at32 at31 carryE Inputs)

theorem at31_wv (c : ProverEnvironment (F p2) → Vector (F p2) 31) (w i : ℕ) :
    at31 ((Circuit.witnessVector 31 c).output w) i = Expression.var ⟨w + i % 31⟩ := by
  show ((Circuit.witnessVector 31 c).output w)[i % 31]'(Nat.mod_lt _ (by norm_num)) = _
  rw [show (Circuit.witnessVector 31 c).output w = varFromOffset (fields 31) w from rfl]
  simp only [varFromOffset, instProvableTypeFields, size, Vector.getElem_mapRange]

theorem carryE_affine {carries : Var (fields 31) (F p2)} (hc : AffineW carries) (i : ℕ) :
    Affine (carryE carries i) := by
  unfold carryE
  split
  · exact Affine.zero
  · exact hc _ (Nat.mod_lt _ (by norm_num))

theorem at31_affine {v : Var (fields 31) (F p2)} (hv : AffineW v) (i : ℕ) :
    Affine (at31 v i) :=
  hv _ (Nat.mod_lt _ (by norm_num))

theorem costIs_main (b : Var Inputs (F p2)) : CostIs (main b) ⟨62, 62⟩ := by
  unfold main
  have hcount :
      (⟨31, 0⟩ + (⟨31, 0⟩ + (⟨31 * 0, 31 * 1⟩ + (⟨31 * 0, 31 * 1⟩ + ⟨0, 0⟩))) : Count)
        = ⟨62, 62⟩ := by
    show (⟨_, _⟩ : Count) = _
    congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 31 _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector 31 _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun _ m => CostIs.assertZero _ m) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun _ m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var Inputs (F p2)) :
    CostIs (subcircuit circuit b) ⟨62, 62⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

section

attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

theorem isCidentity_ops (b : Var Inputs (F p2)) (hx : AffineW b.x) (hy : AffineW b.y) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 31 _ n]
  refine ⟨operationsIsCid_witnessVector 31 _ _ _, ?_⟩
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 31 _ _]
  refine ⟨operationsIsCid_witnessVector 31 _ _ _, ?_⟩
  rw [Circuit.bind_operations_eq, operationsIsCid_append,
    (CostIs.forEach fun _ m => CostIs.assertZero _ m) _]
  refine ⟨?_, ?_⟩
  · rw [Circuit.forEach.operations_eq]
    refine operationsIsCid_flatten_ofFn (L := 1)
      (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
    simp only [Vector.getElem_finRange, Nat.mul_one]
    refine ⟨?_, trivial⟩
    rw [at31_wv, Nat.mod_eq_of_lt i.isLt]
    exact isCidentityRowAt_var_sub_mul
      (Affine.add (hx _ (Nat.mod_lt _ (by norm_num)))
        (carryE_affine (affineW_witnessVector_output 31 _ _) i.val))
      (Affine.add (hy _ (Nat.mod_lt _ (by norm_num)))
        (carryE_affine (affineW_witnessVector_output 31 _ _) i.val))
  · rw [Circuit.bind_operations_eq, operationsIsCid_append,
      (CostIs.forEach fun _ m => CostIs.assertZero _ m) _]
    refine ⟨?_, operationsIsCid_pure _ _ _⟩
    rw [Circuit.forEach.operations_eq]
    refine operationsIsCid_flatten_ofFn (L := 1)
      (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
    simp only [Vector.getElem_finRange, Nat.mul_one]
    refine ⟨?_, trivial⟩
    rw [at31_wv, Nat.mod_eq_of_lt i.isLt]
    exact isCidentityRowAt_var_sub_mul
      (Affine.add (carryE_affine (affineW_witnessVector_output 31 _ _) i.val)
        (at31_affine (affineW_witnessVector_output 31 _ _) i.val))
      Affine.one

end

theorem isCidentity_sub (b : Var Inputs (F p2)) (hx : AffineW b.x) (hy : AffineW b.y) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_ops b hx hy)

theorem balanced_sub (b : Var Inputs (F p2)) :
    Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Add32Canon

theorem wv_getElem {n : ℕ} (c : ProverEnvironment (F p2) → Vector (F p2) n)
    (w i : ℕ) (hi : i < n) :
    ((Circuit.witnessVector n c).output w)[i]'hi = Expression.var ⟨w + i⟩ := by
  rw [show (Circuit.witnessVector n c).output w = varFromOffset (fields n) w from rfl]
  simp only [varFromOffset, instProvableTypeFields, size, Vector.getElem_mapRange]

namespace Pin32Canon

theorem b32_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) (i : ℕ) :
    Affine (b32 v i) :=
  hv _ (Nat.mod_lt _ (by norm_num))

theorem costIs_main (b : Var (fields 32) (F p2)) : CostIs (main b) ⟨32, 32⟩ := by
  unfold main
  have hcount : (⟨32, 0⟩ + (⟨32 * 0, 32 * 1⟩ + ⟨0, 0⟩) : Count) = ⟨32, 32⟩ := by
    show (⟨_, _⟩ : Count) = _
    congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 32 _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun _ m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var (fields 32) (F p2)) :
    CostIs (subcircuit circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

section

attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

theorem isCidentity_ops (b : Var (fields 32) (F p2)) (hb : AffineW b) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 32 _ n]
  refine ⟨operationsIsCid_witnessVector 32 _ _ _, ?_⟩
  rw [Circuit.bind_operations_eq, operationsIsCid_append,
    (CostIs.forEach fun _ m => CostIs.assertZero _ m) _]
  refine ⟨?_, operationsIsCid_pure _ _ _⟩
  rw [Circuit.forEach.operations_eq]
  refine operationsIsCid_flatten_ofFn (L := 1)
    (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
  simp only [Vector.getElem_finRange, Nat.mul_one]
  refine ⟨?_, trivial⟩
  rw [wv_getElem]
  exact isCidentityRowAt_var_sub_mul (b32_affine hb _) Affine.one

end

theorem isCidentity_sub (b : Var (fields 32) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_ops b hb)

theorem balanced_sub (b : Var (fields 32) (F p2)) :
    Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Pin32Canon

namespace PinStateCanon

theorem b512_affine {v : Var (fields 512) (F p2)} (hv : AffineW v) (i : ℕ) :
    Affine (b512 v i) :=
  hv _ (Nat.mod_lt _ (by norm_num))

theorem costIs_main (b : Var (fields 512) (F p2)) : CostIs (main b) ⟨512, 512⟩ := by
  unfold main
  have hcount : (⟨512, 0⟩ + (⟨512 * 0, 512 * 1⟩ + ⟨0, 0⟩) : Count) = ⟨512, 512⟩ := by
    show (⟨_, _⟩ : Count) = _
    congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 512 _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun _ m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var (fields 512) (F p2)) :
    CostIs (subcircuit circuit b) ⟨512, 512⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

section

attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

set_option maxRecDepth 2000 in
theorem isCidentity_ops (b : Var (fields 512) (F p2)) (hb : AffineW b) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 512 _ n]
  refine ⟨operationsIsCid_witnessVector 512 _ _ _, ?_⟩
  rw [Circuit.bind_operations_eq, operationsIsCid_append,
    (CostIs.forEach fun _ m => CostIs.assertZero _ m) _]
  refine ⟨?_, operationsIsCid_pure _ _ _⟩
  rw [Circuit.forEach.operations_eq]
  refine operationsIsCid_flatten_ofFn (L := 1)
    (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
  simp only [Vector.getElem_finRange, Nat.mul_one]
  refine ⟨?_, trivial⟩
  rw [wv_getElem]
  exact isCidentityRowAt_var_sub_mul (b512_affine hb _) Affine.one

end

theorem isCidentity_sub (b : Var (fields 512) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_ops b hb)

theorem balanced_sub (b : Var (fields 512) (F p2)) :
    Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end PinStateCanon

namespace AddExact

theorem costIs_main (b : Var Add32.Inputs (F p2)) : CostIs (main b) ⟨94, 94⟩ :=
  CostIs.bind (Add32Canon.costIs_sub b) fun _ => Pin32Canon.costIs_sub _

theorem costIs_sub (b : Var Add32.Inputs (F p2)) :
    CostIs (subcircuit circuit b) ⟨94, 94⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

theorem balanced_sub (b : Var Add32.Inputs (F p2)) :
    Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end AddExact

namespace XorRotateExact

theorem costIs_main (n : ℕ) (b : Var Inputs (F p2)) :
    CostIs (main n b) ⟨32, 32⟩ :=
  Pin32Canon.costIs_sub _

theorem costIs_sub (n : ℕ) (b : Var Inputs (F p2)) :
    CostIs (subcircuit (circuit n) b) ⟨32, 32⟩ :=
  CostIs.subcircuit (fun k => costIs_main n b k)

theorem balanced_sub (n : ℕ) (b : Var Inputs (F p2)) :
    Balanced (subcircuit (circuit n) b) :=
  Balanced.of_costIs (costIs_sub n b) fun k => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end XorRotateExact

namespace PinQuadExact

theorem costIs_main (b : Var Quad (F p2)) : CostIs (main b) ⟨128, 128⟩ :=
  CostIs.bind (Pin32Canon.costIs_sub b.a) fun _ =>
  CostIs.bind (Pin32Canon.costIs_sub b.b) fun _ =>
  CostIs.bind (Pin32Canon.costIs_sub b.c) fun _ =>
  CostIs.bind (Pin32Canon.costIs_sub b.d) fun _ =>
  CostIs.pure _

theorem costIs_sub (b : Var Quad (F p2)) :
    CostIs (subcircuit circuit b) ⟨128, 128⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

theorem balanced_sub (b : Var Quad (F p2)) :
    Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end PinQuadExact

namespace GFirst

theorem costIs_main (b : Var GInputs (F p2)) : CostIs (main b) ⟨474, 474⟩ :=
  CostIs.bind (AddExact.costIs_sub _) fun _ =>
  CostIs.bind (AddExact.costIs_sub _) fun _ =>
  CostIs.bind (XorRotateExact.costIs_sub 16 _) fun _ =>
  CostIs.bind (AddExact.costIs_sub _) fun _ =>
  CostIs.bind (XorRotateExact.costIs_sub 12 _) fun _ =>
  PinQuadExact.costIs_sub _

theorem costIs_sub (b : Var GInputs (F p2)) :
    CostIs (subcircuit circuit b) ⟨474, 474⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

theorem balanced_sub (b : Var GInputs (F p2)) :
    Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end GFirst

namespace GSecond

theorem costIs_main (b : Var GInputs (F p2)) : CostIs (main b) ⟨474, 474⟩ :=
  CostIs.bind (AddExact.costIs_sub _) fun _ =>
  CostIs.bind (AddExact.costIs_sub _) fun _ =>
  CostIs.bind (XorRotateExact.costIs_sub 8 _) fun _ =>
  CostIs.bind (AddExact.costIs_sub _) fun _ =>
  CostIs.bind (XorRotateExact.costIs_sub 7 _) fun _ =>
  PinQuadExact.costIs_sub _

theorem costIs_sub (b : Var GInputs (F p2)) :
    CostIs (subcircuit circuit b) ⟨474, 474⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

theorem balanced_sub (b : Var GInputs (F p2)) :
    Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end GSecond

namespace G

theorem costIs_main (b : Var GInputs (F p2)) : CostIs (main b) ⟨948, 948⟩ :=
  CostIs.bind (GFirst.costIs_sub b) fun _ => GSecond.costIs_sub _

theorem costIs_sub (b : Var GInputs (F p2)) :
    CostIs (subcircuit circuit b) ⟨948, 948⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

theorem balanced_sub (b : Var GInputs (F p2)) :
    Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end G

namespace ApplyG

theorem costIs_main (a b c d : Fin 16) (x : Var Inputs (F p2)) :
    CostIs (main a b c d x) ⟨1460, 1460⟩ :=
  CostIs.bind (G.costIs_sub _) fun _ => PinStateCanon.costIs_sub _

theorem costIs_sub (a b c d : Fin 16) (x : Var Inputs (F p2)) :
    CostIs (subcircuit (circuit a b c d) x) ⟨1460, 1460⟩ :=
  CostIs.subcircuit (fun n => costIs_main a b c d x n)

theorem balanced_sub (a b c d : Fin 16) (x : Var Inputs (F p2)) :
    Balanced (subcircuit (circuit a b c d) x) :=
  Balanced.of_costIs (costIs_sub a b c d x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end ApplyG

namespace Round.Pair

theorem costIs_main
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (x : Var Round.Inputs (F p2)) :
    CostIs (main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 x) ⟨2920, 2920⟩ :=
  CostIs.bind (ApplyG.costIs_sub _ _ _ _ _) fun _ =>
  ApplyG.costIs_sub _ _ _ _ _

theorem costIs_sub
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (x : Var Round.Inputs (F p2)) :
    CostIs (subcircuit (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) x)
      ⟨2920, 2920⟩ :=
  CostIs.subcircuit (fun n =>
    costIs_main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 x n)

theorem balanced_sub
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (x : Var Round.Inputs (F p2)) :
    Balanced (subcircuit (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) x) :=
  Balanced.of_costIs
    (costIs_sub a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 x) fun n => by
      simp [circuit_norm, subcircuit, circuit, elaborated]

end Round.Pair

namespace Round.Columns

theorem costIs_main (x : Var Round.Inputs (F p2)) :
    CostIs (main x) ⟨5840, 5840⟩ :=
  CostIs.bind (Round.Pair.costIs_sub _ _ _ _ _ _ _ _ _ _ _ _ x) fun _ =>
  Round.Pair.costIs_sub _ _ _ _ _ _ _ _ _ _ _ _ _

theorem costIs_sub (x : Var Round.Inputs (F p2)) :
    CostIs (subcircuit circuit x) ⟨5840, 5840⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Round.Inputs (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Round.Columns

namespace Round.Diagonals

theorem costIs_main (x : Var Round.Inputs (F p2)) :
    CostIs (main x) ⟨5840, 5840⟩ :=
  CostIs.bind (Round.Pair.costIs_sub _ _ _ _ _ _ _ _ _ _ _ _ x) fun _ =>
  Round.Pair.costIs_sub _ _ _ _ _ _ _ _ _ _ _ _ _

theorem costIs_sub (x : Var Round.Inputs (F p2)) :
    CostIs (subcircuit circuit x) ⟨5840, 5840⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Round.Inputs (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Round.Diagonals

namespace Round

theorem costIs_main (x : Var Inputs (F p2)) : CostIs (main x) ⟨11680, 11680⟩ :=
  CostIs.bind (Columns.costIs_sub x) fun _ => Diagonals.costIs_sub _

theorem costIs_sub (x : Var Inputs (F p2)) :
    CostIs (subcircuit circuit x) ⟨11680, 11680⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Inputs (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Round

namespace Prepare

theorem costIs_main (x : Var Input (F p2)) : CostIs (main x) ⟨1024, 1024⟩ :=
  CostIs.bind (PinStateCanon.costIs_sub _) fun _ =>
  CostIs.bind (PinStateCanon.costIs_sub _) fun _ =>
  CostIs.pure _

theorem costIs_sub (x : Var Input (F p2)) :
    CostIs (subcircuit circuit x) ⟨1024, 1024⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Input (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Prepare

namespace Step

theorem costIs_main (x : Var Config (F p2)) : CostIs (main x) ⟨12192, 12192⟩ :=
  CostIs.bind (Round.costIs_sub _) fun _ =>
  CostIs.bind (PinStateCanon.costIs_sub _) fun _ =>
  CostIs.pure _

theorem costIs_sub (x : Var Config (F p2)) :
    CostIs (subcircuit circuit x) ⟨12192, 12192⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Config (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Step

namespace Steps2

theorem costIs_main (x : Var Config (F p2)) : CostIs (main x) ⟨24384, 24384⟩ :=
  CostIs.bind (Step.costIs_sub x) fun _ => Step.costIs_sub _

theorem costIs_sub (x : Var Config (F p2)) :
    CostIs (subcircuit circuit x) ⟨24384, 24384⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Config (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Steps2

namespace Steps4

theorem costIs_main (x : Var Config (F p2)) : CostIs (main x) ⟨48768, 48768⟩ :=
  CostIs.bind (Steps2.costIs_sub x) fun _ => Steps2.costIs_sub _

theorem costIs_sub (x : Var Config (F p2)) :
    CostIs (subcircuit circuit x) ⟨48768, 48768⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Config (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Steps4

namespace Steps7

theorem costIs_main (x : Var Config (F p2)) : CostIs (main x) ⟨85344, 85344⟩ :=
  CostIs.bind (Steps4.costIs_sub x) fun _ =>
  CostIs.bind (Steps2.costIs_sub _) fun _ =>
  Step.costIs_sub _

theorem costIs_sub (x : Var Config (F p2)) :
    CostIs (subcircuit circuit x) ⟨85344, 85344⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Config (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Steps7

namespace Finalize

theorem costIs_main (x : Var Inputs (F p2)) : CostIs (main x) ⟨512, 512⟩ :=
  PinStateCanon.costIs_sub _

theorem costIs_sub (x : Var Inputs (F p2)) :
    CostIs (subcircuit circuit x) ⟨512, 512⟩ :=
  CostIs.subcircuit (fun n => costIs_main x n)

theorem balanced_sub (x : Var Inputs (F p2)) :
    Balanced (subcircuit circuit x) :=
  Balanced.of_costIs (costIs_sub x) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end Finalize

theorem mainCostInternal :
    Challenge.CostR1CS.circuitCost main ⟨86880, 86880⟩ := by
  intro input
  exact
    (CostIs.bind (Prepare.costIs_sub input) fun _ =>
      CostIs.bind (Steps7.costIs_sub _) fun _ =>
      CostIs.bind (Finalize.costIs_sub _) fun _ =>
      CostIs.pure _
      : CostIs (main input) ⟨86880, 86880⟩)

end Solution.Blake3CompressGF2Canonical
