import Solution.SHA256CompressGF2.Add32
import Solution.SHA256CompressGF2.Ch32
import Solution.SHA256CompressGF2.Maj32
import Solution.SHA256CompressGF2.Pin32
import Solution.SHA256CompressGF2.ScheduleStep
import Solution.SHA256CompressGF2.Round
import Solution.SHA256CompressGF2.Pin256
import Solution.SHA256CompressGF2.Sched16
import Solution.SHA256CompressGF2.Rounds16
import Solution.SHA256CompressGF2.MainTheorems

/-!
# Cost and R1CS certificates

Structural operation-count (`CostIs`) and single-row-R1CS (`IsR1CSCirc` /
`AffineW`) certificates for every gadget, kept out of the functional files.
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Add32

/-- One adder costs 31 witnesses / 31 constraints (flock's `CARRIES_PER_ADD`). -/
theorem costIs_main (b : Var Inputs (F p2)) : CostIs (main b) ⟨31, 31⟩ := by
  unfold main
  have hcount : (⟨31, 0⟩ + (⟨31 * 0, 31 * 1⟩ + ⟨0, 0⟩) : Count) = ⟨31, 31⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 31 _) fun ns => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var Inputs (F p2)) :
    CostIs (subcircuit circuit b) ⟨31, 31⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

/-- Index-aware `forEach` R1CS combinator over `F p2`. -/
theorem isR1CSCirc_forEach_mem {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F p2) Unit} {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

/-- `at32` of an affine vector is affine. -/
theorem at32_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (at32 v k) :=
  hv _ (Nat.mod_lt _ (by norm_num))

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- Every constraint row of `Add32.main` is a single R1CS row (`C − A·B` with
all of `A, B, C` affine), given affine inputs. -/
theorem isR1CS_main (b : Var Inputs (F p2)) (hx : AffineW b.x) (hy : AffineW b.y) :
    IsR1CSCirc (main b) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 31 _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine isR1CSCirc_forEach_mem fun i k => ?_
    simp only [Vector.getElem_finRange]
    refine IsR1CSCirc.assertZero ?_ k
    by_cases hi0 : i.val = 0
    · simp only [carryE, hi0, reduceIte]
      exact isR1CSRow_sub_mul
        (Affine.sub (affineW_witnessVector_output 31 _ w _ (Nat.mod_lt _ (by norm_num)))
          Affine.zero)
        (Affine.add (hx _ (Nat.mod_lt _ (by norm_num))) Affine.zero)
        (Affine.add (hy _ (Nat.mod_lt _ (by norm_num))) Affine.zero)
    · simp only [carryE, if_neg hi0]
      exact isR1CSRow_sub_mul
        (Affine.sub (affineW_witnessVector_output 31 _ w _ (Nat.mod_lt _ (by norm_num)))
          (affineW_witnessVector_output 31 _ w _ (Nat.mod_lt _ (by norm_num))))
        (Affine.add (hx _ (Nat.mod_lt _ (by norm_num)))
          (affineW_witnessVector_output 31 _ w _ (Nat.mod_lt _ (by norm_num))))
        (Affine.add (hy _ (Nat.mod_lt _ (by norm_num)))
          (affineW_witnessVector_output 31 _ w _ (Nat.mod_lt _ (by norm_num))))
  · exact IsR1CSCirc.pure _

theorem isR1CS_sub (b : Var Inputs (F p2)) (hx : AffineW b.x) (hy : AffineW b.y) :
    IsR1CSCirc (subcircuit circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main b hx hy n)

end Add32

open Add32 (isR1CSCirc_forEach_mem)

/-- `a96` of an affine vector is affine. -/
theorem a96_affine {v : Var (fields 96) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (a96 v k) :=
  hv _ (Nat.mod_lt _ (by norm_num))

/-- `b32` of an affine vector is affine. -/
theorem b32_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (b32 v k) :=
  hv _ (Nat.mod_lt _ (by norm_num))

theorem b512_affine {v : Var (fields 512) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (b512 v k) := hv _ (Nat.mod_lt _ (by norm_num))

theorem a256_affine {v : Var (fields 256) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (a256 v k) := hv _ (Nat.mod_lt _ (by norm_num))

namespace Ch32

theorem costIs_main (b : Var (fields 96) (F p2)) : CostIs (main b) ⟨32, 32⟩ := by
  unfold main
  have hcount : (⟨32, 0⟩ + (⟨32 * 0, 32 * 1⟩ + ⟨0, 0⟩) : Count) = ⟨32, 32⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 32 _) fun ns => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var (fields 96) (F p2)) : CostIs (subcircuit circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS a96

theorem isR1CS_main (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (main b) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine isR1CSCirc_forEach_mem fun i k => ?_
    simp only [Vector.getElem_finRange]
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_sub_mul
      (Affine.sub (affineW_witnessVector_output 32 _ w i.val i.isLt)
        (a96_affine hb _))
      (a96_affine hb _)
      (Affine.add (a96_affine hb _) (a96_affine hb _))
  · exact IsR1CSCirc.pure _

theorem isR1CS_sub (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main b hb n)

end Ch32

namespace Maj32

theorem costIs_main (b : Var (fields 96) (F p2)) : CostIs (main b) ⟨32, 32⟩ := by
  unfold main
  have hcount : (⟨32, 0⟩ + (⟨32 * 0, 32 * 1⟩ + ⟨0, 0⟩) : Count) = ⟨32, 32⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 32 _) fun ns => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var (fields 96) (F p2)) : CostIs (subcircuit circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS a96

theorem isR1CS_main (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (main b) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine isR1CSCirc_forEach_mem fun i k => ?_
    simp only [Vector.getElem_finRange]
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_sub_mul
      (Affine.sub (affineW_witnessVector_output 32 _ w i.val i.isLt)
        (a96_affine hb _))
      (Affine.add (a96_affine hb _) (a96_affine hb _))
      (Affine.add (a96_affine hb _) (a96_affine hb _))
  · exact IsR1CSCirc.pure _

theorem isR1CS_sub (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main b hb n)

end Maj32

namespace Pin32

theorem costIs_main (b : Var (fields 32) (F p2)) : CostIs (main b) ⟨32, 32⟩ := by
  unfold main
  have hcount : (⟨32, 0⟩ + (⟨32 * 0, 32 * 1⟩ + ⟨0, 0⟩) : Count) = ⟨32, 32⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 32 _) fun ns => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var (fields 32) (F p2)) : CostIs (subcircuit circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS b32

theorem isR1CS_main (b : Var (fields 32) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (main b) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine isR1CSCirc_forEach_mem fun i k => ?_
    simp only [Vector.getElem_finRange]
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_of_affine
      (Affine.sub (affineW_witnessVector_output 32 _ w i.val i.isLt)
        (b32_affine hb _))
  · exact IsR1CSCirc.pure _

theorem isR1CS_sub (b : Var (fields 32) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main b hb n)

end Pin32

theorem a128_affine {v : Var (fields 128) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (a128 v k) :=
  hv _ (Nat.mod_lt _ (by norm_num))

theorem c96_affine {x y z : Var (fields 32) (F p2)}
    (hx : AffineW x) (hy : AffineW y) (hz : AffineW z) : AffineW (c96 x y z) := by
  intro i hi
  unfold c96
  rw [Vector.getElem_ofFn]
  split
  · exact b32_affine hx _
  split
  · exact b32_affine hy _
  · exact b32_affine hz _

theorem c128_affine {x y z w : Var (fields 32) (F p2)}
    (hx : AffineW x) (hy : AffineW y) (hz : AffineW z) (hw : AffineW w) :
    AffineW (c128 x y z w) := by
  intro i hi
  unfold c128
  rw [Vector.getElem_ofFn]
  split
  · exact b32_affine hx _
  split
  · exact b32_affine hy _
  split
  · exact b32_affine hz _
  · exact b32_affine hw _

theorem w128_affine {v : Var (fields 128) (F p2)} (hv : AffineW v) (k : ℕ) :
    AffineW (w128 v k) := by
  intro i hi
  unfold w128
  rw [Vector.getElem_ofFn]
  exact a128_affine hv _

theorem rotrE_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) (n : ℕ) :
    AffineW (rotrE n v) := by
  intro i hi
  unfold rotrE
  rw [Vector.getElem_ofFn]
  exact b32_affine hv _

theorem shrE_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) (n : ℕ) :
    AffineW (shrE n v) := by
  intro i hi
  unfold shrE
  rw [Vector.getElem_ofFn]
  split
  · exact b32_affine hv _
  · exact Affine.zero

theorem xor3E_affine {a b c : Var (fields 32) (F p2)}
    (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) : AffineW (xor3E a b c) := by
  intro i hi
  unfold xor3E
  rw [Vector.getElem_ofFn]
  exact Affine.add (Affine.add (b32_affine ha _) (b32_affine hb _)) (b32_affine hc _)

theorem lowerSigma0E_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) :
    AffineW (lowerSigma0E v) :=
  xor3E_affine (rotrE_affine hv 7) (rotrE_affine hv 18) (shrE_affine hv 3)

theorem lowerSigma1E_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) :
    AffineW (lowerSigma1E v) :=
  xor3E_affine (rotrE_affine hv 17) (rotrE_affine hv 19) (shrE_affine hv 10)

theorem upperSigma0E_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) :
    AffineW (upperSigma0E v) :=
  xor3E_affine (rotrE_affine hv 2) (rotrE_affine hv 13) (rotrE_affine hv 22)

theorem upperSigma1E_affine {v : Var (fields 32) (F p2)} (hv : AffineW v) :
    AffineW (upperSigma1E v) :=
  xor3E_affine (rotrE_affine hv 6) (rotrE_affine hv 11) (rotrE_affine hv 25)

/-- `Pin32`'s output is a fresh witness vector, hence affine. -/
theorem affineW_subOut_pin32 (b : Var (fields 32) (F p2)) (n : ℕ) :
    AffineW ((subcircuit Pin32.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, Pin32.circuit, Pin32.elaborated]
  exact affineW_mapRange_var _

/-- `Ch32`'s output is a fresh witness vector, hence affine. -/
theorem affineW_subOut_ch32 (b : Var (fields 96) (F p2)) (n : ℕ) :
    AffineW ((subcircuit Ch32.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, Ch32.circuit, Ch32.elaborated]
  exact affineW_mapRange_var _

/-- `Maj32`'s output is a fresh witness vector, hence affine. -/
theorem affineW_subOut_maj32 (b : Var (fields 96) (F p2)) (n : ℕ) :
    AffineW ((subcircuit Maj32.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, Maj32.circuit, Maj32.elaborated]
  exact affineW_mapRange_var _

/-- `Add32`'s output entries are `x_i + y_i + carry_i`, affine given affine
inputs (the carries are fresh witness variables). -/
theorem affineW_subOut_add32 (b : Var Add32.Inputs (F p2))
    (hx : AffineW b.x) (hy : AffineW b.y) (n : ℕ) :
    AffineW ((subcircuit Add32.circuit b).output n) := by
  intro j hj
  simp only [circuit_norm, subcircuit, Add32.circuit, Add32.elaborated, Vector.getElem_ofFn]
  refine Affine.add (Affine.add (hx _ (Nat.mod_lt _ (by norm_num)))
    (hy _ (Nat.mod_lt _ (by norm_num)))) ?_
  unfold Add32.carryE
  split
  · exact Affine.zero
  · exact affineW_mapRange_var _ _ (Nat.mod_lt _ (by norm_num))

/-- Component-wise variants (no struct projections at use sites). -/
theorem add32_r1cs (x y : Var (fields 32) (F p2)) (hx : AffineW x) (hy : AffineW y) :
    IsR1CSCirc (subcircuit Add32.circuit ⟨x, y⟩) :=
  Add32.isR1CS_sub ⟨x, y⟩ hx hy

theorem affineW_out_add32 (x y : Var (fields 32) (F p2))
    (hx : AffineW x) (hy : AffineW y) (n : ℕ) :
    AffineW ((subcircuit Add32.circuit (⟨x, y⟩ : Var Add32.Inputs (F p2))).output n) :=
  affineW_subOut_add32 ⟨x, y⟩ hx hy n

namespace ScheduleStep

/-- 3 adders + one pin: `⟨125, 125⟩`. -/
theorem costIs_main (b : Var (fields 128) (F p2)) : CostIs (main b) ⟨125, 125⟩ :=
  fun n => (CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Pin32.costIs_sub _) fun _ =>
    CostIs.pure _ : CostIs (main b) (⟨31, 31⟩ + (⟨31, 31⟩ + (⟨31, 31⟩ + (⟨32, 32⟩ + ⟨0, 0⟩))))) n

theorem costIs_sub (b : Var (fields 128) (F p2)) : CostIs (subcircuit circuit b) ⟨125, 125⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

theorem isR1CS_main (b : Var (fields 128) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (main b) := by
  have h1 : AffineW (lowerSigma1E (w128 b 3)) := lowerSigma1E_affine (w128_affine hb 3)
  have h0 : AffineW (lowerSigma0E (w128 b 1)) := lowerSigma0E_affine (w128_affine hb 1)
  have hw2 : AffineW (w128 b 2) := w128_affine hb 2
  have hw0 : AffineW (w128 b 0) := w128_affine hb 0
  unfold main
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ h1 hw2) fun n1 => ?_
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ h0 hw0) fun n2 => ?_
  refine IsR1CSCirc.bind_out
    (add32_r1cs _ _ (affineW_out_add32 _ _ h1 hw2 n1) (affineW_out_add32 _ _ h0 hw0 n2)) fun n3 => ?_
  refine IsR1CSCirc.bind
    (Pin32.isR1CS_sub _
      (affineW_out_add32 _ _ (affineW_out_add32 _ _ h1 hw2 n1) (affineW_out_add32 _ _ h0 hw0 n2) n3)) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_sub (b : Var (fields 128) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main b hb n)

end ScheduleStep

theorem a288_affine {v : Var (fields 288) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (a288 v k) :=
  hv _ (Nat.mod_lt _ (by norm_num))

theorem w288_affine {v : Var (fields 288) (F p2)} (hv : AffineW v) (k : ℕ) :
    AffineW (w288 v k) := by
  intro i hi
  unfold w288
  rw [Vector.getElem_ofFn]
  exact a288_affine hv _

theorem constW_affine (n : ℕ) : AffineW (constW n) := by
  intro i hi
  unfold constW
  rw [Vector.getElem_ofFn]
  exact Affine.const _

theorem outState_affine {A E : Var (fields 32) (F p2)} {v : Var (fields 288) (F p2)}
    (hA : AffineW A) (hE : AffineW E) (hv : AffineW v) : AffineW (outState A E v) := by
  intro i hi
  unfold outState
  rw [Vector.getElem_ofFn]
  split
  · exact b32_affine hA _
  split
  · exact a288_affine hv _
  split
  · exact b32_affine hE _
  · exact a288_affine hv _

namespace Round

/-- 7 adders + Ch + Maj + 2 pins: `⟨345, 345⟩`. -/
theorem costIs_main (k : ℕ) (b : Var (fields 288) (F p2)) : CostIs (main k b) ⟨345, 345⟩ :=
  fun n => (CostIs.bind (Ch32.costIs_sub _) fun _ =>
    CostIs.bind (Maj32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Add32.costIs_sub _) fun _ =>
    CostIs.bind (Pin32.costIs_sub _) fun _ =>
    CostIs.bind (Pin32.costIs_sub _) fun _ =>
    CostIs.pure _
      : CostIs (main k b) (⟨32,32⟩ + (⟨32,32⟩ + (⟨31,31⟩ + (⟨31,31⟩ + (⟨31,31⟩ + (⟨31,31⟩
          + (⟨31,31⟩ + (⟨31,31⟩ + (⟨31,31⟩ + (⟨32,32⟩ + (⟨32,32⟩ + ⟨0,0⟩)))))))))))) n

theorem costIs_sub (k : ℕ) (b : Var (fields 288) (F p2)) :
    CostIs (subcircuit (circuit k) b) ⟨345, 345⟩ :=
  CostIs.subcircuit (fun n => costIs_main k b n)

theorem isR1CS_main (k : ℕ) (b : Var (fields 288) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (main k b) := by
  have hS1 : AffineW (upperSigma1E (w288 b 4)) := upperSigma1E_affine (w288_affine hb 4)
  have hS0 : AffineW (upperSigma0E (w288 b 0)) := upperSigma0E_affine (w288_affine hb 0)
  have hcK : AffineW (constW k) := constW_affine k
  unfold main
  refine IsR1CSCirc.bind_out
    (Ch32.isR1CS_sub _ (c96_affine (w288_affine hb 4) (w288_affine hb 5) (w288_affine hb 6))) fun nc => ?_
  refine IsR1CSCirc.bind_out
    (Maj32.isR1CS_sub _ (c96_affine (w288_affine hb 0) (w288_affine hb 1) (w288_affine hb 2))) fun nm => ?_
  have hch : AffineW ((subcircuit Ch32.circuit
      (c96 (w288 b 4) (w288 b 5) (w288 b 6))).output nc) := affineW_subOut_ch32 _ _
  have hmj : AffineW ((subcircuit Maj32.circuit
      (c96 (w288 b 0) (w288 b 1) (w288 b 2))).output nm) := affineW_subOut_maj32 _ _
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ (w288_affine hb 7) hS1) fun n1 => ?_
  have ha1 := affineW_out_add32 _ _ (w288_affine hb 7) hS1 n1
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ ha1 hch) fun n2 => ?_
  have ha2 := affineW_out_add32 _ _ ha1 hch n2
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ ha2 hcK) fun n3 => ?_
  have ha3 := affineW_out_add32 _ _ ha2 hcK n3
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ ha3 (w288_affine hb 8)) fun n4 => ?_
  have ht1 := affineW_out_add32 _ _ ha3 (w288_affine hb 8) n4
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ hS0 hmj) fun n5 => ?_
  have ht2 := affineW_out_add32 _ _ hS0 hmj n5
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ (w288_affine hb 3) ht1) fun n6 => ?_
  have hen := affineW_out_add32 _ _ (w288_affine hb 3) ht1 n6
  refine IsR1CSCirc.bind_out (add32_r1cs _ _ ht1 ht2) fun n7 => ?_
  have han := affineW_out_add32 _ _ ht1 ht2 n7
  refine IsR1CSCirc.bind_out (Pin32.isR1CS_sub _ han) fun n8 => ?_
  refine IsR1CSCirc.bind (Pin32.isR1CS_sub _ hen) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem isR1CS_sub (k : ℕ) (b : Var (fields 288) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit (circuit k) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main k b hb n)

/-- The round's output is affine given an affine input (pinned words + input
pass-through). -/
theorem affineW_subOut (k : ℕ) (b : Var (fields 288) (F p2)) (hb : AffineW b) (n : ℕ) :
    AffineW ((subcircuit (circuit k) b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact outState_affine (affineW_mapRange_var _) (affineW_mapRange_var _) hb

end Round

theorem b256_affine {v : Var (fields 256) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (b256 v k) := hv _ (Nat.mod_lt _ (by norm_num))

namespace Pin256

theorem costIs_main (b : Var (fields 256) (F p2)) : CostIs (main b) ⟨256, 256⟩ := by
  unfold main
  have hcount : (⟨256, 0⟩ + (⟨256 * 0, 256 * 1⟩ + ⟨0, 0⟩) : Count) = ⟨256, 256⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 256 _) fun ns => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var (fields 256) (F p2)) : CostIs (subcircuit circuit b) ⟨256, 256⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS b256

theorem isR1CS_main (b : Var (fields 256) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (main b) := by
  unfold main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 256 _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine Add32.isR1CSCirc_forEach_mem fun i k => ?_
    simp only [Vector.getElem_finRange]
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_of_affine
      (Affine.sub (affineW_witnessVector_output 256 _ w i.val i.isLt)
        (b256_affine hb _))
  · exact IsR1CSCirc.pure _

theorem isR1CS_sub (b : Var (fields 256) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main b hb n)

theorem affineW_subOut (b : Var (fields 256) (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

end Pin256

theorem q512_affine {v : Var (fields 512) (F p2)} (hv : AffineW v) (k : ℕ) :
    AffineW (q512 v k) := by
  intro i hi
  unfold q512
  rw [Vector.getElem_ofFn]
  exact b512_affine hv _

theorem c512_affine {w : Fin 16 → Var (fields 32) (F p2)}
    (hw : ∀ j, AffineW (w j)) : AffineW (c512 w) := by
  intro i hi
  unfold c512
  rw [Vector.getElem_ofFn]
  exact b32_affine (hw _) _

theorem c512sel_affine {u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : Var (fields 32) (F p2)}
    (h0 : AffineW u0) (h1 : AffineW u1) (h2 : AffineW u2) (h3 : AffineW u3) (h4 : AffineW u4) (h5 : AffineW u5) (h6 : AffineW u6) (h7 : AffineW u7) (h8 : AffineW u8) (h9 : AffineW u9) (h10 : AffineW u10) (h11 : AffineW u11) (h12 : AffineW u12) (h13 : AffineW u13) (h14 : AffineW u14) (h15 : AffineW u15) :
    ∀ k, AffineW (c512sel u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 k)
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | 3 => h3
  | 4 => h4
  | 5 => h5
  | 6 => h6
  | 7 => h7
  | 8 => h8
  | 9 => h9
  | 10 => h10
  | 11 => h11
  | 12 => h12
  | 13 => h13
  | 14 => h14
  | (_ + 15) => h15

theorem c512x_affine {u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : Var (fields 32) (F p2)}
    (h0 : AffineW u0) (h1 : AffineW u1) (h2 : AffineW u2) (h3 : AffineW u3) (h4 : AffineW u4) (h5 : AffineW u5) (h6 : AffineW u6) (h7 : AffineW u7) (h8 : AffineW u8) (h9 : AffineW u9) (h10 : AffineW u10) (h11 : AffineW u11) (h12 : AffineW u12) (h13 : AffineW u13) (h14 : AffineW u14) (h15 : AffineW u15) :
    AffineW (c512x u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15) := by
  intro i hi
  unfold c512x
  rw [Vector.getElem_ofFn]
  exact b32_affine (c512sel_affine h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 _) _

/-- `ScheduleStep`'s output is a fresh witness vector, hence affine. -/
theorem affineW_subOut_sched (b : Var (fields 128) (F p2)) (n : ℕ) :
    AffineW ((subcircuit ScheduleStep.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, ScheduleStep.circuit, ScheduleStep.elaborated]
  exact affineW_mapRange_var _

namespace Sched16

theorem costIs_main (b : Var (fields 512) (F p2)) : CostIs (main b) ⟨2000, 2000⟩ := by
  unfold main
  exact CostIs.bind (CostIs.foldlRange (constant := constantLength)
      fun _ _ n => (CostIs.bind (ScheduleStep.costIs_sub _) fun _ => CostIs.pure _) n)
    fun _ => CostIs.pure _

theorem costIs_sub (b : Var (fields 512) (F p2)) : CostIs (subcircuit circuit b) ⟨2000, 2000⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem isR1CS_main (b : Var (fields 512) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (main b) := by
  rw [main]
  apply IsR1CSCirc.bind_out
  · refine IsR1CSCirc.foldlRange_inv (constant := constantLength)
      (fun w => ∀ k (hk : k < 32), AffineW (w[k]'hk)) ?_ ?_ ?_
    · intro k hk
      show AffineW (((Vector.ofFn fun j : Fin 16 => q512 b j.val) ++
        Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))[k]'hk)
      rw [Vector.getElem_append]
      split
      · rw [Vector.getElem_ofFn]; exact q512_affine hb _
      · rw [Vector.getElem_replicate]; intro j hj; rw [Vector.getElem_replicate]; exact Affine.zero
    · intro w i hw
      exact IsR1CSCirc.bind_out (ScheduleStep.isR1CS_sub _
        (c128_affine (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega))))
        (fun _ => IsR1CSCirc.pure _)
    · intro w i n hw k hk
      simp only [circuit_norm, Vector.getElem_set]
      split
      · exact affineW_varFromOffset _ _
      · exact hw _ _
  · exact fun n => IsR1CSCirc.pure _

theorem isR1CS_sub (b : Var (fields 512) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main b hb n)

/-- The chunk's output words are `ScheduleStep` outputs, hence affine. -/
theorem affineW_subOut (b : Var (fields 512) (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated, stepWord]
  exact c512x_affine
    (affineW_varFromOffset _ _) (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
    (affineW_varFromOffset _ _) (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
    (affineW_varFromOffset _ _) (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
    (affineW_varFromOffset _ _) (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
    (affineW_varFromOffset _ _) (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
    (affineW_varFromOffset _ _)

end Sched16

theorem a768_affine {v : Var (fields 768) (F p2)} (hv : AffineW v) (k : ℕ) :
    Affine (a768 v k) := hv _ (Nat.mod_lt _ (by norm_num))

theorem q768_affine {v : Var (fields 768) (F p2)} (hv : AffineW v) (k : ℕ) :
    AffineW (q768 v k) := by
  intro i hi
  unfold q768
  rw [Vector.getElem_ofFn]
  exact a768_affine hv _

theorem st768_affine {v : Var (fields 768) (F p2)} (hv : AffineW v) :
    AffineW (st768 v) := by
  intro i hi
  unfold st768
  rw [Vector.getElem_ofFn]
  exact a768_affine hv _

theorem c288s_affine {s : Var (fields 256) (F p2)} {w : Var (fields 32) (F p2)}
    (hs : AffineW s) (hw : AffineW w) : AffineW (c288s s w) := by
  intro i hi
  unfold c288s
  rw [Vector.getElem_ofFn]
  split
  · exact a256_affine hs _
  · exact b32_affine hw _

/-- `Round.affineW_subOut` with implicit input (inferred from the hypothesis). -/
theorem round_out_affine (k : ℕ) {b : Var (fields 288) (F p2)} (hb : AffineW b) (n : ℕ) :
    AffineW ((subcircuit (Round.circuit k) b).output n) :=
  Round.affineW_subOut k b hb n

namespace Rounds16

theorem costIs_main (r0 : ℕ) (b : Var (fields 768) (F p2)) : CostIs (main r0 b) ⟨5776, 5776⟩ :=
  CostIs.bind (CostIs.foldlRange fun _ _ n => Round.costIs_sub _ _ n) fun _ =>
    Pin256.costIs_sub _

theorem costIs_sub (r0 : ℕ) (b : Var (fields 768) (F p2)) :
    CostIs (subcircuit (circuit r0) b) ⟨5776, 5776⟩ :=
  CostIs.subcircuit (fun n => costIs_main r0 b n)

/-- The 16-round fold's output is a witnessed round state, hence affine. -/
theorem affineW_rounds_foldOut (r0 : ℕ) (b : Var (fields 768) (F p2)) (hb : AffineW b) (n : ℕ) :
    AffineW ((Circuit.foldlRange 16 (st768 b) (fun s i =>
      Round.circuit (kAt (r0 + i.val)) (c288s s (q768 b (8 + i.val)))) (constantLength r0 b)).output n) := by
  rw [Circuit.foldlRange.output_eq]
  refine finFoldl_invariant (fun s => AffineW s) _ _ (st768_affine hb) ?_
  intro acc i hacc
  exact round_out_affine _ (c288s_affine hacc (q768_affine hb (8 + i.val))) _

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem isR1CS_main (r0 : ℕ) (b : Var (fields 768) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (main r0 b) := by
  rw [main]
  apply IsR1CSCirc.bind_out
  · exact IsR1CSCirc.foldlRange_inv (fun s => AffineW s) (st768_affine hb)
      (fun s i hs => Round.isR1CS_sub _ _ (c288s_affine hs (q768_affine hb (8 + i.val))))
      (fun s i n hs => round_out_affine _ (c288s_affine hs (q768_affine hb (8 + i.val))) _)
  · exact fun n => Pin256.isR1CS_sub _ (affineW_rounds_foldOut r0 b hb n)

theorem isR1CS_sub (r0 : ℕ) (b : Var (fields 768) (F p2)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit (circuit r0) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_main r0 b hb n)

/-- The chunk's output is a `Pin256` witness vector, hence affine. -/
theorem affineW_subOut (r0 : ℕ) (b : Var (fields 768) (F p2)) (n : ℕ) :
    AffineW ((subcircuit (circuit r0) b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

end Rounds16


/-! ## Top-level (`main`) affine helpers -/

theorem w256_affine {v : Var (fields 256) (F p2)} (hv : AffineW v) (k : ℕ) :
    AffineW (w256 v k) := by
  intro i hi
  unfold w256
  rw [Vector.getElem_ofFn]
  exact a256_affine hv _

theorem c768_affine {s : Var (fields 256) (F p2)} {w : Var (fields 512) (F p2)}
    (hs : AffineW s) (hw : AffineW w) : AffineW (c768 s w) := by
  intro i hi
  unfold c768
  rw [Vector.getElem_ofFn]
  split
  · exact a256_affine hs _
  · exact b512_affine hw _

/-- Output-word selector preserves affinity. -/
theorem o8sel_affine {o0 o1 o2 o3 o4 o5 o6 o7 : Var (fields 32) (F p2)}
    (h0 : AffineW o0) (h1 : AffineW o1) (h2 : AffineW o2) (h3 : AffineW o3)
    (h4 : AffineW o4) (h5 : AffineW o5) (h6 : AffineW o6) (h7 : AffineW o7) :
    ∀ k, AffineW (o8sel o0 o1 o2 o3 o4 o5 o6 o7 k)
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | 3 => h3
  | 4 => h4
  | 5 => h5
  | 6 => h6
  | (_ + 7) => h7

/-- `out256` of affine words is affine. -/
theorem out256_affine {o0 o1 o2 o3 o4 o5 o6 o7 : Var (fields 32) (F p2)}
    (h0 : AffineW o0) (h1 : AffineW o1) (h2 : AffineW o2) (h3 : AffineW o3)
    (h4 : AffineW o4) (h5 : AffineW o5) (h6 : AffineW o6) (h7 : AffineW o7) :
    AffineW (out256 o0 o1 o2 o3 o4 o5 o6 o7) := by
  intro i hi
  unfold out256
  rw [Vector.getElem_ofFn]
  exact b32_affine (o8sel_affine h0 h1 h2 h3 h4 h5 h6 h7 _) _

/-- The feed-forward output `out256` of 8 `Add32`s (adding the input `h` words to a shared
affine state `s4` at arbitrary offsets) is affine. The offsets `e0..e7` and the
state `s4` are abstract parameters so the unifier assigns them structurally, not
by reducing the deep composed circuit. -/
theorem out256_add32_affine {input : Var Input (F p2)} (hh : AffineW input.h)
    {s4 : Var (fields 256) (F p2)} (hs4 : AffineW s4)
    (e0 e1 e2 e3 e4 e5 e6 e7 : ℕ) :
    AffineW (out256
      ((subcircuit Add32.circuit ⟨w256 input.h 0, w256 s4 0⟩).output e0)
      ((subcircuit Add32.circuit ⟨w256 input.h 1, w256 s4 1⟩).output e1)
      ((subcircuit Add32.circuit ⟨w256 input.h 2, w256 s4 2⟩).output e2)
      ((subcircuit Add32.circuit ⟨w256 input.h 3, w256 s4 3⟩).output e3)
      ((subcircuit Add32.circuit ⟨w256 input.h 4, w256 s4 4⟩).output e4)
      ((subcircuit Add32.circuit ⟨w256 input.h 5, w256 s4 5⟩).output e5)
      ((subcircuit Add32.circuit ⟨w256 input.h 6, w256 s4 6⟩).output e6)
      ((subcircuit Add32.circuit ⟨w256 input.h 7, w256 s4 7⟩).output e7)) :=
  out256_affine
    (affineW_subOut_add32 ⟨w256 input.h 0, w256 s4 0⟩ (w256_affine hh 0) (w256_affine hs4 0) e0)
    (affineW_subOut_add32 ⟨w256 input.h 1, w256 s4 1⟩ (w256_affine hh 1) (w256_affine hs4 1) e1)
    (affineW_subOut_add32 ⟨w256 input.h 2, w256 s4 2⟩ (w256_affine hh 2) (w256_affine hs4 2) e2)
    (affineW_subOut_add32 ⟨w256 input.h 3, w256 s4 3⟩ (w256_affine hh 3) (w256_affine hs4 3) e3)
    (affineW_subOut_add32 ⟨w256 input.h 4, w256 s4 4⟩ (w256_affine hh 4) (w256_affine hs4 4) e4)
    (affineW_subOut_add32 ⟨w256 input.h 5, w256 s4 5⟩ (w256_affine hh 5) (w256_affine hs4 5) e5)
    (affineW_subOut_add32 ⟨w256 input.h 6, w256 s4 6⟩ (w256_affine hh 6) (w256_affine hs4 6) e6)
    (affineW_subOut_add32 ⟨w256 input.h 7, w256 s4 7⟩ (w256_affine hh 7) (w256_affine hs4 7) e7)

/-- Project the generic `AffineProvable` hypothesis onto the input `h` field. -/
theorem affineW_input_h {input : Var Input (F p2)} (hinput : AffineProvable input) :
    AffineW input.h := by
  intro i hi
  have hi256 : i < 256 := hi
  have hsz : size Input = 768 := rfl
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz, hi] using hinput i (by omega)

/-- Project the generic `AffineProvable` hypothesis onto the input `m` field. -/
theorem affineW_input_m {input : Var Input (F p2)} (hinput : AffineProvable input) :
    AffineW input.m := by
  intro i hi
  have hi512 : i < 512 := hi
  have hsz : size Input = 768 := rfl
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz, hi] using hinput (256 + i) (by omega)

end Solution.SHA256CompressGF2
