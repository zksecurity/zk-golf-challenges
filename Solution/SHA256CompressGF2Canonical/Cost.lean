import Solution.SHA256CompressGF2Canonical.Add32Canon
import Solution.SHA256CompressGF2Canonical.PinCanon
import Solution.SHA256CompressGF2Canonical.Ch32Canon
import Solution.SHA256CompressGF2Canonical.Maj32Canon
import Solution.SHA256CompressGF2Canonical.ScheduleStepCanon
import Solution.SHA256CompressGF2Canonical.RoundCanon
import Solution.SHA256CompressGF2Canonical.Sched16Canon
import Solution.SHA256CompressGF2Canonical.Rounds16Canon
import Solution.SHA256CompressGF2Canonical.Theorems
import Solution.SHA256CompressGF2.Cost
import Solution.SHA256CompressGF2.MainTheorems
import Challenge.Utils.CostR1CSCanonical

/-!
# Canonical cost and ordered identity-C (`IsCidCirc`) certificates

All `CostIs`/`IsCidCirc`/affine certificates for the canonical gadgets, kept out
of the functional files. `IsCidCirc` is the *ordered* certificate: the `t`-th
constraint of a block at offset `n` pins exactly variable `n + t`, so the pin
counter and the allocation offset march in lockstep through every (balanced)
composition; the `C` matrix is the identity, not a permutation. Each gadget's
block is wrapped in a `section` so its `attribute [local irreducible]` matches
the original per-file scope.
-/

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS
open Solution.SHA256CompressGF2
open Solution.SHA256CompressGF2.Add32 (at32 at31 carryVal carryE Inputs)

namespace Solution.SHA256CompressGF2.Add32Canon
section

/-- `at31` of a freshly witnessed 31-vector is the single output variable. -/
theorem at31_wv (c : ProverEnvironment (F p2) → Vector (F p2) 31) (w i : ℕ) :
    at31 ((Circuit.witnessVector 31 c).output w) i = Expression.var ⟨w + i % 31⟩ := by
  show ((Circuit.witnessVector 31 c).output w)[i % 31]'(Nat.mod_lt _ (by norm_num)) = _
  rw [show (Circuit.witnessVector 31 c).output w = varFromOffset (fields 31) w from rfl]
  simp only [varFromOffset, instProvableTypeFields, size, Vector.getElem_mapRange]

/-- The carry-into-bit expression is affine when the carry vector is affine. -/
theorem carryE_affine {carries : Var (fields 31) (F p2)} (hc : AffineW carries) (i : ℕ) :
    Affine (carryE carries i) := by
  unfold carryE
  by_cases hi : i = 0
  · simp only [hi, reduceIte]; exact Affine.zero
  · simp only [if_neg hi]; exact hc _ (Nat.mod_lt _ (by norm_num))

/-- `at31` of an affine 31-vector is affine. -/
theorem at31_affine {v : Var (fields 31) (F p2)} (hv : AffineW v) (i : ℕ) :
    Affine (at31 v i) :=
  hv _ (Nat.mod_lt _ (by norm_num))

/-- One canonical adder costs 62 witnesses / 62 constraints (2× `Add32`). -/
theorem costIs_main (b : Var Inputs (F p2)) : CostIs (main b) ⟨62, 62⟩ := by
  unfold main
  have hcount : (⟨31, 0⟩ + (⟨31, 0⟩ + (⟨31 * 0, 31 * 1⟩ + (⟨31 * 0, 31 * 1⟩ + ⟨0, 0⟩))) : Count)
      = ⟨62, 62⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 31 _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector 31 _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub (b : Var Inputs (F p2)) : CostIs (subcircuit circuit b) ⟨62, 62⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

section
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

/-- Ordered identity-C: row `t` of the adder at offset `n` pins variable `n+t`:
the 31 product rows pin the 31 products `d₀..d₃₀` (variables `n..n+30`), then the
31 carry rows pin the carries `c₁..c₃₁` (variables `n+31..n+61`), in order. -/
theorem isCidentity_ops (b : Var Inputs (F p2)) (hx : AffineW b.x) (hy : AffineW b.y) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 31 _ n]
  refine ⟨operationsIsCid_witnessVector 31 _ _ _, ?_⟩
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 31 _ _]
  refine ⟨operationsIsCid_witnessVector 31 _ _ _, ?_⟩
  rw [Circuit.bind_operations_eq, operationsIsCid_append,
    (CostIs.forEach fun i m => CostIs.assertZero _ m) _]
  refine ⟨?_, ?_⟩
  · -- product rows: row i pins prods[i] = var (n + i)
    rw [Circuit.forEach.operations_eq]
    refine operationsIsCid_flatten_ofFn (L := 1)
      (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
    simp only [Vector.getElem_finRange]
    simp only [Nat.mul_one]
    refine ⟨?_, trivial⟩
    rw [at31_wv, Nat.mod_eq_of_lt i.isLt]
    exact isCidentityRowAt_var_sub_mul
      (Affine.add (hx _ (Nat.mod_lt _ (by norm_num)))
        (carryE_affine (affineW_witnessVector_output 31 _ _) i.val))
      (Affine.add (hy _ (Nat.mod_lt _ (by norm_num)))
        (carryE_affine (affineW_witnessVector_output 31 _ _) i.val))
  · -- carry rows: row 31+i pins carries[i] = var (n + 31 + i)
    rw [Circuit.bind_operations_eq, operationsIsCid_append,
      (CostIs.forEach fun i m => CostIs.assertZero _ m) _]
    refine ⟨?_, operationsIsCid_pure _ _ _⟩
    rw [Circuit.forEach.operations_eq]
    refine operationsIsCid_flatten_ofFn (L := 1)
      (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
    simp only [Vector.getElem_finRange]
    simp only [Nat.mul_one]
    refine ⟨?_, trivial⟩
    rw [at31_wv, Nat.mod_eq_of_lt i.isLt]
    exact isCidentityRowAt_var_sub_mul
      (Affine.add (carryE_affine (affineW_witnessVector_output 31 _ _) i.val)
        (at31_affine (affineW_witnessVector_output 31 _ _) i.val))
      Affine.one

end

theorem isCidentity_main (b : Var Inputs (F p2)) (hx : AffineW b.x) (hy : AffineW b.y) :
    IsCidCirc (main b) :=
  IsCidCirc.of_ops (isCidentity_ops b hx hy)

theorem isCidentity_sub (b : Var Inputs (F p2)) (hx : AffineW b.x) (hy : AffineW b.y) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_ops b hx hy)

/-- The canonical adder is balanced: 62 constraints = 62 allocations. -/
theorem balanced_sub (b : Var Inputs (F p2)) : Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end
end Solution.SHA256CompressGF2.Add32Canon

namespace Solution.SHA256CompressGF2
section

/-- Entry `i` of a freshly witnessed `n`-vector output is the single var `w+i`. -/
theorem wv_getElem {n : ℕ} (c : ProverEnvironment (F p2) → Vector (F p2) n) (w i : ℕ)
    (h : i < n) :
    ((Circuit.witnessVector n c).output w)[i]'h = Expression.var ⟨w + i⟩ := by
  rw [show (Circuit.witnessVector n c).output w = varFromOffset (fields n) w from rfl]
  simp only [varFromOffset, instProvableTypeFields, size, Vector.getElem_mapRange]

theorem zxorOut_affine {v : Var (fields 96) (F p2)} {p : Var (fields 32) (F p2)}
    (hv : AffineW v) (hp : AffineW p) : AffineW (zxorOut v p) := by
  intro j hj
  unfold zxorOut
  rw [Vector.getElem_ofFn]
  exact Affine.add (a96_affine hv _) (hp _ hj)

end
end Solution.SHA256CompressGF2

namespace Solution.SHA256CompressGF2.Ch32Canon
section

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

section
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

theorem isCidentity_ops (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 32 _ n]
  refine ⟨operationsIsCid_witnessVector 32 _ _ _, ?_⟩
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
  exact isCidentityRowAt_var_sub_mul (a96_affine hb _)
    (Affine.add (a96_affine hb _) (a96_affine hb _))

end

theorem isCidentity_main (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    IsCidCirc (main b) :=
  IsCidCirc.of_ops (isCidentity_ops b hb)

theorem isCidentity_sub (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_ops b hb)

theorem balanced_sub (b : Var (fields 96) (F p2)) : Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end
end Solution.SHA256CompressGF2.Ch32Canon

namespace Solution.SHA256CompressGF2
section

/-- `Ch32Canon`'s output `zxorOut` is affine given affine input. -/
theorem affineW_subOut_ch32canon (v : Var (fields 96) (F p2)) (hv : AffineW v) (n : ℕ) :
    AffineW ((subcircuit Ch32Canon.circuit v).output n) := by
  simp only [circuit_norm, subcircuit, Ch32Canon.circuit, Ch32Canon.elaborated]
  exact zxorOut_affine hv (affineW_mapRange_var _)

end
end Solution.SHA256CompressGF2

namespace Solution.SHA256CompressGF2.Maj32Canon
section

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

section
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

theorem isCidentity_ops (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 32 _ n]
  refine ⟨operationsIsCid_witnessVector 32 _ _ _, ?_⟩
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
  exact isCidentityRowAt_var_sub_mul
    (Affine.add (a96_affine hb _) (a96_affine hb _))
    (Affine.add (a96_affine hb _) (a96_affine hb _))

end

theorem isCidentity_main (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    IsCidCirc (main b) :=
  IsCidCirc.of_ops (isCidentity_ops b hb)

theorem isCidentity_sub (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_ops b hb)

theorem balanced_sub (b : Var (fields 96) (F p2)) : Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end
end Solution.SHA256CompressGF2.Maj32Canon

namespace Solution.SHA256CompressGF2
section

theorem affineW_subOut_maj32canon (v : Var (fields 96) (F p2)) (hv : AffineW v) (n : ℕ) :
    AffineW ((subcircuit Maj32Canon.circuit v).output n) := by
  simp only [circuit_norm, subcircuit, Maj32Canon.circuit, Maj32Canon.elaborated]
  exact zxorOut_affine hv (affineW_mapRange_var _)

end
end Solution.SHA256CompressGF2

namespace Solution.SHA256CompressGF2.Pin32Canon
section

section
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

/-- Canonical pin rows `wᵢ − (vᵢ)·1`, pinned in allocation order. -/
theorem isCidentity_ops (b : Var (fields 32) (F p2)) (hb : AffineW b) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 32 _ n]
  refine ⟨operationsIsCid_witnessVector 32 _ _ _, ?_⟩
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
  exact isCidentityRowAt_var_sub_mul (b32_affine hb _) Affine.one

end

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

theorem isCidentity_main (b : Var (fields 32) (F p2)) (hb : AffineW b) :
    IsCidCirc (main b) :=
  IsCidCirc.of_ops (isCidentity_ops b hb)

theorem isCidentity_sub (b : Var (fields 32) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_ops b hb)

theorem balanced_sub (b : Var (fields 32) (F p2)) : Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end
end Solution.SHA256CompressGF2.Pin32Canon

namespace Solution.SHA256CompressGF2
section

/-- `Add32Canon`'s output entries are affine given affine inputs. -/
theorem affineW_subOut_add32canon (b : Var Add32.Inputs (F p2))
    (hx : AffineW b.x) (hy : AffineW b.y) (n : ℕ) :
    AffineW ((subcircuit Add32Canon.circuit b).output n) := by
  intro j hj
  simp only [circuit_norm, subcircuit, Add32Canon.circuit, Add32Canon.elaborated,
    Vector.getElem_ofFn]
  refine Affine.add (Affine.add (hx _ (Nat.mod_lt _ (by norm_num)))
    (hy _ (Nat.mod_lt _ (by norm_num)))) ?_
  unfold Add32.carryE
  split
  · exact Affine.zero
  · exact affineW_mapRange_var _ _ (Nat.mod_lt _ (by norm_num))

theorem add32canon_cid (x y : Var (fields 32) (F p2)) (hx : AffineW x) (hy : AffineW y) :
    IsCidCirc (subcircuit Add32Canon.circuit ⟨x, y⟩) :=
  Add32Canon.isCidentity_sub ⟨x, y⟩ hx hy

theorem affineW_out_add32canon (x y : Var (fields 32) (F p2))
    (hx : AffineW x) (hy : AffineW y) (n : ℕ) :
    AffineW ((subcircuit Add32Canon.circuit (⟨x, y⟩ : Var Add32.Inputs (F p2))).output n) :=
  affineW_subOut_add32canon ⟨x, y⟩ hx hy n

end
end Solution.SHA256CompressGF2

namespace Solution.SHA256CompressGF2.ScheduleStepCanon
section

/-- 3 canonical adders + one pin: `⟨218, 218⟩`. -/
theorem costIs_main (b : Var (fields 128) (F p2)) : CostIs (main b) ⟨218, 218⟩ :=
  fun n => (CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Pin32Canon.costIs_sub _) fun _ =>
    CostIs.pure _ : CostIs (main b) (⟨62, 62⟩ + (⟨62, 62⟩ + (⟨62, 62⟩ + (⟨32, 32⟩ + ⟨0, 0⟩))))) n

theorem costIs_sub (b : Var (fields 128) (F p2)) : CostIs (subcircuit circuit b) ⟨218, 218⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

theorem isCidentity_main (b : Var (fields 128) (F p2)) (hb : AffineW b) :
    IsCidCirc (main b) := by
  have h1 : AffineW (lowerSigma1E (w128 b 3)) := lowerSigma1E_affine (w128_affine hb 3)
  have h0 : AffineW (lowerSigma0E (w128 b 1)) := lowerSigma0E_affine (w128_affine hb 1)
  have hw2 : AffineW (w128 b 2) := w128_affine hb 2
  have hw0 : AffineW (w128 b 0) := w128_affine hb 0
  unfold main
  refine IsCidCirc.bind_out (add32canon_cid _ _ h1 hw2) (Add32Canon.balanced_sub _) fun n1 => ?_
  refine IsCidCirc.bind_out (add32canon_cid _ _ h0 hw0) (Add32Canon.balanced_sub _) fun n2 => ?_
  refine IsCidCirc.bind_out
    (add32canon_cid _ _ (affineW_out_add32canon _ _ h1 hw2 n1)
      (affineW_out_add32canon _ _ h0 hw0 n2)) (Add32Canon.balanced_sub _) fun n3 => ?_
  refine IsCidCirc.bind
    (Pin32Canon.isCidentity_sub _
      (affineW_out_add32canon _ _ (affineW_out_add32canon _ _ h1 hw2 n1)
        (affineW_out_add32canon _ _ h0 hw0 n2) n3)) (Pin32Canon.balanced_sub _) fun _ => ?_
  exact IsCidCirc.pure _

theorem isCidentity_sub (b : Var (fields 128) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_main b hb).ops

theorem balanced_sub (b : Var (fields 128) (F p2)) : Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end
end Solution.SHA256CompressGF2.ScheduleStepCanon

namespace Solution.SHA256CompressGF2.RoundCanon
section

/-- 7 canonical adders + canonical Ch + Maj + 2 pins: `⟨562, 562⟩`. -/
theorem costIs_main (k : ℕ) (b : Var (fields 288) (F p2)) : CostIs (main k b) ⟨562, 562⟩ :=
  fun n => (CostIs.bind (Ch32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Maj32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Pin32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Pin32Canon.costIs_sub _) fun _ =>
    CostIs.pure _
      : CostIs (main k b) (⟨32,32⟩ + (⟨32,32⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨62,62⟩
          + (⟨62,62⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨32,32⟩ + (⟨32,32⟩ + ⟨0,0⟩)))))))))))) n

theorem costIs_sub (k : ℕ) (b : Var (fields 288) (F p2)) :
    CostIs (subcircuit (circuit k) b) ⟨562, 562⟩ :=
  CostIs.subcircuit (fun n => costIs_main k b n)

theorem isCidentity_main (k : ℕ) (b : Var (fields 288) (F p2)) (hb : AffineW b) :
    IsCidCirc (main k b) := by
  have hS1 : AffineW (upperSigma1E (w288 b 4)) := upperSigma1E_affine (w288_affine hb 4)
  have hS0 : AffineW (upperSigma0E (w288 b 0)) := upperSigma0E_affine (w288_affine hb 0)
  have hcK : AffineW (constW k) := constW_affine k
  have hcv : AffineW (c96 (w288 b 4) (w288 b 5) (w288 b 6)) :=
    c96_affine (w288_affine hb 4) (w288_affine hb 5) (w288_affine hb 6)
  have hmv : AffineW (c96 (w288 b 0) (w288 b 1) (w288 b 2)) :=
    c96_affine (w288_affine hb 0) (w288_affine hb 1) (w288_affine hb 2)
  unfold main
  refine IsCidCirc.bind_out (Ch32Canon.isCidentity_sub _ hcv)
    (Ch32Canon.balanced_sub _) fun nc => ?_
  refine IsCidCirc.bind_out (Maj32Canon.isCidentity_sub _ hmv)
    (Maj32Canon.balanced_sub _) fun nm => ?_
  have hch : AffineW ((subcircuit Ch32Canon.circuit
      (c96 (w288 b 4) (w288 b 5) (w288 b 6))).output nc) := affineW_subOut_ch32canon _ hcv _
  have hmj : AffineW ((subcircuit Maj32Canon.circuit
      (c96 (w288 b 0) (w288 b 1) (w288 b 2))).output nm) := affineW_subOut_maj32canon _ hmv _
  refine IsCidCirc.bind_out (add32canon_cid _ _ (w288_affine hb 7) hS1)
    (Add32Canon.balanced_sub _) fun n1 => ?_
  have ha1 := affineW_out_add32canon _ _ (w288_affine hb 7) hS1 n1
  refine IsCidCirc.bind_out (add32canon_cid _ _ ha1 hch)
    (Add32Canon.balanced_sub _) fun n2 => ?_
  have ha2 := affineW_out_add32canon _ _ ha1 hch n2
  refine IsCidCirc.bind_out (add32canon_cid _ _ ha2 hcK)
    (Add32Canon.balanced_sub _) fun n3 => ?_
  have ha3 := affineW_out_add32canon _ _ ha2 hcK n3
  refine IsCidCirc.bind_out (add32canon_cid _ _ ha3 (w288_affine hb 8))
    (Add32Canon.balanced_sub _) fun n4 => ?_
  have ht1 := affineW_out_add32canon _ _ ha3 (w288_affine hb 8) n4
  refine IsCidCirc.bind_out (add32canon_cid _ _ hS0 hmj)
    (Add32Canon.balanced_sub _) fun n5 => ?_
  have ht2 := affineW_out_add32canon _ _ hS0 hmj n5
  refine IsCidCirc.bind_out (add32canon_cid _ _ (w288_affine hb 3) ht1)
    (Add32Canon.balanced_sub _) fun n6 => ?_
  have hen := affineW_out_add32canon _ _ (w288_affine hb 3) ht1 n6
  refine IsCidCirc.bind_out (add32canon_cid _ _ ht1 ht2)
    (Add32Canon.balanced_sub _) fun n7 => ?_
  have han := affineW_out_add32canon _ _ ht1 ht2 n7
  refine IsCidCirc.bind_out (Pin32Canon.isCidentity_sub _ han)
    (Pin32Canon.balanced_sub _) fun n8 => ?_
  refine IsCidCirc.bind (Pin32Canon.isCidentity_sub _ hen)
    (Pin32Canon.balanced_sub _) fun _ => ?_
  exact IsCidCirc.pure _

theorem isCidentity_sub (k : ℕ) (b : Var (fields 288) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit (circuit k) b) :=
  IsCidCirc.subcircuit (isCidentity_main k b hb).ops

theorem balanced_sub (k : ℕ) (b : Var (fields 288) (F p2)) :
    Balanced (subcircuit (circuit k) b) :=
  Balanced.of_costIs (costIs_sub k b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

theorem affineW_subOut (k : ℕ) (b : Var (fields 288) (F p2)) (hb : AffineW b) (n : ℕ) :
    AffineW ((subcircuit (circuit k) b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact outState_affine (affineW_mapRange_var _) (affineW_mapRange_var _) hb

end
end Solution.SHA256CompressGF2.RoundCanon

namespace Solution.SHA256CompressGF2.Pin256Canon
section

section
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid

/-- Canonical pin rows `wᵢ − (vᵢ)·1`, pinned in allocation order. -/
theorem isCidentity_ops (b : Var (fields 256) (F p2)) (hb : AffineW b) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 256 _ n]
  refine ⟨operationsIsCid_witnessVector 256 _ _ _, ?_⟩
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
  exact isCidentityRowAt_var_sub_mul (b256_affine hb _) Affine.one

end

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

theorem isCidentity_main (b : Var (fields 256) (F p2)) (hb : AffineW b) :
    IsCidCirc (main b) :=
  IsCidCirc.of_ops (isCidentity_ops b hb)

theorem isCidentity_sub (b : Var (fields 256) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_ops b hb)

theorem balanced_sub (b : Var (fields 256) (F p2)) : Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

end
end Solution.SHA256CompressGF2.Pin256Canon

namespace Solution.SHA256CompressGF2
section

/-- `ScheduleStepCanon`'s output is a `Pin32` witness vector, hence affine. -/
theorem affineW_subOut_schedcanon (b : Var (fields 128) (F p2)) (n : ℕ) :
    AffineW ((subcircuit ScheduleStepCanon.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, ScheduleStepCanon.circuit, ScheduleStepCanon.elaborated]
  exact affineW_mapRange_var _

end
end Solution.SHA256CompressGF2

namespace Solution.SHA256CompressGF2.Sched16Canon
section

theorem costIs_main (b : Var (fields 512) (F p2)) : CostIs (main b) ⟨3488, 3488⟩ := by
  unfold main
  exact CostIs.bind (CostIs.foldlRange (constant := constantLength)
      fun _ _ n => (CostIs.bind (ScheduleStepCanon.costIs_sub _) fun _ => CostIs.pure _) n)
    fun _ => CostIs.pure _

theorem costIs_sub (b : Var (fields 512) (F p2)) : CostIs (subcircuit circuit b) ⟨3488, 3488⟩ :=
  CostIs.subcircuit (fun n => costIs_main b n)

theorem isCidentity_main (b : Var (fields 512) (F p2)) (hb : AffineW b) :
    IsCidCirc (main b) := by
  rw [main]
  apply IsCidCirc.bind_out
  · refine IsCidCirc.foldlRange_inv (constant := constantLength) (L := 218)
      (fun w => ∀ k (hk : k < 32), AffineW (w[k]'hk)) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      show AffineW (((Vector.ofFn fun j : Fin 16 => q512 b j.val) ++
        Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))[k]'hk)
      rw [Vector.getElem_append]
      split
      · rw [Vector.getElem_ofFn]; exact q512_affine hb _
      · rw [Vector.getElem_replicate]; intro j hj; rw [Vector.getElem_replicate]; exact Affine.zero
    · intro i
      simp [circuit_norm, ScheduleStepCanon.circuit, ScheduleStepCanon.elaborated]
    · intro w i n hw
      exact (CostIs.bind (ScheduleStepCanon.costIs_sub _) fun _ => CostIs.pure _).constraints n
    · intro w i hw
      exact IsCidCirc.bind_out (ScheduleStepCanon.isCidentity_sub _
        (c128_affine (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega))))
        (ScheduleStepCanon.balanced_sub _)
        (fun _ => IsCidCirc.pure _)
    · intro w i n hw k hk
      simp only [circuit_norm, Vector.getElem_set]
      split
      · exact affineW_varFromOffset _ _
      · exact hw _ _
  · exact fun n =>
      Balanced.of_costIs (CostIs.foldlRange (constant := constantLength)
        fun _ _ n' => (CostIs.bind (ScheduleStepCanon.costIs_sub _) fun _ => CostIs.pure _) n')
        (fun n' => by
          simp [circuit_norm, ScheduleStepCanon.circuit, ScheduleStepCanon.elaborated,
            Count.zero]) n
  · exact fun n => IsCidCirc.pure _

theorem isCidentity_sub (b : Var (fields 512) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_main b hb).ops

theorem balanced_sub (b : Var (fields 512) (F p2)) : Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

/-- The chunk's output words are `ScheduleStepCanon` outputs, hence affine. -/
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

end
end Solution.SHA256CompressGF2.Sched16Canon

namespace Solution.SHA256CompressGF2
section

theorem round_out_affine_canon (k : ℕ) {b : Var (fields 288) (F p2)} (hb : AffineW b) (n : ℕ) :
    AffineW ((subcircuit (RoundCanon.circuit k) b).output n) :=
  RoundCanon.affineW_subOut k b hb n

end
end Solution.SHA256CompressGF2

namespace Solution.SHA256CompressGF2.Rounds16Canon
section

theorem costIs_main (r0 : ℕ) (b : Var (fields 768) (F p2)) : CostIs (main r0 b) ⟨9248, 9248⟩ :=
  CostIs.bind (CostIs.foldlRange (constant := constantLength r0 b) fun _ _ n => RoundCanon.costIs_sub _ _ n) fun _ =>
    Pin256Canon.costIs_sub _

theorem costIs_sub (r0 : ℕ) (b : Var (fields 768) (F p2)) :
    CostIs (subcircuit (circuit r0) b) ⟨9248, 9248⟩ :=
  CostIs.subcircuit (fun n => costIs_main r0 b n)

/-- The 16-round fold's output is a witnessed round state, hence affine. -/
theorem affineW_rounds_foldOut (r0 : ℕ) (b : Var (fields 768) (F p2)) (hb : AffineW b) (n : ℕ) :
    AffineW ((Circuit.foldlRange 16 (st768 b) (fun s i =>
      RoundCanon.circuit (kAt (r0 + i.val)) (c288s s (q768 b (8 + i.val)))) (constantLength r0 b)).output n) := by
  rw [Circuit.foldlRange.output_eq]
  refine finFoldl_invariant (fun s => AffineW s) _ _ (st768_affine hb) ?_
  intro acc i hacc
  exact round_out_affine_canon _ (c288s_affine hacc (q768_affine hb (8 + i.val))) _

theorem isCidentity_main (r0 : ℕ) (b : Var (fields 768) (F p2)) (hb : AffineW b) :
    IsCidCirc (main r0 b) := by
  rw [main]
  apply IsCidCirc.bind_out
  · refine IsCidCirc.foldlRange_inv (L := 562) (fun s => AffineW s) (st768_affine hb)
      ?_ ?_ ?_ ?_
    · intro i
      simp [circuit_norm, RoundCanon.circuit, RoundCanon.elaborated]
    · intro s i n hs
      exact (RoundCanon.costIs_sub _ _).constraints n
    · exact fun s i hs => RoundCanon.isCidentity_sub _ _ (c288s_affine hs (q768_affine hb (8 + i.val)))
    · exact fun s i n hs => round_out_affine_canon _ (c288s_affine hs (q768_affine hb (8 + i.val))) _
  · exact fun n =>
      Balanced.of_costIs (CostIs.foldlRange (constant := constantLength r0 b)
        fun _ _ n' => RoundCanon.costIs_sub _ _ n')
        (fun n' => by simp [circuit_norm, RoundCanon.circuit, RoundCanon.elaborated]) n
  · exact fun n => Pin256Canon.isCidentity_sub _ (affineW_rounds_foldOut r0 b hb n)

theorem isCidentity_sub (r0 : ℕ) (b : Var (fields 768) (F p2)) (hb : AffineW b) :
    IsCidCirc (subcircuit (circuit r0) b) :=
  IsCidCirc.subcircuit (isCidentity_main r0 b hb).ops

theorem balanced_sub (r0 : ℕ) (b : Var (fields 768) (F p2)) :
    Balanced (subcircuit (circuit r0) b) :=
  Balanced.of_costIs (costIs_sub r0 b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]

/-- The chunk's output is a `Pin256` witness vector, hence affine. -/
theorem affineW_subOut (r0 : ℕ) (b : Var (fields 768) (F p2)) (n : ℕ) :
    AffineW ((subcircuit (circuit r0) b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

end
end Solution.SHA256CompressGF2.Rounds16Canon

namespace Solution.SHA256CompressGF2Canonical

theorem out256_add32canon_affine {input : Var Input (F p2)} (hh : AffineW input.h)
    {s4 : Var (fields 256) (F p2)} (hs4 : AffineW s4)
    (e0 e1 e2 e3 e4 e5 e6 e7 : ℕ) :
    AffineW (out256
      ((subcircuit Add32Canon.circuit ⟨w256 input.h 0, w256 s4 0⟩).output e0)
      ((subcircuit Add32Canon.circuit ⟨w256 input.h 1, w256 s4 1⟩).output e1)
      ((subcircuit Add32Canon.circuit ⟨w256 input.h 2, w256 s4 2⟩).output e2)
      ((subcircuit Add32Canon.circuit ⟨w256 input.h 3, w256 s4 3⟩).output e3)
      ((subcircuit Add32Canon.circuit ⟨w256 input.h 4, w256 s4 4⟩).output e4)
      ((subcircuit Add32Canon.circuit ⟨w256 input.h 5, w256 s4 5⟩).output e5)
      ((subcircuit Add32Canon.circuit ⟨w256 input.h 6, w256 s4 6⟩).output e6)
      ((subcircuit Add32Canon.circuit ⟨w256 input.h 7, w256 s4 7⟩).output e7)) :=
  out256_affine
    (affineW_subOut_add32canon ⟨w256 input.h 0, w256 s4 0⟩ (w256_affine hh 0) (w256_affine hs4 0) e0)
    (affineW_subOut_add32canon ⟨w256 input.h 1, w256 s4 1⟩ (w256_affine hh 1) (w256_affine hs4 1) e1)
    (affineW_subOut_add32canon ⟨w256 input.h 2, w256 s4 2⟩ (w256_affine hh 2) (w256_affine hs4 2) e2)
    (affineW_subOut_add32canon ⟨w256 input.h 3, w256 s4 3⟩ (w256_affine hh 3) (w256_affine hs4 3) e3)
    (affineW_subOut_add32canon ⟨w256 input.h 4, w256 s4 4⟩ (w256_affine hh 4) (w256_affine hs4 4) e4)
    (affineW_subOut_add32canon ⟨w256 input.h 5, w256 s4 5⟩ (w256_affine hh 5) (w256_affine hs4 5) e5)
    (affineW_subOut_add32canon ⟨w256 input.h 6, w256 s4 6⟩ (w256_affine hh 6) (w256_affine hs4 6) e6)
    (affineW_subOut_add32canon ⟨w256 input.h 7, w256 s4 7⟩ (w256_affine hh 7) (w256_affine hs4 7) e7)

end Solution.SHA256CompressGF2Canonical
