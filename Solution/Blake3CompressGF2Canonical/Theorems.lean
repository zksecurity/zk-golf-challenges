import Solution.Blake3CompressGF2Canonical.Add32Canon
import Clean.Utils.Bits

/-!
# GF(2) word lemmas for the BLAKE3 reference circuit

The key bridge is that `F 2` bit vectors are uniquely represented by `toNat`.
It lets the numeric postcondition of the reusable ripple-carry adder feed the
bit-level BLAKE3 semantics in the trusted interface.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.Instances.Blake3CompressGF2Canonical.Interface.Blake3Bits
open Challenge.F2Bits
open Add32

theorem val_le_one : ∀ a : F p2, ZMod.val a ≤ 1 := by decide

theorem foldl_add_eq_sum {n : ℕ} (g : Fin n → ℕ) (a : ℕ) :
    Fin.foldl n (fun acc i => acc + g i) a = a + ∑ i, g i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ_last, ih, Fin.sum_univ_castSucc]
    ring

theorem fromBits_eq_sum {n : ℕ} (bits : Vector ℕ n) :
    Utils.Bits.fromBits bits = ∑ i : Fin n, bits[i.val] * 2 ^ i.val := by
  unfold Utils.Bits.fromBits
  rw [foldl_add_eq_sum (fun i : Fin n => bits[i.val] * 2 ^ i.val) 0, zero_add]

theorem toNat_eq_fromBits (v : Word (F p2)) :
    toNat v = Utils.Bits.fromBits (v.map ZMod.val) := by
  rw [fromBits_eq_sum]
  unfold Challenge.F2Bits.toNat Challenge.F2Bits.wordAt
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [Add32.bitAt_eq _ j.val j.isLt, Vector.getElem_map]
  rfl

theorem bits_bool (v : Word (F p2)) :
    ∀ (i : ℕ) (hi : i < 32), (v.map ZMod.val)[i] = 0 ∨ (v.map ZMod.val)[i] = 1 := by
  intro i hi
  rw [Vector.getElem_map]
  have := val_le_one (v[i]'hi)
  omega

theorem val_eq_testBit (v : Word (F p2)) (i : ℕ) (hi : i < 32) :
    ZMod.val (v[i]'hi) = (if (toNat v).testBit i then 1 else 0) := by
  have h := Utils.Bits.toBits_fromBits (v.map ZMod.val) (bits_bool v)
  have h2 := congrArg (fun w => w[i]'hi) h
  simp only [Utils.Bits.toBits, Vector.getElem_mapRange, Vector.getElem_map] at h2
  rw [← toNat_eq_fromBits] at h2
  omega

theorem toNat_injective : Function.Injective (toNat : Word (F p2) → ℕ) := by
  intro x y hxy
  refine Vector.ext fun i hi => ?_
  have hx := val_eq_testBit x i hi
  have hy := val_eq_testBit y i hi
  rw [hxy] at hx
  have hv : ZMod.val (x[i]'hi) = ZMod.val (y[i]'hi) := hx.trans hy.symm
  exact ZMod.val_injective p2 hv

theorem carry_eq (x y : Word (F p2)) (n : ℕ) :
    Blake3Bits.carry x y n = Add32.carryVal (atWord x) (atWord y) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Blake3Bits.carry, Add32.carryVal]
    rw [ih]

theorem toNat_addWord (x y : Word (F p2)) :
    toNat (addWord x y) = (toNat x + toNat y) % 2 ^ 32 := by
  rw [Add32.toNat_eq_sum, Add32.toNat_eq_sum, Add32.toNat_eq_sum]
  calc
    (∑ j ∈ Finset.range 32, bitAt (addWord x y) j * 2 ^ j)
        = ∑ j ∈ Finset.range 32,
            ZMod.val (atWord x j + atWord y j
              + Add32.carryVal (atWord x) (atWord y) j) * 2 ^ j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj32 := Finset.mem_range.mp hj
          rw [Add32.bitAt_eq _ j hj32]
          simp only [addWord, Vector.getElem_ofFn, carry_eq]
    _ = ((∑ j ∈ Finset.range 32, ZMod.val (atWord x j) * 2 ^ j)
          + ∑ j ∈ Finset.range 32, ZMod.val (atWord y j) * 2 ^ j) % 2 ^ 32 :=
      Add32.adder_correct (atWord x) (atWord y)
    _ = ((∑ j ∈ Finset.range 32, bitAt x j * 2 ^ j)
          + ∑ j ∈ Finset.range 32, bitAt y j * 2 ^ j) % 2 ^ 32 := by
      rfl

theorem eval_xorWord (env : Environment (F p2))
    (x y : Word (Expression (F p2))) :
    Vector.map (Expression.eval env) (xorWord x y) =
      xorWord (Vector.map (Expression.eval env) x) (Vector.map (Expression.eval env) y) := by
  refine Vector.ext fun i hi => ?_
  simp [xorWord, circuit_norm]

theorem eval_rotRight (env : Environment (F p2))
    (x : Word (Expression (F p2))) (n : ℕ) :
    Vector.map (Expression.eval env) (rotRight x n) =
      rotRight (Vector.map (Expression.eval env) x) n := by
  refine Vector.ext fun i hi => ?_
  simp [rotRight, atWord, circuit_norm]

theorem eval_stateWord (env : Environment (F p2))
    (v : State (Expression (F p2))) (i : Fin 16) :
    Vector.map (Expression.eval env) (stateWord v i) =
      stateWord (Vector.map (Expression.eval env) v) i := by
  refine Vector.ext fun j hj => ?_
  simp [stateWord, circuit_norm]

theorem eval_setWord (env : Environment (F p2))
    (v : State (Expression (F p2))) (i : Fin 16) (x : Word (Expression (F p2))) :
    Vector.map (Expression.eval env) (setWord v i x) =
      setWord (Vector.map (Expression.eval env) v) i
        (Vector.map (Expression.eval env) x) := by
  refine Vector.ext fun j hj => ?_
  by_cases h : j / 32 = i.val <;>
    simp [setWord, h, circuit_norm]

theorem eval_readQuad (env : Environment (F p2))
    (v : State (Expression (F p2))) (a b c d : Fin 16) :
    eval env (readQuad v a b c d) =
      readQuad (Vector.map (Expression.eval env) v) a b c d := by
  simp only [readQuad, circuit_norm, eval_stateWord]

theorem eval_writeQuad (env : Environment (F p2))
    (v : State (Expression (F p2))) (a b c d : Fin 16)
    (q : Var Quad (F p2)) :
    Vector.map (Expression.eval env) (writeQuad v a b c d q) =
      writeQuad (Vector.map (Expression.eval env) v) a b c d (eval env q) := by
  simp only [writeQuad, circuit_norm, eval_setWord]

end Solution.Blake3CompressGF2Canonical
