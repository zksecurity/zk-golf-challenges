import Solution.SHA256CompressGF2.Add32
import Clean.Utils.Bits

/-!
# Word bridges: GF(2) bit vectors ↔ `ℕ` bitwise operations

The soundness layer: `toNat` of an `F 2` bit vector characterized via
`Nat.testBit` (through `Utils.Bits.fromBits`), per-bit `decide` identities for
`+`/`*` vs `^^^`/`&&&`, and the `rotRight32` bit map.
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

/-! ## Per-bit facts on `F 2` (all by `decide`) -/

theorem val_le_one : ∀ a : F p2, ZMod.val a ≤ 1 := by decide

theorem val_add_eq_xor : ∀ a b : F p2,
    ZMod.val (a + b) = ZMod.val a ^^^ ZMod.val b := by decide

theorem val_mul_eq_and : ∀ a b : F p2,
    ZMod.val (a * b) = ZMod.val a &&& ZMod.val b := by decide

/-! ## `toNat` as `fromBits`, and its `testBit` characterization -/

/-- Additive `Fin.foldl` is a sum. -/
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

/-- `toNat` is `fromBits` of the bit values. -/
theorem toNat_eq_fromBits (v : Vector (F p2) 32) :
    toNat v = Utils.Bits.fromBits (v.map ZMod.val) := by
  rw [fromBits_eq_sum]
  unfold Challenge.F2Bits.toNat Challenge.F2Bits.wordAt
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [Add32.bitAt_eq _ j.val j.isLt, Vector.getElem_map]
  rfl

/-- The bit values of `v` are boolean. -/
theorem bits_bool (v : Vector (F p2) 32) :
    ∀ (i : ℕ) (hi : i < 32), (v.map ZMod.val)[i] = 0 ∨ (v.map ZMod.val)[i] = 1 := by
  intro i hi
  rw [Vector.getElem_map]
  have := val_le_one (v[i]'hi)
  omega

/-- `toNat` is bounded. -/
theorem toNat_lt (v : Vector (F p2) 32) : toNat v < 2 ^ 32 := by
  rw [toNat_eq_fromBits]
  exact Utils.Bits.fromBits_lt _ (bits_bool v)

/-- Bit `i < 32` of `toNat v`, in rewrite-friendly form. -/
theorem val_eq_testBit (v : Vector (F p2) 32) (i : ℕ) (hi : i < 32) :
    ZMod.val (v[i]'hi) = (if (toNat v).testBit i then 1 else 0) := by
  have h := Utils.Bits.toBits_fromBits (v.map ZMod.val) (bits_bool v)
  have h2 := congrArg (fun w => w[i]'hi) h
  simp only [Utils.Bits.toBits, Vector.getElem_mapRange, Vector.getElem_map] at h2
  rw [← toNat_eq_fromBits] at h2
  omega

/-- Bits at or above 32 are clear. -/
theorem testBit_toNat_ge (v : Vector (F p2) 32) (i : ℕ) (hi : 32 ≤ i) :
    (toNat v).testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (toNat_lt v) (Nat.pow_le_pow_right (by norm_num) hi))

/-- Boolean form: bit `i < 32` of `toNat v` is whether `v[i] = 1`. -/
theorem testBit_toNat (v : Vector (F p2) 32) (i : ℕ) (hi : i < 32) :
    (toNat v).testBit i = decide (ZMod.val (v[i]'hi) = 1) := by
  have := val_eq_testBit v i hi
  rcases Bool.eq_false_or_eq_true ((toNat v).testBit i) with h | h <;>
    · rw [h] at this ⊢
      simp_all

/-! ## `rotRight32` and shift bit maps -/

/-- Bit `i < 32` of `rotRight32 x n` (for `x < 2^32`) is bit `(i + n) % 32` of `x`. -/
theorem testBit_rotRight32 (x n i : ℕ) (hx : x < 2 ^ 32) (hi : i < 32) :
    (rotRight32 x n).testBit i = x.testBit ((i + n) % 32) := by
  unfold rotRight32
  set m := n % 32 with hm
  have hm32 : m < 32 := Nat.mod_lt _ (by norm_num)
  have hhigh : x / 2 ^ m < 2 ^ (32 - m) := by
    apply Nat.div_lt_of_lt_mul
    calc x < 2 ^ 32 := hx
    _ = 2 ^ m * 2 ^ (32 - m) := by rw [← pow_add]; congr 1; omega
  rw [show x % 2 ^ m * 2 ^ (32 - m) + x / 2 ^ m
        = 2 ^ (32 - m) * (x % 2 ^ m) + x / 2 ^ m by ring,
    Nat.testBit_two_pow_mul_add _ hhigh]
  split
  · -- i < 32 - m : reads the high part, bit (i + m) of x
    rw [Nat.testBit_div_two_pow]
    congr 1
    omega
  · -- i ≥ 32 - m : reads the low part, bit (i - (32 - m)) of x % 2^m
    rw [Nat.testBit_mod_two_pow]
    have : i - (32 - m) < m := by omega
    rw [show (i + n) % 32 = i - (32 - m) by omega]
    simp [this]

/-- Bit `i` of `x / 2^n` for `x < 2^32`: bit `i + n` of `x`. -/
theorem testBit_shr (x n i : ℕ) :
    (x / 2 ^ n).testBit i = x.testBit (i + n) :=
  Nat.testBit_div_two_pow ..

/-! ## Windowed words (`wordAt`) -/

/-- The bit values of window `k` of `v`. -/
def windowVals {N : ℕ} (v : Vector (F p2) N) (k : ℕ) (h : 32 * k + 32 ≤ N) : Vector ℕ 32 :=
  Vector.ofFn fun i : Fin 32 => ZMod.val (v[32 * k + i.val]'(by omega))

theorem windowVals_getElem {N : ℕ} (v : Vector (F p2) N) (k : ℕ) (h : 32 * k + 32 ≤ N)
    (i : ℕ) (hi : i < 32) :
    (windowVals v k h)[i] = ZMod.val (v[32 * k + i]'(by omega)) := by
  unfold windowVals
  rw [Vector.getElem_ofFn]

/-- `wordAt 32 v k` is `fromBits` of the window's bit values. -/
theorem wordAt_eq_fromBits {N : ℕ} (v : Vector (F p2) N) (k : ℕ) (h : 32 * k + 32 ≤ N) :
    wordAt 32 v k = Utils.Bits.fromBits (windowVals v k h) := by
  rw [fromBits_eq_sum]
  unfold Challenge.F2Bits.wordAt
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Add32.bitAt_eq _ (32 * k + j.val) (by omega), windowVals_getElem v k h j.val j.isLt]

theorem window_bool {N : ℕ} (v : Vector (F p2) N) (k : ℕ) (h : 32 * k + 32 ≤ N) :
    ∀ (i : ℕ) (hi : i < 32),
      (windowVals v k h)[i] = 0 ∨ (windowVals v k h)[i] = 1 := by
  intro i hi
  rw [windowVals_getElem v k h i hi]
  exact Nat.le_one_iff_eq_zero_or_eq_one.mp (val_le_one _)

theorem wordAt_lt {N : ℕ} (v : Vector (F p2) N) (k : ℕ) (h : 32 * k + 32 ≤ N) :
    wordAt 32 v k < 2 ^ 32 := by
  rw [wordAt_eq_fromBits v k h]
  exact Utils.Bits.fromBits_lt _ (window_bool v k h)

/-- Bit `i < 32` of window word `k`. -/
theorem testBit_wordAt {N : ℕ} (v : Vector (F p2) N) (k : ℕ) (h : 32 * k + 32 ≤ N)
    (i : ℕ) (hi : i < 32) :
    (wordAt 32 v k).testBit i = decide (ZMod.val (v[32 * k + i]'(by omega)) = 1) := by
  have hb := Utils.Bits.toBits_fromBits _ (window_bool v k h)
  have h2 := congrArg (fun w => w[i]'hi) hb
  simp only [Utils.Bits.toBits, Vector.getElem_mapRange] at h2
  rw [← wordAt_eq_fromBits v k h, windowVals_getElem v k h i hi] at h2
  rcases Bool.eq_false_or_eq_true ((wordAt 32 v k).testBit i) with hc | hc <;>
    · rw [hc] at h2 ⊢
      simp at h2 ⊢
      omega

theorem testBit_wordAt_ge {N : ℕ} (v : Vector (F p2) N) (k : ℕ) (h : 32 * k + 32 ≤ N)
    (i : ℕ) (hi : 32 ≤ i) :
    (wordAt 32 v k).testBit i = false :=
  Nat.testBit_lt_two_pow
    (lt_of_lt_of_le (wordAt_lt v k h) (Nat.pow_le_pow_right (by norm_num) hi))

/-- 3-way xor bit identity on `F 2`. -/
theorem xor3_bit : ∀ a b c : F p2,
    decide (ZMod.val (a + b + c) = 1)
      = ((decide (ZMod.val a = 1) ^^ decide (ZMod.val b = 1)) ^^ decide (ZMod.val c = 1)) := by
  decide

/-- `rotRight32` stays below `2^32`. -/
theorem rotRight32_lt (x n : ℕ) (hx : x < 2 ^ 32) : rotRight32 x n < 2 ^ 32 := by
  unfold rotRight32
  set m := n % 32 with hm
  show x % 2 ^ m * 2 ^ (32 - m) + x / 2 ^ m < 2 ^ 32
  have hm32 : m < 32 := Nat.mod_lt _ (by norm_num)
  have hsplit : 2 ^ m * 2 ^ (32 - m) = 2 ^ 32 := by
    rw [← pow_add]; congr 1; omega
  have hmod : x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
  have hdiv : x / 2 ^ m < 2 ^ (32 - m) :=
    Nat.div_lt_of_lt_mul (by rw [hsplit]; exact hx)
  have h1 : x % 2 ^ m * 2 ^ (32 - m) + 2 ^ (32 - m) ≤ 2 ^ 32 := by
    calc x % 2 ^ m * 2 ^ (32 - m) + 2 ^ (32 - m)
        = (x % 2 ^ m + 1) * 2 ^ (32 - m) := by ring
      _ ≤ 2 ^ m * 2 ^ (32 - m) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 32 := hsplit
  omega

/-- `toNat` of an evaluated 32-bit window is `wordAt` of the packed input,
given a pointwise evaluation bridge. -/
theorem toNat_map_eval_window {N : ℕ} {env : Environment (F p2)}
    (w : Var (fields 32) (F p2)) (v : fields N (F p2)) (k : ℕ) (hk : 32 * k + 32 ≤ N)
    (hw : ∀ (j : ℕ) (hj : j < 32),
      Expression.eval env (w[j]'hj) = v[32 * k + j]'(by omega)) :
    toNat (Vector.map (Expression.eval env) w) = wordAt 32 v k := by
  rw [toNat_eq_fromBits, wordAt_eq_fromBits v k hk]
  apply congrArg
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_map, Vector.getElem_map, windowVals_getElem v k hk j hj, hw j hj]

/-- A 32-bit window of an evaluated composite vector is `toNat` of an evaluated
32-vector whose entries evaluate equally. -/
theorem wordAt_map_eval_eq_toNat {N : ℕ} {env : Environment (F p2)}
    (v : Var (fields N) (F p2)) (w : Var (fields 32) (F p2)) (k : ℕ) (hk : 32 * k + 32 ≤ N)
    (hw : ∀ (j : ℕ) (hj : j < 32),
      Expression.eval env (v[32 * k + j]'(by omega)) = Expression.eval env (w[j]'hj)) :
    wordAt 32 (Vector.map (Expression.eval env) v) k
      = toNat (Vector.map (Expression.eval env) w) := by
  rw [toNat_eq_fromBits, wordAt_eq_fromBits (Vector.map (Expression.eval env) v) k hk]
  apply congrArg
  refine Vector.ext fun j hj => ?_
  simp only [windowVals_getElem, Vector.getElem_map]
  rw [hw j hj]

/-- A 32-bit window of an evaluated composite vector that passes through window
`l` of an already-evaluated vector. -/
theorem wordAt_map_eval_eq_wordAt {N M : ℕ} {env : Environment (F p2)}
    (v : Var (fields N) (F p2)) (input : fields M (F p2)) (k l : ℕ)
    (hk : 32 * k + 32 ≤ N) (hl : 32 * l + 32 ≤ M)
    (hw : ∀ (j : ℕ) (hj : j < 32),
      Expression.eval env (v[32 * k + j]'(by omega)) = input[32 * l + j]'(by omega)) :
    wordAt 32 (Vector.map (Expression.eval env) v) k = wordAt 32 input l := by
  rw [wordAt_eq_fromBits (Vector.map (Expression.eval env) v) k hk,
    wordAt_eq_fromBits input l hl]
  apply congrArg
  refine Vector.ext fun j hj => ?_
  simp only [windowVals_getElem, Vector.getElem_map]
  rw [hw j hj]

/-- Entry `k < n` of `toWords w n v` is `wordAt w v k`. -/
theorem toWords_getElem {N : ℕ} (w n : ℕ) (v : Vector (F p2) N) (k : ℕ) (hk : k < n) :
    (toWords w n v)[k]'hk = wordAt w v k := by
  unfold toWords
  rw [Vector.getElem_ofFn]

/-! ## Per-bit `decide` identities for Ch and Maj -/

theorem ch_bit : ∀ e f g : F p2,
    decide (ZMod.val (g + e * (f + g)) = 1)
      = ((decide (ZMod.val e = 1) && decide (ZMod.val f = 1))
          ^^ (!decide (ZMod.val e = 1) && decide (ZMod.val g = 1))) := by decide

theorem maj_bit : ∀ a b c : F p2,
    decide (ZMod.val ((a + c) * (b + c) + c) = 1)
      = (((decide (ZMod.val a = 1) && decide (ZMod.val b = 1))
          ^^ (decide (ZMod.val a = 1) && decide (ZMod.val c = 1)))
          ^^ (decide (ZMod.val b = 1) && decide (ZMod.val c = 1))) := by decide

/-- Bit `i < 32` of `not32 x` for `x < 2^32`. -/
theorem testBit_not32 (x i : ℕ) (hi : i < 32) :
    (Specs.SHA256.not32 x).testBit i = !x.testBit i := by
  unfold Specs.SHA256.not32
  rw [Nat.testBit_xor, show (0xffffffff : ℕ) = 2 ^ 32 - 1 by norm_num,
    Nat.testBit_two_pow_sub_one]
  simp [hi, Bool.xor_comm]

/-! ## Word-level Ch/Maj theorems -/

/-- Bit `i < 32` of `Ch a b c`, in variables only. -/
theorem testBit_Ch (a b c i : ℕ) (hi : i < 32) :
    (Specs.SHA256.Ch a b c).testBit i
      = ((a.testBit i && b.testBit i) ^^ (!a.testBit i && c.testBit i)) := by
  unfold Specs.SHA256.Ch
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, testBit_not32 _ i hi]

/-- Bit `i < 32` of `Maj a b c`, in variables only. -/
theorem testBit_Maj (a b c i : ℕ) (_hi : i < 32) :
    (Specs.SHA256.Maj a b c).testBit i
      = (((a.testBit i && b.testBit i) ^^ (a.testBit i && c.testBit i))
          ^^ (b.testBit i && c.testBit i)) := by
  unfold Specs.SHA256.Maj
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and]

/-- `Ch` of `< 2^32` words is `< 2^32` (bitwise, so bits ≥ 32 are clear). -/
theorem testBit_Ch_ge (a b c i : ℕ) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) (hi : 32 ≤ i) :
    (Specs.SHA256.Ch a b c).testBit i = false := by
  unfold Specs.SHA256.Ch
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi)),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi))]
  simp

theorem testBit_Maj_ge (a b c i : ℕ) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hi : 32 ≤ i) :
    (Specs.SHA256.Maj a b c).testBit i = false := by
  unfold Specs.SHA256.Maj
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi)),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))]
  simp

/-- Window words of a 96-vector at pre-normalized indices. -/
theorem testBit_w96_0 (v : Vector (F p2) 96) (i : ℕ) (hi : i < 32) :
    (wordAt 32 v 0).testBit i = decide (ZMod.val (v[i]'(by omega)) = 1) := by
  have h := testBit_wordAt v 0 (by omega) i hi
  rw [h]
  simp only [Nat.mul_zero, Nat.zero_add]

theorem testBit_w96_1 (v : Vector (F p2) 96) (i : ℕ) (hi : i < 32) :
    (wordAt 32 v 1).testBit i = decide (ZMod.val (v[32 + i]'(by omega)) = 1) := by
  have h := testBit_wordAt v 1 (by omega) i hi
  rw [h]

theorem testBit_w96_2 (v : Vector (F p2) 96) (i : ℕ) (hi : i < 32) :
    (wordAt 32 v 2).testBit i = decide (ZMod.val (v[64 + i]'(by omega)) = 1) := by
  have h := testBit_wordAt v 2 (by omega) i hi
  rw [h]

/-- If `out`'s bits are the Ch combination of `v = e ‖ f ‖ g`'s bits, then
`toNat out` is `Ch` of the packed words. -/
theorem ch_words (v : Vector (F p2) 96) (out : Vector (F p2) 32)
    (hout : ∀ (j : ℕ) (hj : j < 32),
      ZMod.val (out[j]'hj)
        = ZMod.val ((v[64 + j]'(by omega))
            + (v[j]'(by omega)) * ((v[32 + j]'(by omega)) + (v[64 + j]'(by omega))))) :
    toNat out = Specs.SHA256.Ch (wordAt 32 v 0) (wordAt 32 v 1) (wordAt 32 v 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · have h1 : (toNat out).testBit i = decide (ZMod.val (out[i]'hi) = 1) :=
      testBit_toNat out i hi
    have h2 : decide (ZMod.val (out[i]'hi) = 1)
        = decide (ZMod.val ((v[64 + i]'(by omega))
            + (v[i]'(by omega)) * ((v[32 + i]'(by omega)) + (v[64 + i]'(by omega)))) = 1) := by
      rw [hout i hi]
    have h3 := ch_bit (v[i]'(by omega)) (v[32 + i]'(by omega)) (v[64 + i]'(by omega))
    have h4 := testBit_Ch (wordAt 32 v 0) (wordAt 32 v 1) (wordAt 32 v 2) i hi
    rw [h1, h2, h3, h4, testBit_w96_0 v i hi, testBit_w96_1 v i hi, testBit_w96_2 v i hi]
  · push_neg at hi
    rw [testBit_toNat_ge out i hi,
      testBit_Ch_ge _ _ _ i (wordAt_lt v 1 (by omega)) (wordAt_lt v 2 (by omega)) hi]
/-- If `out`'s bits are the Maj combination of `v = a ‖ b ‖ c`'s bits, then
`toNat out` is `Maj` of the packed words. -/
theorem maj_words (v : Vector (F p2) 96) (out : Vector (F p2) 32)
    (hout : ∀ (j : ℕ) (hj : j < 32),
      ZMod.val (out[j]'hj)
        = ZMod.val (((v[j]'(by omega)) + (v[64 + j]'(by omega)))
            * ((v[32 + j]'(by omega)) + (v[64 + j]'(by omega)))
            + (v[64 + j]'(by omega)))) :
    toNat out = Specs.SHA256.Maj (wordAt 32 v 0) (wordAt 32 v 1) (wordAt 32 v 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · have h1 : (toNat out).testBit i = decide (ZMod.val (out[i]'hi) = 1) :=
      testBit_toNat out i hi
    have h2 : decide (ZMod.val (out[i]'hi) = 1)
        = decide (ZMod.val (((v[i]'(by omega)) + (v[64 + i]'(by omega)))
            * ((v[32 + i]'(by omega)) + (v[64 + i]'(by omega)))
            + (v[64 + i]'(by omega))) = 1) := by
      rw [hout i hi]
    have h3 := maj_bit (v[i]'(by omega)) (v[32 + i]'(by omega)) (v[64 + i]'(by omega))
    have h4 := testBit_Maj (wordAt 32 v 0) (wordAt 32 v 1) (wordAt 32 v 2) i hi
    rw [h1, h2, h3, h4, testBit_w96_0 v i hi, testBit_w96_1 v i hi, testBit_w96_2 v i hi]
  · push_neg at hi
    rw [testBit_toNat_ge out i hi,
      testBit_Maj_ge _ _ _ i (wordAt_lt v 0 (by omega)) (wordAt_lt v 1 (by omega)) hi]

/-! ## Shared total accessors (mod-trick windows) -/

/-- Plain (semireducible) total accessor into a 96-vector. -/
def a96 {α : Type} (v : Vector α 96) (k : ℕ) : α :=
  v[k % 96]'(Nat.mod_lt _ (by norm_num))

/-- Plain total accessor into a 32-vector. -/
def b32 {α : Type} (v : Vector α 32) (k : ℕ) : α :=
  v[k % 32]'(Nat.mod_lt _ (by norm_num))

/-! ## Shared wide-vector accessors -/

/-- Plain total accessor into a 512-bit vector. -/
def b512 {α : Type} (v : Vector α 512) (k : ℕ) : α :=
  v[k % 512]'(Nat.mod_lt _ (by norm_num))

/-- Plain total accessor into a 256-vector. -/
def a256 {α : Type} (v : Vector α 256) (k : ℕ) : α :=
  v[k % 256]'(Nat.mod_lt _ (by norm_num))

end Solution.SHA256CompressGF2
