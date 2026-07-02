import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.IntervalCases
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Bytes
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModTheorems

/-!
# Arithmetic bridge lemmas for the byte/bit/limb glue

This file proves the lemmas connecting the `Bytes.lean` glue (`byteFromBits`,
`packLimbs`) to the `BigInt.value` / `os2ip` semantics, for the modulus /
signature recomposition + normalization. The EM/padding lemmas are a separate
task and are not addressed here.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace BytesLemmas

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open Specs.RSASSAPKCS1v15

/-! ## Field-size facts about `circomPrime`. -/

/-- `circomPrime ≈ 2^253.5`, so `2^121 < circomPrime`. -/
theorem two_pow_121_lt_circomPrime : (2 : ℕ) ^ 121 < circomPrime := by
  unfold circomPrime; norm_num

theorem two_pow_256_lt_circomPrime : (256 : ℕ) < circomPrime := by
  unfold circomPrime; norm_num

/-! ## Generic eval-of-`Fin.foldl` distribution. -/

/-- `Expression.eval` distributes over the affine `Fin.foldl` accumulator. -/
theorem eval_foldl_add (env : Environment (F circomPrime)) (n : ℕ)
    (g : Fin n → Expression (F circomPrime)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0)
      = ∑ i : Fin n, Expression.eval env (g i) := by
  induction n with
  | zero => simp [Expression.eval]
  | succ k ih =>
    simp [Fin.foldl_succ_last, Fin.sum_univ_castSucc, Expression.eval, ih]

/-! ## Lemma 1 — `byteFromBits` value. -/

/-- Booleanity of an `Expression` bit vector under `env`. -/
def BitsBool (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) totalBits) : Prop :=
  ∀ (i : ℕ) (h : i < totalBits), (Expression.eval env (bits[i]'h)).val < 2

theorem byteFromBits_val (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) totalBits) (base : ℕ)
    (hbase : base + 8 ≤ totalBits) (hbool : BitsBool env bits) :
    (Expression.eval env (byteFromBits bits base)).val
      = ∑ t : Fin 8, (Expression.eval env (bits[base + t.val]'(by have := t.isLt; omega))).val
          * 2 ^ t.val := by
  unfold byteFromBits
  rw [eval_foldl_add]
  have hcast : (∑ i : Fin 8, Expression.eval env
        ((if h : base + (i : ℕ) < totalBits then bits[base + (i : ℕ)]'h else 0)
          * Expression.const ((2 ^ (i : ℕ) : ℕ) : F circomPrime)))
      = ((∑ t : Fin 8,
          (Expression.eval env (bits[base + t.val]'(by have := t.isLt; omega))).val
            * 2 ^ t.val : ℕ) : F circomPrime) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : base + (i : ℕ) < totalBits := by have := i.isLt; omega
    rw [dif_pos hi]
    simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [ZMod.natCast_zmod_val]
  rw [hcast, ZMod.val_natCast_of_lt]
  -- the byte value is `< 256 < circomPrime`
  calc (∑ t : Fin 8, (Expression.eval env (bits[base + t.val]'(by have := t.isLt; omega))).val
            * 2 ^ t.val)
      < 256 := by
        have := sum_lt_pow (B := 1) (n := 8)
          (fun t : Fin 8 =>
            (Expression.eval env (bits[base + t.val]'(by have := t.isLt; omega))).val)
          (by
            intro i
            have := hbool (base + i.val) (by have := i.isLt; omega)
            simpa using this)
        simpa using this
    _ ≤ circomPrime := le_of_lt two_pow_256_lt_circomPrime

/-- Generic version of `byteFromBits_val` for an arbitrary bit-vector width `n`
(used for the 256-wide digest bits). -/
theorem byteFromBits_val_gen {n : ℕ} (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) n) (base : ℕ)
    (hbase : base + 8 ≤ n)
    (hbool : ∀ (i : ℕ) (h : i < n), (Expression.eval env (bits[i]'h)).val < 2) :
    (Expression.eval env (byteFromBits bits base)).val
      = ∑ t : Fin 8, (Expression.eval env (bits[base + t.val]'(by have := t.isLt; omega))).val
          * 2 ^ t.val := by
  unfold byteFromBits
  rw [eval_foldl_add]
  have hcast : (∑ i : Fin 8, Expression.eval env
        ((if h : base + (i : ℕ) < n then bits[base + (i : ℕ)]'h else 0)
          * Expression.const ((2 ^ (i : ℕ) : ℕ) : F circomPrime)))
      = ((∑ t : Fin 8,
          (Expression.eval env (bits[base + t.val]'(by have := t.isLt; omega))).val
            * 2 ^ t.val : ℕ) : F circomPrime) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : base + (i : ℕ) < n := by have := i.isLt; omega
    rw [dif_pos hi]
    simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [ZMod.natCast_zmod_val]
  rw [hcast, ZMod.val_natCast_of_lt]
  calc (∑ t : Fin 8, (Expression.eval env (bits[base + t.val]'(by have := t.isLt; omega))).val
            * 2 ^ t.val)
      < 256 := by
        have := sum_lt_pow (B := 1) (n := 8)
          (fun t : Fin 8 =>
            (Expression.eval env (bits[base + t.val]'(by have := t.isLt; omega))).val)
          (by
            intro i
            have := hbool (base + i.val) (by have := i.isLt; omega)
            simpa using this)
        simpa using this
    _ ≤ circomPrime := le_of_lt two_pow_256_lt_circomPrime

/-! ## Lemma 2 — `packLimbs` per-limb value and bound. -/

/-- A guarded little-endian sum of `121` boolean-bounded terms is `< 2^121`. -/
theorem guarded_limb_sum_lt (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) totalBits) (hbool : BitsBool env bits)
    (k : ℕ) :
    (∑ t ∈ Finset.range 121,
        (if h : 121 * k + t < 4096 then
            (Expression.eval env (bits[121 * k + t]'(by simpa using h))).val
          else 0) * 2 ^ t) < 2 ^ 121 := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun t => (if h : 121 * k + t < 4096 then
        (Expression.eval env (bits[121 * k + t]'(by simpa using h))).val
      else 0) * 2 ^ t)]
  have := sum_lt_pow (B := 1) (n := 121)
    (fun t : Fin 121 =>
      if h : 121 * k + (t : ℕ) < 4096 then
        (Expression.eval env (bits[121 * k + (t : ℕ)]'(by simpa using h))).val
      else 0)
    (by
      intro t
      dsimp only
      by_cases h : 121 * k + (t : ℕ) < 4096
      · rw [dif_pos h]
        simpa using hbool (121 * k + (t : ℕ)) (by simpa using h)
      · rw [dif_neg h]; exact Nat.two_pow_pos 1)
  simpa using this

/-- The per-limb value: limb `k` of `packLimbs bits` evaluates to the guarded
sum of its `121` bits weighted by `2^t`. -/
theorem packLimbs_limb_val (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) totalBits) (hbool : BitsBool env bits)
    (k : Fin numLimbs) :
    (Expression.eval env ((packLimbs bits)[k.val]'k.isLt)).val
      = ∑ t ∈ Finset.range 121,
          (if h : 121 * k.val + t < 4096 then
              (Expression.eval env (bits[121 * k.val + t]'(by simpa using h))).val
            else 0) * 2 ^ t := by
  unfold packLimbs
  rw [Vector.getElem_ofFn, eval_foldl_add]
  show (∑ i : Fin 121, Expression.eval env
      ((if h : 121 * k.val + (i : ℕ) < 4096 then bits[121 * k.val + (i : ℕ)]'h else 0)
        * Expression.const ((2 ^ (i : ℕ) : ℕ) : F circomPrime))).val = _
  have hcast : (∑ i : Fin 121, Expression.eval env
        ((if h : 121 * k.val + (i : ℕ) < 4096 then bits[121 * k.val + (i : ℕ)]'h else 0)
          * Expression.const ((2 ^ (i : ℕ) : ℕ) : F circomPrime)))
      = ((∑ t ∈ Finset.range 121,
          (if h : 121 * k.val + t < 4096 then
              (Expression.eval env (bits[121 * k.val + t]'(by simpa using h))).val
            else 0) * 2 ^ t : ℕ) : F circomPrime) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i => Expression.eval env
        ((if h : 121 * k.val + i < 4096 then bits[121 * k.val + i]'h else 0)
          * Expression.const ((2 ^ i : ℕ) : F circomPrime))), Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 121 * k.val + i < 4096
    · rw [dif_pos hi, dif_pos hi]
      simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [ZMod.natCast_zmod_val]
    · rw [dif_neg hi, dif_neg hi]
      simp [Expression.eval]
  rw [hcast, ZMod.val_natCast_of_lt]
  exact lt_of_lt_of_le (guarded_limb_sum_lt env bits hbool k.val)
    (le_of_lt two_pow_121_lt_circomPrime)

/-- Each evaluated limb of `packLimbs bits` is `< 2^121 = 2^limbBits`. -/
theorem packLimbs_limb_lt (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) totalBits) (hbool : BitsBool env bits)
    (k : Fin numLimbs) :
    (Expression.eval env ((packLimbs bits)[k.val]'k.isLt)).val < 2 ^ limbBits := by
  rw [packLimbs_limb_val env bits hbool k]
  exact guarded_limb_sum_lt env bits hbool k.val

/-! ## Lemma 3 — `packLimbs` is normalized. -/

/-- The big integer `packLimbs bits` (evaluated under `env`) is `Normalized` at
limb width `limbBits = 121`. This is the form `BigInt.value_eq_sum` /
`Equal.Assumptions` consume: the limbs are `Vector.map (Expression.eval env)
(packLimbs bits)`, the evaluation of the `Var (BigInt 34)`. -/
theorem packLimbs_normalized (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) totalBits) (hbool : BitsBool env bits) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) (packLimbs bits)) := by
  intro i
  rw [Fin.getElem_fin, Vector.getElem_map]
  exact packLimbs_limb_lt env bits hbool i

/-! ## Lemma 4 — `packLimbs` value equals the flat bit-sum. -/

/-- The flat bit term, defined for all `p` (zero past the top bit). -/
def bitTerm (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) totalBits) (p : ℕ) : ℕ :=
  if h : p < totalBits then (Expression.eval env (bits[p]'h)).val * 2 ^ p else 0

/-- **Crux.** The big-integer value of `packLimbs bits` equals the flat
little-endian bit-sum `∑_{p<4096} bit[p] · 2^p`. -/
theorem packLimbs_value_eq_bitsum (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) totalBits) (hbool : BitsBool env bits) :
    BigInt.value limbBits (Vector.map (Expression.eval env) (packLimbs bits))
      = ∑ p ∈ Finset.range totalBits, bitTerm env bits p := by
  rw [Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod.value_map_eval]
  -- Step 1: substitute the per-limb value.
  have hstep1 : (∑ k : Fin numLimbs,
        (Expression.eval env (packLimbs bits)[k.val]).val * 2 ^ (limbBits * k.val))
      = ∑ k : Fin numLimbs, ∑ t ∈ Finset.range 121,
          bitTerm env bits (limbBits * k.val + t) := by
    apply Finset.sum_congr rfl
    intro k _
    have hlimb : (Expression.eval env ((packLimbs bits)[k.val]'k.isLt)).val
        = ∑ t ∈ Finset.range 121,
            (if h : 121 * k.val + t < 4096 then
                (Expression.eval env (bits[121 * k.val + t]'(by simpa using h))).val
              else 0) * 2 ^ t :=
      packLimbs_limb_val env bits hbool k
    rw [hlimb, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    show _ = bitTerm env bits (121 * k.val + t)
    unfold bitTerm
    by_cases hp : 121 * k.val + t < totalBits
    · rw [dif_pos hp, dif_pos (show 121 * k.val + t < 4096 by simpa using hp)]
      have hexp : t + limbBits * k.val = 121 * k.val + t := by
        show t + 121 * k.val = 121 * k.val + t; omega
      rw [mul_assoc, ← pow_add, hexp]
    · rw [dif_neg hp, dif_neg (show ¬ 121 * k.val + t < 4096 by simpa using hp)]
      simp
  rw [hstep1]
  -- Reindex the `(k, t)` double sum onto `range (34 * 121) = range 4114`.
  have hreindex : (∑ k : Fin numLimbs, ∑ t ∈ Finset.range 121,
        bitTerm env bits (limbBits * k.val + t))
      = ∑ p ∈ Finset.range (numLimbs * 121), bitTerm env bits p := by
    rw [Finset.sum_range
      (fun p => bitTerm env bits p)]
    rw [← (finProdFinEquiv (m := numLimbs) (n := 121)).sum_comp
      (fun q : Fin (numLimbs * 121) => bitTerm env bits q.val)]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Fin.sum_univ_eq_sum_range (fun t => bitTerm env bits (limbBits * k.val + t))]
    apply Finset.sum_congr rfl
    intro t _
    have harg : limbBits * k.val + t.val = (finProdFinEquiv (k, t)).val := by
      rw [finProdFinEquiv_apply_val]
      show 121 * k.val + t.val = t.val + 121 * k.val
      omega
    rw [harg]
  rw [hreindex]
  -- Drop the all-zero tail `[4096, 4114)`.
  have htail : numLimbs * 121 = totalBits + 18 := by
    show 34 * 121 = 4096 + 18; norm_num
  rw [htail, Finset.sum_range_add]
  have hzero : (∑ i ∈ Finset.range 18, bitTerm env bits (totalBits + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    unfold bitTerm
    rw [dif_neg (by omega)]
  rw [hzero, Nat.add_zero]

/-! ## Lemma 5 — flat bit-sum equals `os2ip`. -/

/-- Horner factoring of the `os2ip` `foldl` over a list with a nonzero seed. -/
private theorem os2ip_foldl_factor (a : ℕ) (l : List ℕ) :
    l.foldl (fun acc x => acc * 256 + x) a
      = a * 256 ^ l.length + l.foldl (fun acc x => acc * 256 + x) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, List.length_cons, pow_succ]
    rw [ih (a * 256 + h), ih (0 * 256 + h)]
    ring

/-- `os2ip` of a big-endian list as a positional sum: the `i`-th element
(`0` = most significant) carries weight `256^(length-1-i)`. -/
private theorem os2ip_list_eq_sum (l : List ℕ) :
    l.foldl (fun acc x => acc * 256 + x) 0
      = ∑ i ∈ Finset.range l.length, l[i]! * 256 ^ (l.length - 1 - i) := by
  induction l with
  | nil => simp
  | cons h t ih =>
    rw [List.foldl_cons, os2ip_foldl_factor, ih]
    simp only [List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getElem!_cons_zero, Nat.zero_add, Nat.sub_zero, Nat.add_sub_cancel,
      List.getElem!_cons_succ, Nat.zero_mul]
    rw [Nat.add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      congr 2
      omega

/-- `os2ip` of a `512`-byte big-endian vector as a positional sum with `2`-power
weights: byte `j` (`0` = MSB) carries weight `2^(8·(511-j))`. -/
private theorem os2ip_vec_eq_sum (xs : Vector ℕ 512) :
    os2ip xs = ∑ j ∈ Finset.range 512, xs[j]! * 2 ^ (8 * (511 - j)) := by
  unfold os2ip
  rw [show Vector.foldl (fun acc x => acc * 256 + x) 0 xs
        = xs.toList.foldl (fun acc x => acc * 256 + x) 0 from by
      simp only [Vector.foldl, ← Array.foldl_toList, Vector.toList]]
  rw [os2ip_list_eq_sum]
  have hlen : xs.toList.length = 512 := by simp
  rw [hlen]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hidx : xs.toList[j]! = xs[j]! := by
    rw [getElem!_pos xs.toList j (by simp [hj]), getElem!_pos xs j (by simpa using hj)]
    simp
  rw [hidx, show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul,
    show 8 * (512 - 1 - j) = 8 * (511 - j) by omega]

/-- Byte-consistency hypothesis: each big-endian byte `j` equals the affine
recomposition `∑_{t<8} bit[bitIndexOfByte j t] · 2^t` of its 8 bits. -/
def ByteConsistent (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) totalBits) : Prop :=
  ∀ (j : ℕ) (h : j < 512),
    (Expression.eval env (bytes[j]'h)).val
      = ∑ t : Fin 8, (Expression.eval env
          (bits[bitIndexOfByte j t.val]'(by
            have := t.isLt
            show 8 * (511 - j) + t.val < 4096
            omega))).val * 2 ^ t.val

/-- The flat little-endian bit-sum equals `os2ip` of the (evaluated) big-endian
byte vector, under byte-consistency. -/
theorem bitsum_eq_os2ip (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) totalBits)
    (hbyte : ByteConsistent env bytes bits) :
    (∑ p ∈ Finset.range totalBits, bitTerm env bits p)
      = os2ip (Vector.map (fun e => (Expression.eval env e).val) bytes) := by
  rw [os2ip_vec_eq_sum]
  -- Expand each byte into its 8-bit recomposition and distribute the weight.
  have hbytes : (∑ j ∈ Finset.range 512,
        (Vector.map (fun e => (Expression.eval env e).val) bytes)[j]! * 2 ^ (8 * (511 - j)))
      = ∑ j ∈ Finset.range 512, ∑ t ∈ Finset.range 8,
          bitTerm env bits (8 * (511 - j) + t) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hget : (Vector.map (fun e => (Expression.eval env e).val) bytes)[j]!
        = (Expression.eval env (bytes[j]'hj)).val := by
      rw [getElem!_pos _ j (by simpa using hj)]
      rw [Vector.getElem_map]
    rw [hget, hbyte j hj, Finset.sum_mul,
      ← Fin.sum_univ_eq_sum_range
        (fun t => bitTerm env bits (8 * (511 - j) + t))]
    apply Finset.sum_congr rfl
    intro t _
    have hp : 8 * (511 - j) + t.val < totalBits := by
      have := t.isLt
      show 8 * (511 - j) + t.val < 4096
      omega
    show (Expression.eval env (bits[bitIndexOfByte j t.val]'_)).val * 2 ^ t.val * 2 ^ (8 * (511 - j))
        = bitTerm env bits (8 * (511 - j) + t.val)
    unfold bitTerm
    rw [dif_pos hp, mul_assoc, ← pow_add]
    have hexp : t.val + 8 * (511 - j) = 8 * (511 - j) + t.val := by omega
    rw [hexp]
  rw [hbytes]
  -- Flip the big-endian outer index, then reindex `(j, t) ↦ 8 * j + t`.
  have hreflect : (∑ j ∈ Finset.range 512, ∑ t ∈ Finset.range 8,
        bitTerm env bits (8 * (511 - j) + t))
      = ∑ j ∈ Finset.range 512, ∑ t ∈ Finset.range 8, bitTerm env bits (8 * j + t) := by
    rw [← Finset.sum_range_reflect
      (fun j => ∑ t ∈ Finset.range 8, bitTerm env bits (8 * j + t)) 512]
  rw [hreflect]
  -- `(j, t) ↦ 8 * j + t` is the `finProdFinEquiv` bijection onto `range 4096`.
  have hreindex : (∑ j ∈ Finset.range 512, ∑ t ∈ Finset.range 8,
        bitTerm env bits (8 * j + t))
      = ∑ p ∈ Finset.range totalBits, bitTerm env bits p := by
    rw [show totalBits = 512 * 8 from rfl, Finset.sum_range (fun p => bitTerm env bits p),
      ← (finProdFinEquiv (m := 512) (n := 8)).sum_comp
        (fun q : Fin (512 * 8) => bitTerm env bits q.val), Fintype.sum_prod_type]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => ∑ t ∈ Finset.range 8, bitTerm env bits (8 * j + t)) 512]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Fin.sum_univ_eq_sum_range (fun t => bitTerm env bits (8 * j.val + t)) 8]
    apply Finset.sum_congr rfl
    intro t _
    have harg : 8 * j.val + t.val = (finProdFinEquiv (j, t)).val := by
      rw [finProdFinEquiv_apply_val]
      show 8 * j.val + t.val = t.val + 8 * j.val
      omega
    rw [harg]
  rw [hreindex]

/-! ## Lemma 6 — `packLimbs` value equals `os2ip` (the soundness deliverable). -/

/-- **Deliverable.** The big-integer value of `packLimbs bits` equals `os2ip`
of the evaluated big-endian byte vector. The byte vector is phrased as
`fieldBytesToNat (Vector.map (Expression.eval env) bytes)` so that, in the
soundness proof where `Vector.map (Expression.eval env) input_var.modulus =
input.modulus`, this reduces to `os2ip (fieldBytesToNat input.modulus)`. -/
theorem packLimbs_value_eq_os2ip (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) totalBits)
    (hbool : BitsBool env bits)
    (hbyte : ByteConsistent env bytes bits) :
    BigInt.value limbBits (Vector.map (Expression.eval env) (packLimbs bits))
      = os2ip (fieldBytesToNat (Vector.map (Expression.eval env) bytes)) := by
  rw [packLimbs_value_eq_bitsum env bits hbool, bitsum_eq_os2ip env bytes bits hbyte]
  congr 1
  -- `fieldBytesToNat (map (eval env) bytes) = map (fun e => (eval env e).val) bytes`
  unfold fieldBytesToNat
  rw [Vector.map_map]
  rfl

/-! ## EM (PKCS#1-v1_5 encoded message) bridge lemmas. -/

/-- The constant EM byte values are all `< 256`. -/
theorem emByteConst_lt (j : ℕ) : emByteConst j < 256 := by
  unfold emByteConst
  split_ifs with h0 h1 h2 h3 h4 h5
  · decide
  · decide
  · decide
  · decide
  · generalize hk : j - 461 = k at h5 ⊢
    interval_cases k <;> simp [derPrefix]
  · decide
  · decide

/-- Each constant EM bit value (`p ≥ 256`) is a boolean (`.val < 2`). -/
theorem emConstBit_val_lt_two (p : ℕ) (hp : 256 ≤ p) : (emConstBit p).val < 2 := by
  unfold emConstBit
  rw [if_neg (by omega)]
  simp only
  rw [ZMod.val_natCast]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by norm_num))

/-! ### Lemma 1 — `emBits` is boolean. -/

/-- Booleanity of `emBits digBits`: given the digest bits are boolean on `[0,256)`,
the full `4096`-bit EM vector is boolean (the constant prefix bits are `0`/`1`). -/
theorem emBits_bitsBool (env : Environment (F circomPrime))
    (digBits : Vector (Expression (F circomPrime)) 256)
    (hdig : ∀ (i : ℕ) (h : i < 256), (Expression.eval env (digBits[i]'h)).val < 2) :
    BitsBool env (emBits digBits) := by
  intro p hp
  unfold emBits
  rw [Vector.getElem_ofFn]
  by_cases hlt : p < 256
  · rw [dif_pos hlt]
    exact hdig p hlt
  · rw [dif_neg hlt]
    show (Expression.eval env (Expression.const (emConstBit p))).val < 2
    show (emConstBit p).val < 2
    exact emConstBit_val_lt_two p (by omega)

/-! ### Lemma 2 — the EM byte-expression vector. -/

/-- The `512`-byte EM expression vector: big-endian bytes `0..479` are the
constant EM prefix (`emByteConst`), bytes `480..511` are the digest bytes
`digBytes` (in big-endian digest order). -/
def emByteExpr (digBytes : Vector (Expression (F circomPrime)) 32) :
    Vector (Expression (F circomPrime)) 512 :=
  Vector.ofFn fun j : Fin 512 =>
    if j.val < 480 then Expression.const ((emByteConst j.val : ℕ) : F circomPrime)
    else digBytes[j.val - 480]'(by have := j.isLt; omega)

/-- Digest-consistency hypothesis (what the `ByteBlock` digest-consistency loop
provides): each big-endian digest byte `dj` equals the affine recomposition of
its 8 digest bits. -/
def DigestConsistent (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (digBits : Vector (Expression (F circomPrime)) 256) : Prop :=
  ∀ (dj : ℕ) (h : dj < 32),
    (Expression.eval env (digBytes[dj]'h)).val
      = ∑ t : Fin 8, (Expression.eval env
          (digBits[digestBitIndex dj t.val]'(by
            have := t.isLt
            show 8 * (31 - dj) + t.val < 256
            omega))).val * 2 ^ t.val

/-- For the constant region (`j < 480`), the EM bit at global index
`8 * (511 - j) + t` is `emConstBit (8 * (511 - j) + t)`, and that equals the
`2^t` bit of `emByteConst j`. -/
theorem emConstBit_digit (j t : ℕ) (hj : j < 480) (ht : t < 8) :
    emConstBit (8 * (511 - j) + t) = ((emByteConst j / 2 ^ t % 2 : ℕ) : F circomPrime) := by
  unfold emConstBit
  rw [if_neg (by omega)]
  simp only
  have h1 : (8 * (511 - j) + t) / 8 = 511 - j := by omega
  have h2 : (8 * (511 - j) + t) % 8 = t := by omega
  rw [h1, h2, show 511 - (511 - j) = j by omega]

/-- Little-endian binary decomposition: for `x < 2^m`, summing its low `m` bits
weighted by `2^t` recovers `x`. -/
theorem sum_bits_eq (x : ℕ) : ∀ m : ℕ, x < 2 ^ m →
    (∑ t ∈ Finset.range m, (x / 2 ^ t % 2) * 2 ^ t) = x := by
  intro m
  induction m generalizing x with
  | zero => intro h; simp at h ⊢; omega
  | succ k ih =>
    intro h
    rw [Finset.sum_range_succ']
    have hhalf : x / 2 < 2 ^ k := by
      rw [pow_succ] at h; omega
    have key : (∑ t ∈ Finset.range k, (x / 2 ^ (t + 1) % 2) * 2 ^ (t + 1))
        = 2 * (x / 2) := by
      rw [← ih (x / 2) hhalf, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [pow_succ, Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm (2 ^ t) 2]; ring
    rw [key]
    simp only [pow_zero, mul_one]
    omega

/-- `.val` of a nat-cast field element below `circomPrime` is the nat itself. -/
private theorem val_natCast_lt {n : ℕ} (h : n < circomPrime) :
    ((n : F circomPrime)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

/-! ### Lemma 3 — `emByteExpr` / `emBits` byte-consistency. -/

/-- **Byte-consistency of the EM construction.** Given the digest bytes are
consistent with the digest bits, the full EM byte-expression vector `emByteExpr`
is `ByteConsistent` with the full EM bit-expression vector `emBits`. -/
theorem emBits_byteConsistent (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (digBits : Vector (Expression (F circomPrime)) 256)
    (hdig : DigestConsistent env digBytes digBits) :
    ByteConsistent env (emByteExpr digBytes) (emBits digBits) := by
  intro j hj
  -- Rewrite the LHS through `emByteExpr`.
  have hbyte : (emByteExpr digBytes)[j]'hj
      = if j < 480 then Expression.const ((emByteConst j : ℕ) : F circomPrime)
        else digBytes[j - 480]'(by omega) := by
    unfold emByteExpr; rw [Vector.getElem_ofFn]
  rw [hbyte]
  -- Rewrite each EM bit `emBits[8*(511-j)+t]`.
  by_cases hcase : j < 480
  · -- Constant region.
    rw [if_pos hcase]
    -- LHS value.
    rw [show (Expression.eval env (Expression.const ((emByteConst j : ℕ) : F circomPrime)))
          = ((emByteConst j : ℕ) : F circomPrime) from rfl,
        val_natCast_lt (lt_of_lt_of_le (emByteConst_lt j)
          (le_of_lt two_pow_256_lt_circomPrime))]
    -- Turn the RHS bit-sum into the binary decomposition of `emByteConst j`.
    have hsum : (∑ t : Fin 8, (Expression.eval env
            ((emBits digBits)[bitIndexOfByte j t.val]'(by
              have := t.isLt
              show 8 * (511 - j) + t.val < 4096
              omega))).val * 2 ^ t.val)
        = ∑ t : Fin 8, (emByteConst j / 2 ^ t.val % 2) * 2 ^ t.val := by
      apply Finset.sum_congr rfl
      intro t _
      have hp : ¬ (8 * (511 - j) + t.val < 256) := by have := t.isLt; omega
      have hbit : (emBits digBits)[bitIndexOfByte j t.val]'(by
            have := t.isLt; show 8 * (511 - j) + t.val < 4096; omega)
          = Expression.const (emConstBit (8 * (511 - j) + t.val)) := by
        unfold emBits bitIndexOfByte
        rw [Vector.getElem_ofFn, dif_neg hp]
      rw [hbit]
      rw [show (Expression.eval env (Expression.const (emConstBit (8 * (511 - j) + t.val))))
            = emConstBit (8 * (511 - j) + t.val) from rfl]
      rw [emConstBit_digit j t.val hcase t.isLt,
          val_natCast_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
            (le_of_lt (lt_trans (by norm_num) two_pow_256_lt_circomPrime)))]
    rw [hsum, Fin.sum_univ_eq_sum_range
      (fun t => (emByteConst j / 2 ^ t % 2) * 2 ^ t) 8]
    exact (sum_bits_eq (emByteConst j) 8 (emByteConst_lt j)).symm
  · -- Digest region.
    rw [if_neg hcase]
    push_neg at hcase
    have hdj : j - 480 < 32 := by omega
    rw [hdig (j - 480) hdj]
    apply Finset.sum_congr rfl
    intro t _
    have hp : 8 * (511 - j) + t.val < 256 := by have := t.isLt; omega
    have hbit : (emBits digBits)[bitIndexOfByte j t.val]'(by
          have := t.isLt; show 8 * (511 - j) + t.val < 4096; omega)
        = digBits[digestBitIndex (j - 480) t.val]'(by
          have := t.isLt; show 8 * (31 - (j - 480)) + t.val < 256; omega) := by
      unfold emBits bitIndexOfByte digestBitIndex
      rw [Vector.getElem_ofFn, dif_pos hp]
      have hidx : 8 * (511 - j) + t.val = 8 * (31 - (j - 480)) + t.val := by omega
      simp only [hidx]
    rw [hbit]

/-! ### Lemma 4 — EM `packLimbs` value equals `os2ip` of the EM byte vector. -/

/-- The big-integer value of `packLimbs (emBits digBits)` equals `os2ip` of the
evaluated EM byte-expression vector. -/
theorem em_value_eq_os2ip_emByteExpr (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (digBits : Vector (Expression (F circomPrime)) 256)
    (hbool : ∀ (i : ℕ) (h : i < 256), (Expression.eval env (digBits[i]'h)).val < 2)
    (hdig : DigestConsistent env digBytes digBits) :
    BigInt.value limbBits (Vector.map (Expression.eval env) (packLimbs (emBits digBits)))
      = os2ip (Vector.map (fun e => (Expression.eval env e).val) (emByteExpr digBytes)) := by
  rw [packLimbs_value_eq_bitsum env (emBits digBits) (emBits_bitsBool env digBits hbool),
      bitsum_eq_os2ip env (emByteExpr digBytes) (emBits digBits)
        (emBits_byteConsistent env digBytes digBits hdig)]

/-! ### Lemma 5 — the evaluated EM byte vector equals the spec `EM`. -/

open Specs.RSASSAPKCS1v15.HashAlgorithm in
/-- The SHA-256 DER DigestInfo prefix in the spec equals the local `derPrefix`. -/
theorem digestInfoPrefix_sha256_eq_derPrefix :
    (Specs.RSASSAPKCS1v15.HashAlgorithm.digestInfoPrefix
      Specs.RSASSAPKCS1v15.HashAlgorithm.sha256) = derPrefix := by
  decide

/-- The spec-shaped EM byte vector for a digest `dnat : Vector ℕ 32`. -/
def emVec (dnat : Vector ℕ 32) : Vector ℕ 512 :=
  Vector.cast (by decide)
    ((#v[0x00, 0x01] : Vector ℕ 2) ++
      Vector.replicate 458 0xff ++
      (#v[0x00] : Vector ℕ 1) ++
      ((Specs.RSASSAPKCS1v15.HashAlgorithm.digestInfoPrefix
        Specs.RSASSAPKCS1v15.HashAlgorithm.sha256) ++ dnat))

/-- The constant EM byte at `j < 480` equals the corresponding entry of the
spec-shaped EM byte vector (the digest tail being irrelevant for `j < 480`). -/
theorem emVec_getElem (dnat : Vector ℕ 32) (j : ℕ) (hj : j < 512) :
    (emVec dnat)[j]'hj
      = if j < 480 then emByteConst j else dnat[j - 480]'(by omega) := by
  unfold emVec
  rw [Vector.getElem_cast]
  rw [Vector.getElem_append]
  rw [digestInfoPrefix_sha256_eq_derPrefix]
  by_cases hj480 : j < 480
  · rw [if_pos hj480]
    -- inside the `(... ++ ... ++ #v[0]) ++ (derPrefix ++ dnat)` left part (length 461)
    -- and unfold `emByteConst`.
    by_cases hlt461 : j < 461
    · rw [dif_pos hlt461]
      rw [Vector.getElem_append]
      by_cases hlt460 : j < 460
      · rw [dif_pos hlt460]
        rw [Vector.getElem_append]
        by_cases hlt2 : j < 2
        · rw [dif_pos hlt2]
          interval_cases j <;> rfl
        · rw [dif_neg hlt2, Vector.getElem_replicate]
          unfold emByteConst
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      · rw [dif_neg hlt460]
        have hje : j = 460 := by omega
        subst hje
        rfl
    · rw [dif_neg hlt461]
      simp only [Specs.RSASSAPKCS1v15.HashAlgorithm.digestInfoPrefixLength] at *
      rw [Vector.getElem_append_left (show j - (2 + 458 + 1) < 19 by omega)]
      unfold emByteConst
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (by omega), dif_pos (show j - 461 < 19 by omega)]
  · rw [if_neg hj480]
    rw [dif_neg (show ¬ j < 2 + 458 + 1 by omega)]
    simp only [Specs.RSASSAPKCS1v15.HashAlgorithm.digestInfoPrefixLength] at *
    rw [Vector.getElem_append_right (by omega) (show 19 ≤ j - (2 + 458 + 1) by omega)]
    simp only [show j - (2 + 458 + 1) - 19 = j - 480 from by omega]

/-- **Lemma 5.** The evaluated EM byte-expression vector equals the spec EM byte
vector `emVec dnat`, with `dnat` the evaluated digest bytes. -/
theorem emByteExpr_eval_eq_EM (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32) :
    Vector.map (fun e => (Expression.eval env e).val) (emByteExpr digBytes)
      = emVec (Vector.map (fun e => (Expression.eval env e).val) digBytes) := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, emVec_getElem]
  unfold emByteExpr
  rw [Vector.getElem_ofFn]
  by_cases hj480 : j < 480
  · rw [if_pos hj480, if_pos hj480]
    show (Expression.eval env (Expression.const ((emByteConst j : ℕ) : F circomPrime))).val
        = emByteConst j
    rw [show (Expression.eval env (Expression.const ((emByteConst j : ℕ) : F circomPrime)))
          = ((emByteConst j : ℕ) : F circomPrime) from rfl,
        val_natCast_lt (lt_of_lt_of_le (emByteConst_lt j)
          (le_of_lt two_pow_256_lt_circomPrime))]
  · rw [if_neg hj480, if_neg hj480, Vector.getElem_map]

/-! ### Lemma 6 — THE DELIVERABLE: `packLimbs` value equals `os2ip` of the
spec-encoded EM, and the spec encode succeeds. -/

/-- The EMSA-PKCS1-v1_5 encoding of `dnat` (under SHA-256, `emLen = 512`)
succeeds and equals `emVec dnat`, given `dnat` is an octet string. -/
theorem emsaEncode_eq_emVec (dnat : Vector ℕ 32)
    (hoct : Specs.RSASSAPKCS1v15.IsOctetString dnat) :
    Specs.RSASSAPKCS1v15.emsaPkcs1v15Encode?
      Specs.RSASSAPKCS1v15.HashAlgorithm.sha256 dnat 512 = some (emVec dnat) := by
  unfold Specs.RSASSAPKCS1v15.emsaPkcs1v15Encode?
  rw [dif_pos ⟨hoct, by decide⟩]
  rfl

/-- **DELIVERABLE (Lemma 6).** Given the evaluated digest bytes `dnat` form an
octet string, the digest bits are boolean and the digest bytes are consistent
with them, there is an EM such that the EMSA-PKCS1-v1_5 encode succeeds with that
EM and the big-integer value of `packLimbs (emBits digBits)` equals `os2ip EM`. -/
theorem h_value_eq_emsaEncode (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (digBits : Vector (Expression (F circomPrime)) 256)
    (hoct : Specs.RSASSAPKCS1v15.IsOctetString
      (Vector.map (fun e => (Expression.eval env e).val) digBytes))
    (hbool : ∀ (i : ℕ) (h : i < 256), (Expression.eval env (digBits[i]'h)).val < 2)
    (hdig : DigestConsistent env digBytes digBits) :
    ∃ EM, Specs.RSASSAPKCS1v15.emsaPkcs1v15Encode?
        Specs.RSASSAPKCS1v15.HashAlgorithm.sha256
        (Vector.map (fun e => (Expression.eval env e).val) digBytes) 512 = some EM
      ∧ BigInt.value limbBits
          (Vector.map (Expression.eval env) (packLimbs (emBits digBits)))
        = Specs.RSASSAPKCS1v15.os2ip EM := by
  set dnat := Vector.map (fun e => (Expression.eval env e).val) digBytes with hdnat
  refine ⟨emVec dnat, emsaEncode_eq_emVec dnat hoct, ?_⟩
  rw [em_value_eq_os2ip_emByteExpr env digBytes digBits hbool hdig,
      emByteExpr_eval_eq_EM env digBytes]

/-! ### Lemma 7 — EM value upper bound (`< 2^4088`). -/

/-- The top byte of EM is `0x00`, so every EM bit `p ∈ [4088, 4096)` is `0`. -/
theorem emBits_top_zero (env : Environment (F circomPrime))
    (digBits : Vector (Expression (F circomPrime)) 256) (p : ℕ)
    (hp1 : 4088 ≤ p) (hp2 : p < 4096) :
    bitTerm env (emBits digBits) p = 0 := by
  unfold bitTerm
  rw [dif_pos (by omega)]
  have hbit : (emBits digBits)[p]'(by omega)
      = Expression.const (emConstBit p) := by
    unfold emBits
    rw [Vector.getElem_ofFn, dif_neg (show ¬ p < 256 by omega)]
  rw [hbit]
  show (emConstBit p).val * 2 ^ p = 0
  have hdiv : p / 8 = 511 := by omega
  have hzero : emConstBit p = 0 := by
    unfold emConstBit
    rw [if_neg (by omega)]
    simp only
    have hj : 511 - p / 8 = 0 := by rw [hdiv]
    rw [hj]
    show ((emByteConst 0 / 2 ^ (p % 8) % 2 : ℕ) : F circomPrime) = 0
    norm_num [emByteConst]
  rw [hzero]
  simp

/-- **Lemma 7.** The big-integer value of `packLimbs (emBits digBits)` is
`< 2^4088` (hence `< 2^4095`). -/
theorem em_value_lt (env : Environment (F circomPrime))
    (digBits : Vector (Expression (F circomPrime)) 256)
    (hbool : ∀ (i : ℕ) (h : i < 256), (Expression.eval env (digBits[i]'h)).val < 2) :
    BigInt.value limbBits (Vector.map (Expression.eval env) (packLimbs (emBits digBits)))
      < 2 ^ 4088 := by
  rw [packLimbs_value_eq_bitsum env (emBits digBits) (emBits_bitsBool env digBits hbool)]
  -- Drop the all-zero top byte: `∑_{p<4096} = ∑_{p<4088}`.
  have hsplit : (∑ p ∈ Finset.range totalBits, bitTerm env (emBits digBits) p)
      = ∑ p ∈ Finset.range 4088, bitTerm env (emBits digBits) p := by
    rw [show totalBits = 4088 + 8 from rfl, Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range 8, bitTerm env (emBits digBits) (4088 + i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      exact emBits_top_zero env digBits (4088 + i) (by omega) (by omega)
    rw [hz, Nat.add_zero]
  rw [hsplit]
  -- Apply the boolean base-2 bound with `B = 1`, `n = 4088`.
  rw [← Fin.sum_univ_eq_sum_range (fun p => bitTerm env (emBits digBits) p) 4088]
  have hbnd := sum_lt_pow (B := 1) (n := 4088)
    (fun p : Fin 4088 =>
      (Expression.eval env ((emBits digBits)[p.val]'(by
        have := p.isLt; show p.val < 4096; omega))).val)
    (by
      intro p
      have := emBits_bitsBool env digBits hbool p.val (by
        have := p.isLt; show p.val < 4096; omega)
      simpa using this)
  -- Normalize `1 * 4088 → 4088` in the bound so its RHS is syntactically `2 ^ 4088`,
  -- matching the goal without forcing a kernel reduction of the literal power.
  rw [show (1 : ℕ) * 4088 = 4088 from rfl] at hbnd
  refine lt_of_le_of_lt (le_of_eq ?_) hbnd
  apply Finset.sum_congr rfl
  intro p _
  unfold bitTerm
  rw [dif_pos (by have := p.isLt; show p.val < 4096; omega), one_mul]

/-! ## OS2IP / I2OSP round-trip. -/

/-- `os2ip` as a little-endian base-256 digit sum: digit `k` is byte `511 - k`. -/
theorem os2ip_vec_eq_sum_le (xs : Vector ℕ 512) :
    os2ip xs = ∑ k ∈ Finset.range 512, xs[511 - k]! * 2 ^ (8 * k) := by
  rw [os2ip_vec_eq_sum]
  rw [← Finset.sum_range_reflect (fun j => xs[j]! * 2 ^ (8 * (511 - j))) 512]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  congr 2
  omega

/-- The base-256 digit extraction of `os2ip xs` recovers the bytes of an octet
string. -/
theorem os2ip_digit (xs : Vector ℕ 512) (hoct : IsOctetString xs) (i : ℕ) (hi : i < 512) :
    os2ip xs / 256 ^ (511 - i) % 256 = xs[i]'hi := by
  rw [os2ip_vec_eq_sum_le]
  have hf : ∀ j, (if h : 511 - j < 512 then xs[511 - j]'h else 0) < 2 ^ 8 := by
    intro j
    by_cases hj : 511 - j < 512
    · rw [dif_pos hj]; have := hoct ⟨511 - j, hj⟩; simpa using this
    · rw [dif_neg hj]; exact Nat.two_pow_pos 8
  have hsum : (∑ k ∈ Finset.range 512, xs[511 - k]! * 2 ^ (8 * k))
      = ∑ k ∈ Finset.range 512, (if h : 511 - k < 512 then xs[511 - k]'h else 0) * 2 ^ (8 * k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [dif_pos (by omega), getElem!_pos xs (511 - k) (by omega)]
  rw [hsum]
  have hext := digit_extract 8 (fun j => if h : 511 - j < 512 then xs[511 - j]'h else 0) hf 512
    (511 - i) (by omega)
  simp only at hext
  rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]
  rw [hext, dif_pos (show 511 - (511 - i) < 512 from by omega)]
  exact getElem_congr_idx (show 511 - (511 - i) = i from by omega)

/-- `i2osp` succeeds whenever the value fits in `len` octets, returning the
little-endian base-256 digit vector. `len` is kept symbolic so use sites (e.g.
`len = 512`) never force a kernel reduction of the literal power `256 ^ len`:
unfolding `i2osp` here exposes only the symbolic `256 ^ len`. -/
theorem i2osp_eq_some {x len : ℕ} {v : Vector ℕ len}
    (hlt : x < 256 ^ len)
    (hv : v = Vector.ofFn fun i : Fin len => x / 256 ^ (len - 1 - i.val) % 256) :
    i2osp x len = some v := by
  unfold i2osp
  rw [if_pos hlt, hv]

/-- Inverse of `i2osp_eq_some`: a successful `i2osp` pins both the size bound and
the digit shape of the result. `len` symbolic for the same reason. -/
theorem i2osp_some_inv {x len : ℕ} {v : Vector ℕ len} (h : i2osp x len = some v) :
    x < 256 ^ len ∧
      v = Vector.ofFn fun i : Fin len => x / 256 ^ (len - 1 - i.val) % 256 := by
  unfold i2osp at h
  by_cases hlt : x < 256 ^ len
  · rw [if_pos hlt, Option.some.injEq] at h
    exact ⟨hlt, h.symm⟩
  · rw [if_neg hlt] at h
    exact absurd h (by simp)

/-- **OS2IP / I2OSP round-trip** for octet strings of length `512`. -/
theorem os2ip_i2osp_roundtrip (xs : Vector ℕ 512) (hoct : IsOctetString xs) :
    i2osp (os2ip xs) 512 = some xs := by
  have hlt : os2ip xs < 256 ^ 512 := by
    rw [os2ip_vec_eq_sum_le]
    -- bound: each digit < 256, 512 digits ⇒ sum < 256^512
    have : (∑ k ∈ Finset.range 512, xs[511 - k]! * 2 ^ (8 * k))
        < 2 ^ (8 * 512) := by
      have hb := sum_lt_pow (B := 8) (n := 512)
        (fun k : Fin 512 => xs[511 - k.val]!)
        (by
          intro k
          show xs[511 - k.val]! < 2 ^ 8
          rw [getElem!_pos xs (511 - k.val) (by have := k.isLt; omega)]
          exact hoct ⟨511 - k.val, by have := k.isLt; omega⟩)
      rw [← Fin.sum_univ_eq_sum_range (fun k => xs[511 - k]! * 2 ^ (8 * k)) 512]
      exact hb
    rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]
    exact this
  refine i2osp_eq_some hlt ?_
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, show 512 - 1 - i = 511 - i from by omega]
  exact (os2ip_digit xs hoct i hi).symm

/-! ## `IsOctetString (emVec dnat)`. -/

/-- Every byte of `emVec dnat` is `< 256` when the digest `dnat` is an octet
string. -/
theorem isOctetString_emVec (dnat : Vector ℕ 32) (hoct : IsOctetString dnat) :
    IsOctetString (emVec dnat) := by
  intro i
  rw [Fin.getElem_fin, emVec_getElem dnat i.val i.isLt]
  by_cases hi : i.val < 480
  · rw [if_pos hi]; exact emByteConst_lt i.val
  · rw [if_neg hi]
    have hdj : i.val - 480 < 32 := by have := i.isLt; omega
    exact hoct ⟨i.val - 480, hdj⟩

end BytesLemmas
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
