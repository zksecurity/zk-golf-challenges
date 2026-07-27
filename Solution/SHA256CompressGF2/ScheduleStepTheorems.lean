import Solution.SHA256CompressGF2.Ch32
import Solution.SHA256CompressGF2.Maj32
import Solution.SHA256CompressGF2.Pin32

/-!
# Composition helpers for `ScheduleStep` / `Round`

Slicing/concatenation of bit vectors as plain `ofFn` selections (the `b32`
mod-32 accessor makes windowed indexing proof-free), σ₀/σ₁/Σ₀/Σ₁ as pure affine
expression maps, and output-affinity lemmas for the gadgets.
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

/-! ## Vector builders (plain defs, mod-trick windows) -/

/-- Plain total accessor into a 128-vector. -/
def a128 {α : Type} (v : Vector α 128) (k : ℕ) : α :=
  v[k % 128]'(Nat.mod_lt _ (by norm_num))

/-- Concatenate three 32-vectors into a 96-vector (window `k` reads source bit
`i % 32 = i − 32k`). -/
def c96 (x y z : Var (fields 32) (F p2)) : Var (fields 96) (F p2) :=
  Vector.ofFn fun i : Fin 96 =>
    if i.val < 32 then b32 x i.val else if i.val < 64 then b32 y i.val else b32 z i.val

/-- Concatenate four 32-vectors into a 128-vector. -/
def c128 (x y z w : Var (fields 32) (F p2)) : Var (fields 128) (F p2) :=
  Vector.ofFn fun i : Fin 128 =>
    if i.val < 32 then b32 x i.val else if i.val < 64 then b32 y i.val
    else if i.val < 96 then b32 z i.val else b32 w i.val

/-- Window `k` (32 bits) of a 128-vector. -/
def w128 (v : Var (fields 128) (F p2)) (k : ℕ) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => a128 v (32 * k + i.val)

/-! ## σ/Σ as affine expression maps -/

/-- Rotate right by `n`: result bit `i` = source bit `(i + n) % 32`. -/
def rotrE (n : ℕ) (v : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => b32 v (i.val + n)

/-- Shift right by `n`: result bit `i` = source bit `i + n` (or `0` past 31). -/
def shrE (n : ℕ) (v : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => if i.val + n < 32 then b32 v (i.val + n) else 0

/-- 3-way XOR. -/
def xor3E (a b c : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => b32 a i.val + b32 b i.val + b32 c i.val

def lowerSigma0E (v : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  xor3E (rotrE 7 v) (rotrE 18 v) (shrE 3 v)

def lowerSigma1E (v : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  xor3E (rotrE 17 v) (rotrE 19 v) (shrE 10 v)

def upperSigma0E (v : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  xor3E (rotrE 2 v) (rotrE 13 v) (rotrE 22 v)

def upperSigma1E (v : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  xor3E (rotrE 6 v) (rotrE 11 v) (rotrE 25 v)

/-! ## `toNat` bridges for the σ/Σ maps -/

/-- Entry `i < 32` of the evaluated `rot ⊕ rot ⊕ shr` map. -/
theorem eval_sigShr_entry (env : Environment (F p2)) (v : Var (fields 32) (F p2))
    (r1 r2 s i : ℕ) (hi : i < 32) :
    (Vector.map (Expression.eval env) (xor3E (rotrE r1 v) (rotrE r2 v) (shrE s v)))[i]'hi
      = Expression.eval env (v[(i + r1) % 32]'(Nat.mod_lt _ (by norm_num)))
        + Expression.eval env (v[(i + r2) % 32]'(Nat.mod_lt _ (by norm_num)))
        + (if i + s < 32
            then Expression.eval env (v[(i + s) % 32]'(Nat.mod_lt _ (by norm_num)))
            else 0) := by
  rw [Vector.getElem_map]
  unfold xor3E rotrE shrE b32
  simp only [Vector.getElem_ofFn, Nat.mod_eq_of_lt hi]
  by_cases hs32 : i + s < 32
  · simp only [if_pos hs32, circuit_norm]
  · simp only [if_neg hs32, circuit_norm]

/-- Entry `i < 32` of the evaluated `rot ⊕ rot ⊕ rot` map. -/
theorem eval_sig3_entry (env : Environment (F p2)) (v : Var (fields 32) (F p2))
    (r1 r2 r3 i : ℕ) (hi : i < 32) :
    (Vector.map (Expression.eval env) (xor3E (rotrE r1 v) (rotrE r2 v) (rotrE r3 v)))[i]'hi
      = Expression.eval env (v[(i + r1) % 32]'(Nat.mod_lt _ (by norm_num)))
        + Expression.eval env (v[(i + r2) % 32]'(Nat.mod_lt _ (by norm_num)))
        + Expression.eval env (v[(i + r3) % 32]'(Nat.mod_lt _ (by norm_num))) := by
  rw [Vector.getElem_map]
  unfold xor3E rotrE b32
  simp only [Vector.getElem_ofFn, Nat.mod_eq_of_lt hi, circuit_norm]

/-- `toNat` of the evaluated `rot ⊕ rot ⊕ shr` map, as ℕ bit operations. -/
theorem toNat_eval_sigShr (env : Environment (F p2)) (v : Var (fields 32) (F p2))
    (r1 r2 s : ℕ) :
    toNat (Vector.map (Expression.eval env) (xor3E (rotrE r1 v) (rotrE r2 v) (shrE s v)))
      = rotRight32 (toNat (Vector.map (Expression.eval env) v)) r1
        ^^^ rotRight32 (toNat (Vector.map (Expression.eval env) v)) r2
        ^^^ toNat (Vector.map (Expression.eval env) v) / 2 ^ s := by
  have hxlt : toNat (Vector.map (Expression.eval env) v) < 2 ^ 32 := toNat_lt _
  have hb : ∀ (j : ℕ) (hj : j < 32),
      (toNat (Vector.map (Expression.eval env) v)).testBit j
        = decide (ZMod.val (Expression.eval env (v[j]'hj)) = 1) := by
    intro j hj
    have h := testBit_toNat (Vector.map (Expression.eval env) v) j hj
    rwa [Vector.getElem_map] at h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · have hL1 := testBit_toNat
      (Vector.map (Expression.eval env) (xor3E (rotrE r1 v) (rotrE r2 v) (shrE s v))) i hi
    have hL2 := eval_sigShr_entry env v r1 r2 s i hi
    have hA1 : (rotRight32 (toNat (Vector.map (Expression.eval env) v)) r1).testBit i
        = decide (ZMod.val (Expression.eval env
            (v[(i + r1) % 32]'(Nat.mod_lt _ (by norm_num)))) = 1) := by
      rw [testBit_rotRight32 _ r1 i hxlt hi, hb _ (Nat.mod_lt _ (by norm_num))]
    have hA2 : (rotRight32 (toNat (Vector.map (Expression.eval env) v)) r2).testBit i
        = decide (ZMod.val (Expression.eval env
            (v[(i + r2) % 32]'(Nat.mod_lt _ (by norm_num)))) = 1) := by
      rw [testBit_rotRight32 _ r2 i hxlt hi, hb _ (Nat.mod_lt _ (by norm_num))]
    rw [Nat.testBit_xor, Nat.testBit_xor, hA1, hA2, testBit_shr, hL1, hL2]
    by_cases hs32 : i + s < 32
    · rw [if_pos hs32, xor3_bit, hb (i + s) hs32]
      simp only [Nat.mod_eq_of_lt hs32]
    · rw [if_neg hs32, xor3_bit, testBit_toNat_ge _ (i + s) (by omega)]
      simp
  · push_neg at hi
    rw [testBit_toNat_ge _ i hi, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (rotRight32_lt _ r1 hxlt)
        (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (rotRight32_lt _ r2 hxlt)
        (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le
        (lt_of_le_of_lt (Nat.div_le_self _ _) hxlt)
        (Nat.pow_le_pow_right (by norm_num) hi))]
    rfl

/-- `toNat` of the evaluated `rot ⊕ rot ⊕ rot` map, as ℕ bit operations. -/
theorem toNat_eval_sig3 (env : Environment (F p2)) (v : Var (fields 32) (F p2))
    (r1 r2 r3 : ℕ) :
    toNat (Vector.map (Expression.eval env) (xor3E (rotrE r1 v) (rotrE r2 v) (rotrE r3 v)))
      = rotRight32 (toNat (Vector.map (Expression.eval env) v)) r1
        ^^^ rotRight32 (toNat (Vector.map (Expression.eval env) v)) r2
        ^^^ rotRight32 (toNat (Vector.map (Expression.eval env) v)) r3 := by
  have hxlt : toNat (Vector.map (Expression.eval env) v) < 2 ^ 32 := toNat_lt _
  have hb : ∀ (j : ℕ) (hj : j < 32),
      (toNat (Vector.map (Expression.eval env) v)).testBit j
        = decide (ZMod.val (Expression.eval env (v[j]'hj)) = 1) := by
    intro j hj
    have h := testBit_toNat (Vector.map (Expression.eval env) v) j hj
    rwa [Vector.getElem_map] at h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · have hL1 := testBit_toNat
      (Vector.map (Expression.eval env) (xor3E (rotrE r1 v) (rotrE r2 v) (rotrE r3 v))) i hi
    have hL2 := eval_sig3_entry env v r1 r2 r3 i hi
    have hA1 : (rotRight32 (toNat (Vector.map (Expression.eval env) v)) r1).testBit i
        = decide (ZMod.val (Expression.eval env
            (v[(i + r1) % 32]'(Nat.mod_lt _ (by norm_num)))) = 1) := by
      rw [testBit_rotRight32 _ r1 i hxlt hi, hb _ (Nat.mod_lt _ (by norm_num))]
    have hA2 : (rotRight32 (toNat (Vector.map (Expression.eval env) v)) r2).testBit i
        = decide (ZMod.val (Expression.eval env
            (v[(i + r2) % 32]'(Nat.mod_lt _ (by norm_num)))) = 1) := by
      rw [testBit_rotRight32 _ r2 i hxlt hi, hb _ (Nat.mod_lt _ (by norm_num))]
    have hA3 : (rotRight32 (toNat (Vector.map (Expression.eval env) v)) r3).testBit i
        = decide (ZMod.val (Expression.eval env
            (v[(i + r3) % 32]'(Nat.mod_lt _ (by norm_num)))) = 1) := by
      rw [testBit_rotRight32 _ r3 i hxlt hi, hb _ (Nat.mod_lt _ (by norm_num))]
    rw [Nat.testBit_xor, Nat.testBit_xor, hA1, hA2, hA3, hL1, hL2, xor3_bit]
  · push_neg at hi
    rw [testBit_toNat_ge _ i hi, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (rotRight32_lt _ r1 hxlt)
        (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (rotRight32_lt _ r2 hxlt)
        (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (rotRight32_lt _ r3 hxlt)
        (Nat.pow_le_pow_right (by norm_num) hi))]
    rfl

/-- `toNat` bridge for `lowerSigma0E`. -/
theorem toNat_eval_lowerSigma0E (env : Environment (F p2)) (v : Var (fields 32) (F p2)) :
    toNat (Vector.map (Expression.eval env) (lowerSigma0E v))
      = Specs.SHA256.lowerSigma0 (toNat (Vector.map (Expression.eval env) v)) :=
  toNat_eval_sigShr env v 7 18 3

/-- `toNat` bridge for `lowerSigma1E`. -/
theorem toNat_eval_lowerSigma1E (env : Environment (F p2)) (v : Var (fields 32) (F p2)) :
    toNat (Vector.map (Expression.eval env) (lowerSigma1E v))
      = Specs.SHA256.lowerSigma1 (toNat (Vector.map (Expression.eval env) v)) :=
  toNat_eval_sigShr env v 17 19 10

/-- `toNat` bridge for `upperSigma0E`. -/
theorem toNat_eval_upperSigma0E (env : Environment (F p2)) (v : Var (fields 32) (F p2)) :
    toNat (Vector.map (Expression.eval env) (upperSigma0E v))
      = Specs.SHA256.upperSigma0 (toNat (Vector.map (Expression.eval env) v)) :=
  toNat_eval_sig3 env v 2 13 22

/-- `toNat` bridge for `upperSigma1E`. -/
theorem toNat_eval_upperSigma1E (env : Environment (F p2)) (v : Var (fields 32) (F p2)) :
    toNat (Vector.map (Expression.eval env) (upperSigma1E v))
      = Specs.SHA256.upperSigma1 (toNat (Vector.map (Expression.eval env) v)) :=
  toNat_eval_sig3 env v 6 11 25

/-! ## `eval`-agreement congruences for the builders

Every builder below selects entries of its argument(s) and combines them
affinely, so two prover environments agreeing on the argument agree on the
result. These feed the `hinput` obligations of the `computableWitness` proofs. -/

section EvalCongr

variable {env env' : ProverEnvironment (F p2)}

theorem eval_c96_congr {x y z : Var (fields 32) (F p2)}
    (hx : eval env x = eval env' x) (hy : eval env y = eval env' y)
    (hz : eval env z = eval env' z) :
    eval env (c96 x y z) = eval env' (c96 x y z) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold c96 b32
  rw [Vector.getElem_ofFn]
  split
  · exact eval_getElem_congr hx _ _
  · split
    · exact eval_getElem_congr hy _ _
    · exact eval_getElem_congr hz _ _

theorem eval_c128_congr {x y z w : Var (fields 32) (F p2)}
    (hx : eval env x = eval env' x) (hy : eval env y = eval env' y)
    (hz : eval env z = eval env' z) (hw : eval env w = eval env' w) :
    eval env (c128 x y z w) = eval env' (c128 x y z w) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold c128 b32
  rw [Vector.getElem_ofFn]
  split
  · exact eval_getElem_congr hx _ _
  · split
    · exact eval_getElem_congr hy _ _
    · split
      · exact eval_getElem_congr hz _ _
      · exact eval_getElem_congr hw _ _

theorem eval_w128_congr {v : Var (fields 128) (F p2)} (h : eval env v = eval env' v) (k : ℕ) :
    eval env (w128 v k) = eval env' (w128 v k) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold w128 a128
  rw [Vector.getElem_ofFn]
  exact eval_getElem_congr h _ _

theorem eval_rotrE_congr {v : Var (fields 32) (F p2)} (h : eval env v = eval env' v) (n : ℕ) :
    eval env (rotrE n v) = eval env' (rotrE n v) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold rotrE b32
  rw [Vector.getElem_ofFn]
  exact eval_getElem_congr h _ _

theorem eval_shrE_congr {v : Var (fields 32) (F p2)} (h : eval env v = eval env' v) (n : ℕ) :
    eval env (shrE n v) = eval env' (shrE n v) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold shrE b32
  rw [Vector.getElem_ofFn]
  split
  · exact eval_getElem_congr h _ _
  · rfl

theorem eval_xor3E_congr {x y z : Var (fields 32) (F p2)}
    (hx : eval env x = eval env' x) (hy : eval env y = eval env' y)
    (hz : eval env z = eval env' z) :
    eval env (xor3E x y z) = eval env' (xor3E x y z) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold xor3E b32
  rw [Vector.getElem_ofFn]
  simp only [circuit_norm]
  rw [eval_getElem_congr hx, eval_getElem_congr hy, eval_getElem_congr hz]

theorem eval_lowerSigma0E_congr {v : Var (fields 32) (F p2)} (h : eval env v = eval env' v) :
    eval env (lowerSigma0E v) = eval env' (lowerSigma0E v) :=
  eval_xor3E_congr (eval_rotrE_congr h 7) (eval_rotrE_congr h 18) (eval_shrE_congr h 3)

theorem eval_lowerSigma1E_congr {v : Var (fields 32) (F p2)} (h : eval env v = eval env' v) :
    eval env (lowerSigma1E v) = eval env' (lowerSigma1E v) :=
  eval_xor3E_congr (eval_rotrE_congr h 17) (eval_rotrE_congr h 19) (eval_shrE_congr h 10)

theorem eval_upperSigma0E_congr {v : Var (fields 32) (F p2)} (h : eval env v = eval env' v) :
    eval env (upperSigma0E v) = eval env' (upperSigma0E v) :=
  eval_xor3E_congr (eval_rotrE_congr h 2) (eval_rotrE_congr h 13) (eval_rotrE_congr h 22)

theorem eval_upperSigma1E_congr {v : Var (fields 32) (F p2)} (h : eval env v = eval env' v) :
    eval env (upperSigma1E v) = eval env' (upperSigma1E v) :=
  eval_xor3E_congr (eval_rotrE_congr h 6) (eval_rotrE_congr h 11) (eval_rotrE_congr h 25)

end EvalCongr

end Solution.SHA256CompressGF2
