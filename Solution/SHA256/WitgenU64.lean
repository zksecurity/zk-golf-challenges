import Clean.Circuit.WitnessIRSugar
import Solution.SHA256.NvalNorm

/-!
# The ℕ view of the witness IR's u64 sort

The witness IR's integer sort is `UInt64`: every operation wraps modulo `2^64`, and a
shift reduces its amount modulo `64`. The functional proofs, however, are stated over
`ℕ` — `specPaddedByte`, `numBlocksForLen`, `valueBits` and friends all compute with
honest naturals. This file is the bridge: `nval` is the ℕ value of a u64-sorted
program, and each former gets one lemma saying what `nval` of it is, in the shape
`(ℕ operation) % 2^64`.

The `_of` variants take the bound that makes the wrap vacuous and land on the plain ℕ
operation, which is the form the callers want: every quantity in this solution (byte
offsets, lengths, 32-bit words) is far below `2^64`, so the side conditions are
`omega` one-liners.

`nsub` is here for the same reason. The sort has no subtraction, but it wraps, so
`a + (2^64 - 1) · b` *is* `a - b` whenever `b ≤ a` — and unlike routing the
subtraction through the field it needs no bound on the minuend at all.

Witgen helpers are solution-local (the analogue of a circom function), so this lives
under `Solution/` rather than in the trusted challenge project.
-/

namespace Solution.SHA256
namespace WitgenU64

open Witgen

/-! The operator instances are not matched by the constructor-keyed lemmas below, so
peel them first. -/
attribute [nval_norm]
  Witgen.U64Expr.add_def Witgen.U64Expr.mul_def Witgen.U64Expr.div_def
  Witgen.U64Expr.hDiv_def Witgen.U64Expr.mod_def Witgen.U64Expr.hMod_def
  Witgen.U64Expr.land_def Witgen.U64Expr.lor_def Witgen.U64Expr.lxor_def
  Witgen.U64Expr.shiftL_def Witgen.U64Expr.shiftR_def
  Witgen.U64Expr.hShiftL_def Witgen.U64Expr.hShiftR_def
  Witgen.EqCond.u64_u64_def Witgen.EqCond.u64_nat_def Witgen.EqCond.nat_u64_def
  Witgen.LtCond.u64_u64_def Witgen.LtCond.u64_nat_def Witgen.LtCond.nat_u64_def
  Witgen.BExpr.and_def
  UInt64.toNat_ofNat' Nat.reduceMod Nat.reducePow

variable {K : Type} [FiniteField K] {ctx : Witgen.Ctx K} {a b : U64Expr K}

/-- The ℕ value of a u64-sorted witness expression. -/
def nval (ctx : Witgen.Ctx K) (e : U64Expr K) : ℕ := (e.eval ctx).toNat

theorem nval_lt (ctx : Witgen.Ctx K) (e : U64Expr K) : nval ctx e < 2 ^ 64 :=
  (e.eval ctx).toNat_lt_size

/-- Fold an unfolded `.toNat` back into `nval`, so a goal that `circuit_norm` has
already opened up meets the lemmas below in the shape they expect. -/
@[nval_norm] theorem toNat_eval (e : U64Expr K) : (e.eval ctx).toNat = nval ctx e := rfl

/-! ## One lemma per former -/

@[simp, nval_norm] theorem nval_const (c : UInt64) : nval ctx (.const c) = c.toNat := rfl

/-- The shape a numeral takes after `circuit_norm` has unfolded the operator instances. -/
@[simp, nval_norm] theorem nval_const_ofNat (n : ℕ) :
    nval (K := K) ctx (.const (UInt64.ofNat n)) = n % 2 ^ 64 := UInt64.toNat_ofNat'

/-- Numerals are `.const` under the `OfNat` instance; peel the instance so the
`nval_const_ofNat` rewrite above can fire. -/
@[simp, nval_norm] theorem ofNat_def (n : ℕ) :
    (OfNat.ofNat n : U64Expr K) = .const (UInt64.ofNat n) := rfl

/-- Numerals in range, in the form the ℕ-level proofs want to see them. -/
theorem nval_ofNat_of (n : ℕ) (h : n < 2 ^ 64) :
    nval (K := K) ctx (OfNat.ofNat n) = n := by
  rw [ofNat_def, nval_const_ofNat, Nat.mod_eq_of_lt h]

@[simp, nval_norm] theorem nval_idx : nval (K := K) ctx .idx = ctx.idx % 2 ^ 64 :=
  UInt64.toNat_ofNat'

@[simp, nval_norm] theorem nval_val (x : FExpr K) :
    nval ctx (.val x) = FiniteField.val (x.eval ctx) % 2 ^ 64 :=
  UInt64.toNat_ofNat'

@[simp, nval_norm] theorem nval_add : nval ctx (.add a b) = (nval ctx a + nval ctx b) % 2 ^ 64 :=
  UInt64.toNat_add _ _

@[simp, nval_norm] theorem nval_mul : nval ctx (.mul a b) = (nval ctx a * nval ctx b) % 2 ^ 64 :=
  UInt64.toNat_mul _ _

@[simp, nval_norm] theorem nval_div : nval ctx (.div a b) = nval ctx a / nval ctx b :=
  UInt64.toNat_div _ _

@[simp, nval_norm] theorem nval_mod : nval ctx (.mod a b) = nval ctx a % nval ctx b :=
  UInt64.toNat_mod _ _

@[simp, nval_norm] theorem nval_shiftR :
    nval ctx (.shiftR a b) = nval ctx a >>> (nval ctx b % 64) :=
  UInt64.toNat_shiftRight _ _

@[simp, nval_norm] theorem nval_shiftL :
    nval ctx (.shiftL a b) = (nval ctx a <<< (nval ctx b % 64)) % 2 ^ 64 :=
  UInt64.toNat_shiftLeft _ _

@[simp, nval_norm] theorem nval_ite (c : BExpr K) (t e : U64Expr K) :
    nval ctx (.ite c t e) = if c.eval ctx then nval ctx t else nval ctx e := by
  simp only [nval, U64Expr.eval]
  split <;> rfl

/-! ## Conditions -/

@[simp, nval_norm] theorem eval_lt : (BExpr.lt a b).eval ctx = decide (nval ctx a < nval ctx b) := by
  simp only [BExpr.eval, nval, UInt64.lt_iff_toNat_lt]
  rfl

@[simp, nval_norm] theorem eval_and (x y : BExpr K) :
    (BExpr.and x y).eval ctx = (x.eval ctx && y.eval ctx) := rfl

@[simp, nval_norm] theorem eval_not (x : BExpr K) :
    (BExpr.not x).eval ctx = !x.eval ctx := rfl

@[simp, nval_norm] theorem eval_neq : (BExpr.neq a b).eval ctx = decide (nval ctx a = nval ctx b) := by
  simp [BExpr.eval, nval, UInt64.toNat_inj]

/-! ## The `ℕ`-shaped forms, for operands that do not wrap -/

theorem nval_add_of (h : nval ctx a + nval ctx b < 2 ^ 64) :
    nval ctx (.add a b) = nval ctx a + nval ctx b := by
  rw [nval_add, Nat.mod_eq_of_lt h]

theorem nval_mul_of (h : nval ctx a * nval ctx b < 2 ^ 64) :
    nval ctx (.mul a b) = nval ctx a * nval ctx b := by
  rw [nval_mul, Nat.mod_eq_of_lt h]

theorem nval_shiftR_of (h : nval ctx b < 64) :
    nval ctx (.shiftR a b) = nval ctx a / 2 ^ nval ctx b := by
  rw [nval_shiftR, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]

theorem nval_shiftL_of (h : nval ctx b < 64)
    (hlt : nval ctx a * 2 ^ nval ctx b < 2 ^ 64) :
    nval ctx (.shiftL a b) = nval ctx a * 2 ^ nval ctx b := by
  rw [nval_shiftL, Nat.mod_eq_of_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt]

/-! ## Truncated subtraction -/

/-- Truncated subtraction in the u64 sort: `a - b` when `b ≤ a`. -/
def nsub (a b : U64Expr K) : U64Expr K :=
  .add a (.mul (.const 18446744073709551615) b)

/-- The unconditional, simp-normal shape: `nsub` is a wrapping add-multiply, so
everything below it is ordinary `ℕ` arithmetic that `omega` can finish. -/
@[simp, nval_norm] theorem nval_nsub_wrap :
    nval ctx (nsub a b) = (nval ctx a + 18446744073709551615 * nval ctx b) % 2 ^ 64 := by
  simp only [nval, nsub, U64Expr.eval, UInt64.toNat_add, UInt64.toNat_mul,
    show (18446744073709551615 : UInt64).toNat = 18446744073709551615 from rfl]
  have hb : (U64Expr.eval ctx b).toNat < 2 ^ 64 := (U64Expr.eval ctx b).toNat_lt_size
  omega

theorem nval_nsub (hba : nval ctx b ≤ nval ctx a) :
    nval ctx (nsub a b) = nval ctx a - nval ctx b := by
  have ha := nval_lt ctx a
  have hb := nval_lt ctx b
  simp only [nval, nsub, U64Expr.eval, UInt64.toNat_add, UInt64.toNat_mul,
    show (18446744073709551615 : UInt64).toNat = 18446744073709551615 from rfl] at ha hb hba ⊢
  omega

end WitgenU64
end Solution.SHA256
