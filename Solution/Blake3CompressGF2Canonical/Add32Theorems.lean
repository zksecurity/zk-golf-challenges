import Challenge.Instances.Blake3CompressGF2Canonical.Interface
import Solution.Blake3CompressGF2Canonical.EvalCongr
import Mathlib.Tactic.LinearCombination

/-!
# 32-bit ripple-carry lemmas over GF(2)

BLAKE3 uses `add32 x y = (x + y) mod 2^32`. The canonical adder uses the
following ripple-carry semantics. Over `F 2` the carry recurrence has the
**single-product char-2 form**

  `c₀ = 0,   cᵢ₊₁ = (xᵢ + cᵢ)·(yᵢ + cᵢ) + cᵢ`

(equal to the textbook `xᵢyᵢ ⊕ cᵢ(xᵢ ⊕ yᵢ)` because `a² = a` in `F 2`).
The canonical circuit itself lives in `Add32Canon.lean`; this file contains
only its shared input type, pure arithmetic lemmas, and witness-agreement
helpers.
-/

namespace Solution.Blake3CompressGF2Canonical
namespace Add32

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.F2Bits

/-- Two 32-bit operands, as bit vectors. -/
structure Inputs (F : Type) where
  x : Vector F 32
  y : Vector F 32
deriving ProvableStruct

/-! ## Total accessors -/

/-- Entry `k % 32` (total access into a 32-vector). -/
@[reducible] def at32 {α : Type} (v : Vector α 32) (k : ℕ) : α :=
  v[k % 32]'(Nat.mod_lt _ (by norm_num))

/-- Entry `k % 31` (total access into a 31-vector). -/
@[reducible] def at31 {α : Type} (v : Vector α 31) (k : ℕ) : α :=
  v[k % 31]'(Nat.mod_lt _ (by norm_num))

/-! ## Pure ripple-carry semantics over `F 2` -/

/-- Honest carry into bit `i` (`c₀ = 0`), single-product char-2 form. -/
def carryVal (xv yv : ℕ → F p2) : ℕ → F p2
  | 0 => 0
  | i + 1 =>
    let c := carryVal xv yv i
    (xv i + c) * (yv i + c) + c

/-- Full-adder numeric identity on `F 2`: bit values of sum and carry decompose
`a + b + c` exactly. -/
theorem fullAdder_val : ∀ a b c : F p2,
    ZMod.val a + ZMod.val b + ZMod.val c
      = ZMod.val (a + b + c) + 2 * ZMod.val ((a + c) * (b + c) + c) := by decide

/-- Ripple-carry invariant: partial bit sums of `x`, `y` equal partial bit sums
of the sum bits plus the outgoing carry. -/
theorem adder_invariant (xv yv : ℕ → F p2) (k : ℕ) :
    (∑ i ∈ Finset.range k, ZMod.val (xv i) * 2 ^ i)
      + (∑ i ∈ Finset.range k, ZMod.val (yv i) * 2 ^ i)
      = (∑ i ∈ Finset.range k, ZMod.val (xv i + yv i + carryVal xv yv i) * 2 ^ i)
        + ZMod.val (carryVal xv yv k) * 2 ^ k := by
  induction k with
  | zero => simp [carryVal]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hfa := fullAdder_val (xv n) (yv n) (carryVal xv yv n)
    have hstep : carryVal xv yv (n + 1)
        = (xv n + carryVal xv yv n) * (yv n + carryVal xv yv n) + carryVal xv yv n := rfl
    have hfa' := congrArg (· * 2 ^ n) hfa
    simp only [add_mul] at hfa'
    rw [hstep, pow_succ]
    ring_nf
    ring_nf at hfa' ih
    linarith [ih, hfa']

/-- A sum of `k` bits weighted by `2^i` is `< 2^k`. -/
theorem sum_bits_lt (f : ℕ → F p2) (k : ℕ) :
    ∑ i ∈ Finset.range k, ZMod.val (f i) * 2 ^ i < 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hb : ZMod.val (f n) ≤ 1 := by
      have := ZMod.val_lt (f n); simp only [p2] at this; omega
    have hle : ZMod.val (f n) * 2 ^ n ≤ 2 ^ n := by
      calc ZMod.val (f n) * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ hb
        _ = 2 ^ n := one_mul _
    linarith

/-- The ripple-carry sum bits recompose to `(x + y) mod 2^32`. -/
theorem adder_correct (xv yv : ℕ → F p2) :
    (∑ i ∈ Finset.range 32, ZMod.val (xv i + yv i + carryVal xv yv i) * 2 ^ i)
      = ((∑ i ∈ Finset.range 32, ZMod.val (xv i) * 2 ^ i)
          + (∑ i ∈ Finset.range 32, ZMod.val (yv i) * 2 ^ i)) % 2 ^ 32 := by
  have hinv := adder_invariant xv yv 32
  have hlt := sum_bits_lt (fun i => xv i + yv i + carryVal xv yv i) 32
  have hc : ZMod.val (carryVal xv yv 32) < 2 := by
    have := ZMod.val_lt (carryVal xv yv 32); simp only [p2] at this; omega
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  rw [h32] at hinv hlt ⊢
  omega

/-! ## The witness IR for the carry chain

`carryVal` is a recursive accumulator, so an unrolled `FExpr` per bit would triple in
size at every step. The generator uses the **closed form** of a binary ripple carry
instead: over `F 2` the carry into position `k` is the arithmetic carry of the two
operand values,

  `val (carryVal xv yv k) = ((X % 2^k) + (Y % 2^k)) / 2^k`,   `X = Σ_{j<32} val (xv j)·2^j`,

which `adder_invariant` and `sum_bits_lt` above already prove. Each operand sum is one
authoring-time fold of 32 terms and the 31 carries share a single `mapRange` body, so
the whole program is O(32) IR nodes. -/

/-- A weighted bit sum truncated to its low `k` bits: the terms at positions `≥ k` are
divisible by `2^k`, and the low part is `< 2^k`. -/
theorem sum_bits_mod (f : ℕ → F p2) (k d : ℕ) :
    (∑ j ∈ Finset.range (k + d), ZMod.val (f j) * 2 ^ j) % 2 ^ k
      = ∑ j ∈ Finset.range k, ZMod.val (f j) * 2 ^ j := by
  induction d with
  | zero => exact Nat.mod_eq_of_lt (sum_bits_lt f k)
  | succ e ih =>
    rw [show k + (e + 1) = k + e + 1 from rfl, Finset.sum_range_succ]
    obtain ⟨c, hc⟩ : (2 : ℕ) ^ k ∣ ZMod.val (f (k + e)) * 2 ^ (k + e) :=
      Dvd.dvd.mul_left (pow_dvd_pow 2 (Nat.le_add_right k e)) _
    rw [hc, Nat.add_mul_mod_self_left, ih]

theorem sum_bits_mod_le (f : ℕ → F p2) {k n : ℕ} (hk : k ≤ n) :
    (∑ j ∈ Finset.range n, ZMod.val (f j) * 2 ^ j) % 2 ^ k
      = ∑ j ∈ Finset.range k, ZMod.val (f j) * 2 ^ j := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  exact sum_bits_mod f k d

/-- Closed form of the ripple carry: the carry into position `k` is the arithmetic
carry of the two operands' low-`k` bit sums. -/
theorem val_carryVal (xv yv : ℕ → F p2) (k : ℕ) :
    ZMod.val (carryVal xv yv k)
      = ((∑ j ∈ Finset.range k, ZMod.val (xv j) * 2 ^ j)
          + ∑ j ∈ Finset.range k, ZMod.val (yv j) * 2 ^ j) / 2 ^ k := by
  rw [adder_invariant xv yv k, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k),
    Nat.div_eq_of_lt (sum_bits_lt _ k), Nat.zero_add]

/-- The ℕ value of a 32-bit operand as a witness-IR expression: `Σ_j (at32 v j).val · 2^j`
(authoring-time fold; the IR counterpart of the bit sums the adder proofs use). -/
def bitsValIR (v : Var (fields 32) (F p2)) : Witgen.U64Expr (F p2) :=
  (List.finRange 32).foldr (fun j acc => (at32 v j.val).val * (2 ^ j.val : ℕ) + acc) 0

/-- The fold evaluates in the u64 sort, so it lands on `UInt64.ofNat` of the bit sum.
This holds unconditionally (`UInt64.ofNat` commutes with `+` and `*`); the `< 2^32`
bound that makes the truncation vacuous is produced once, in `eval_carryIR`. -/
theorem eval_bitsValIR (v : Var (fields 32) (F p2)) (ctx : Witgen.Ctx (F p2)) :
    (bitsValIR v).eval ctx
      = UInt64.ofNat (∑ j ∈ Finset.range 32,
          ZMod.val (Expression.eval ctx.env.toEnvironment (at32 v j)) * 2 ^ j) := by
  rw [← Fin.sum_univ_eq_sum_range
      (fun j => ZMod.val (Expression.eval ctx.env.toEnvironment (at32 v j)) * 2 ^ j) 32,
    Fin.sum_univ_def, bitsValIR, List.sum_eq_foldr, List.foldr_map]
  generalize List.finRange 32 = l
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [circuit_norm] at ih
    simp only [List.foldr_cons, circuit_norm, ih, UInt64.ofNat_add, UInt64.ofNat_mul]

/-- Carry into position `k` as a witness-IR field expression, in closed form. -/
def carryIR (x y : Var (fields 32) (F p2)) (k : Witgen.U64Expr (F p2)) : Witgen.FExpr (F p2) :=
  (((bitsValIR x % Witgen.U64Expr.pow2 k) + (bitsValIR y % Witgen.U64Expr.pow2 k))
    / Witgen.U64Expr.pow2 k).toField

/-- Every intermediate of `carryIR` is below `2^33`, so none of the u64 wraps fire and the
closed form is the honest carry. `hk` is what bounds the shift (`k ≤ 32 < 64`, so the
shift amount is not reduced either). -/
theorem eval_carryIR (x y : Var (fields 32) (F p2)) (ctx : Witgen.Ctx (F p2))
    (k : Witgen.U64Expr (F p2)) (hk : (k.eval ctx).toNat ≤ 32) :
    (carryIR x y k).eval ctx
      = carryVal (fun j => Expression.eval ctx.env.toEnvironment (at32 x j))
          (fun j => Expression.eval ctx.env.toEnvironment (at32 y j))
          (k.eval ctx).toNat := by
  set kn := (k.eval ctx).toNat with hkn
  set Sx := ∑ j ∈ Finset.range 32,
    ZMod.val (Expression.eval ctx.env.toEnvironment (at32 x j)) * 2 ^ j with hSx
  set Sy := ∑ j ∈ Finset.range 32,
    ZMod.val (Expression.eval ctx.env.toEnvironment (at32 y j)) * 2 ^ j with hSy
  have hSx_lt : Sx < 2 ^ 32 := sum_bits_lt _ 32
  have hSy_lt : Sy < 2 ^ 32 := sum_bits_lt _ 32
  have hpow : ((1 : UInt64) <<< k.eval ctx).toNat = 2 ^ kn := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_one,
      Nat.mod_eq_of_lt (show kn < 64 by omega), Nat.shiftLeft_eq, one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hpow_pos : 0 < 2 ^ kn := Nat.two_pow_pos kn
  have hpow_le : 2 ^ kn ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hk
  -- the whole computation stays below `2^33`, so every u64 wrap is the identity
  have hval : ((UInt64.ofNat Sx % (1 : UInt64) <<< k.eval ctx
        + UInt64.ofNat Sy % (1 : UInt64) <<< k.eval ctx)
      / (1 : UInt64) <<< k.eval ctx).toNat
      = (Sx % 2 ^ kn + Sy % 2 ^ kn) / 2 ^ kn := by
    have hx : (UInt64.ofNat Sx % (1 : UInt64) <<< k.eval ctx).toNat = Sx % 2 ^ kn := by
      rw [UInt64.toNat_mod, hpow, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (show Sx < 2 ^ 64 by omega)]
    have hy : (UInt64.ofNat Sy % (1 : UInt64) <<< k.eval ctx).toNat = Sy % 2 ^ kn := by
      rw [UInt64.toNat_mod, hpow, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (show Sy < 2 ^ 64 by omega)]
    have hxlt : Sx % 2 ^ kn < 2 ^ 32 := lt_of_lt_of_le (Nat.mod_lt _ hpow_pos) hpow_le
    have hylt : Sy % 2 ^ kn < 2 ^ 32 := lt_of_lt_of_le (Nat.mod_lt _ hpow_pos) hpow_le
    rw [UInt64.toNat_div, hpow, UInt64.toNat_add, hx, hy,
      Nat.mod_eq_of_lt (by omega : Sx % 2 ^ kn + Sy % 2 ^ kn < 2 ^ 64)]
  simp only [carryIR, Witgen.U64Expr.pow2, circuit_norm, eval_bitsValIR, ← hSx, ← hSy,
    hval]
  -- the truncated operand sums are the low-`kn` bit sums the adder invariant is stated over
  rw [hSx, hSy, sum_bits_mod_le _ hk, sum_bits_mod_le _ hk, ← val_carryVal]
  -- `circuit_norm` already turned `FiniteField.fromNat` into the `ℕ` cast
  simp [ZMod.natCast_val]

/-- Witness program for the 31 ripple carries `c₁..c₃₁`: one `mapRange` loop whose body
is the closed form of the carry at the running index. -/
def carriesIR (x y : Var (fields 32) (F p2)) : Witgen.VExpr (F p2) 31 :=
  .range 31 fun i => carryIR x y (i + 1)

/-- `carriesIR` computes exactly the values the adder proofs are stated over: cell `i`
is the honest carry into bit `i+1`. -/
theorem getElem_eval_carriesIR (x y : Var (fields 32) (F p2))
    (env : ProverEnvironment (F p2)) (i : ℕ) (hi : i < 31) :
    ((carriesIR x y).eval { env })[i]
      = carryVal (fun j => Expression.eval env.toEnvironment (at32 x j))
          (fun j => Expression.eval env.toEnvironment (at32 y j)) (i + 1) := by
  have hk : (Witgen.U64Expr.eval (F := F p2)
      { env := env, locals := #[], idx := i } (Witgen.U64Expr.idx + 1)).toNat = i + 1 := by
    simp only [circuit_norm, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_one]
  rw [carriesIR, Witgen.VExpr.range_def,
    Witgen.VExpr.getElem_eval_mapRange _ _ _ i hi,
    eval_carryIR x y _ _ (by rw [hk]; omega), hk]

/-! ## Shared symbolic helpers -/

/-- Carry into bit `i` as an expression over the witnessed carries
(`c₀ = 0`; `cᵢ = carries[i-1]` for `i ≥ 1`). -/
def carryE (carries : Vector (Expression (F p2)) 31) (i : ℕ) : Expression (F p2) :=
  if i = 0 then 0 else at31 carries (i - 1)

/-- No preconditions: over `F 2` every wire is already a bit. -/
def Assumptions (_ : Inputs (F p2)) : Prop := True

/-- Postcondition: the output word is `(x + y) mod 2^32`. -/
def Spec (input : Inputs (F p2)) (out : fields 32 (F p2)) : Prop :=
  toNat out = (toNat input.x + toNat input.y) % 2 ^ 32

/-- `toNat` on a 32-vector is the range-32 bit sum. -/
theorem toNat_eq_sum (v : Vector (F p2) 32) :
    toNat v = ∑ j ∈ Finset.range 32, bitAt v j * 2 ^ j := by
  unfold Challenge.F2Bits.toNat Challenge.F2Bits.wordAt
  exact Finset.sum_congr rfl fun j hj => by norm_num

/-- In-range `bitAt` is `ZMod.val` of the entry. -/
theorem bitAt_eq {N : ℕ} (v : Vector (F p2) N) (j : ℕ) (hj : j < N) :
    bitAt v j = ZMod.val (v[j]'hj) := by
  unfold Challenge.F2Bits.bitAt
  rw [getElem?_pos v j hj]
  rfl

/-! ## Witness-agreement helpers -/

/-- Componentwise agreement builds struct agreement. -/
theorem eval_mk_congr {x y : Var (fields 32) (F p2)} {env env' : ProverEnvironment (F p2)}
    (hx : eval env x = eval env' x) (hy : eval env y = eval env' y) :
    eval env (⟨x, y⟩ : Var Inputs (F p2)) = eval env' (⟨x, y⟩ : Var Inputs (F p2)) := by
  simp only [circuit_norm] at hx hy ⊢
  exact ⟨hx, hy⟩

theorem eval_x_congr {v : Var Inputs (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) : eval env v.x = eval env' v.x := by
  obtain ⟨x, y⟩ := v
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h
  simp only [circuit_norm, explicit_provable_type]
  exact h.1

theorem eval_y_congr {v : Var Inputs (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) : eval env v.y = eval env' v.y := by
  obtain ⟨x, y⟩ := v
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h
  simp only [circuit_norm, explicit_provable_type]
  exact h.2

/-- The witnessed carry expression at index `i` reads only variables in the
adder's own 31-cell block. -/
theorem eval_carryE_of_agreesBelow (n : ℕ) {k : ℕ} (hk : n + 31 ≤ k)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow k env') (i : ℕ) :
    Expression.eval env.toEnvironment
        (carryE (Vector.mapRange 31 fun j => var ⟨n + j⟩) i)
      = Expression.eval env'.toEnvironment
        (carryE (Vector.mapRange 31 fun j => var ⟨n + j⟩) i) := by
  unfold carryE at31
  split
  · rfl
  · have hmod : (i - 1) % 31 < 31 := Nat.mod_lt _ (by norm_num)
    simp only [circuit_norm]
    exact h_agree (n + (i - 1) % 31) (by omega)

end Add32
end Solution.Blake3CompressGF2Canonical
