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
  rw [hx, hy]

theorem eval_x_congr {v : Var Inputs (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) : eval env v.x = eval env' v.x := by
  have h2 := congrArg (fun s : Inputs (F p2) => s.x) h
  simpa [circuit_norm] using h2

theorem eval_y_congr {v : Var Inputs (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) : eval env v.y = eval env' v.y := by
  have h2 := congrArg (fun s : Inputs (F p2) => s.y) h
  simpa [circuit_norm] using h2

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
