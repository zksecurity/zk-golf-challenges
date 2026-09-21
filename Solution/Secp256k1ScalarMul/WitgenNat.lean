import Clean.Circuit.WitnessIRSugar
import Mathlib.FieldTheory.Finite.Basic

/-!
# The ℕ model the big-integer witness programs are proved against

The witness IR's integer sort is `UInt64`. A secp limb is 64 bits wide and an RSA limb
121, so no big-integer quantity in these gadgets — not a limb product, not a running
carry, and certainly not a 256- or 4096-bit value — fits in one u64. Big values
therefore have to be *represented*, as little-endian digit lists in a base the sort can
multiply in (`2^W` with `2 * W ≤ 64`), and every witness program becomes a loop over
digits.

This file is the ℕ half of that: digit lists, the schoolbook operations on them, and
the proof that each one computes the ordinary `ℕ` operation on the value the list
denotes. It mentions the IR nowhere, so it is ordinary arithmetic that `omega` and
induction can handle. The u64 step lists are built on top and proved to leave exactly
the digits these functions produce, which is what makes the two halves compose.

Two things shape the definitions below, both learned the hard way:

* **Never divide by the base.** `(x + base) / base` with `base` a `2^32`-sized literal
  sends `Nat.div`'s unfolding into a recursion over the literal: a two-line lemma about
  it takes minutes to elaborate, and a `rw` on the defining equation never finishes.
  Every carry and borrow here is therefore a *case split* (`if s < base then … else …`),
  never a division. Same values, none of the blow-up.
* **Digits and carry-out are separate functions.** A pair-valued definition puts two
  copies of the recursive call into its equation lemma, and `simp` then unfolds the
  recursion exponentially.

Division is *binary* long division rather than a base-`2^W` schoolbook: one bit at a
time costs a factor `W` more steps, but its invariant is a short induction, where a
digit-estimating division needs the whole quotient-digit correction argument. Witness
programs are data, so the step count is a prover-runtime cost, not an elaboration one.
-/

namespace Solution.Secp256k1ScalarMul
namespace WitgenNat

/-- Digit width. Chosen so that a product of two digits, plus two carries, stays below
`2^64`: `(2^32 - 1)^2 + 2 * (2^32 - 1) < 2^64`. -/
def W : ℕ := 32

/-- The digit base. -/
def base : ℕ := 2 ^ W

theorem base_eq : base = 4294967296 := by rw [base, W]; norm_num

theorem base_pos : 0 < base := by rw [base_eq]; norm_num

theorem base_lt : base < 2 ^ 64 := by rw [base_eq]; norm_num

theorem two_base_lt : 2 * base < 2 ^ 64 := by rw [base_eq]; norm_num

theorem three_base_lt : 3 * base < 2 ^ 64 := by rw [base_eq]; norm_num

/-- A digit product plus two digits still fits a u64: this is the whole reason `W` is
half of the u64 width. -/
theorem base_mul_base : base * base = 2 ^ 64 := by rw [base_eq]; norm_num

/-- Subtracting a multiple of the base is taking the remainder, when the result is a
digit. Every digit-producing step below is stated as `s - base * carry` (which is what
makes the value identities `omega`-sized) but *computed* in the u64 sort as `s % base`,
because that sort has no subtraction; this is the bridge. -/
theorem sub_mul_eq_mod {s k : ℕ} (h1 : base * k ≤ s) (h2 : s - base * k < base) :
    s - base * k = s % base := by
  conv_rhs => rw [show s = base * k + (s - base * k) by omega]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h2]

/-- The value of a little-endian digit list. -/
def lval : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + base * lval ds

@[simp] theorem lval_nil : lval [] = 0 := rfl
@[simp] theorem lval_cons (d : ℕ) (ds : List ℕ) : lval (d :: ds) = d + base * lval ds := rfl

/-- A digit list is *normalized* when every digit is a digit. -/
def Bounded (l : List ℕ) : Prop := ∀ d ∈ l, d < base

theorem Bounded.nil : Bounded [] := by intro _ h; cases h

theorem Bounded.cons {d : ℕ} {ds : List ℕ} (hd : d < base) (h : Bounded ds) :
    Bounded (d :: ds) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hd
  · exact h x hx

theorem Bounded.tail {d : ℕ} {ds : List ℕ} (h : Bounded (d :: ds)) : Bounded ds :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem Bounded.head {d : ℕ} {ds : List ℕ} (h : Bounded (d :: ds)) : d < base :=
  h d (List.mem_cons_self ..)

theorem headD_lt {ys : List ℕ} (hy : Bounded ys) : ys.headD 0 < base := by
  cases ys with
  | nil => simpa using base_pos
  | cons z zs => simpa using hy.head

theorem bounded_tail {ys : List ℕ} (hy : Bounded ys) : Bounded ys.tail := by
  cases ys with
  | nil => exact Bounded.nil
  | cons z zs => exact (hy : Bounded (z :: zs)).tail

theorem lval_headD_tail : ∀ l : List ℕ, lval l = l.headD 0 + base * lval l.tail
  | [] => by simp
  | _ :: _ => by simp

/-- A normalized list of length `k` denotes a value below `base ^ k`. -/
theorem lval_lt {l : List ℕ} (h : Bounded l) : lval l < base ^ l.length := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    have hd := h.head
    have hds := ih h.tail
    have hb : 1 ≤ base ^ ds.length := Nat.one_le_pow _ _ base_pos
    simp only [List.length_cons, pow_succ, lval_cons, base_eq] at hd hds hb ⊢
    omega

/-! ## Digits of a number

`ofNat v len` is the inverse of `lval` on a fixed width: the `len` low digits of `v`.
The IR programs that *write* a value (a constant, or a window of bits read out of a
field element) land on exactly these digits, so this is the spec they are proved
against. -/

/-- The `len` low digits of `v`, least significant first. -/
def ofNat (v : ℕ) : ℕ → List ℕ
  | 0 => []
  | len + 1 => v % base :: ofNat (v / base) len

@[simp] theorem length_ofNat (v len : ℕ) : (ofNat v len).length = len := by
  induction len generalizing v with
  | zero => rfl
  | succ len ih => simp only [ofNat, List.length_cons, ih]

theorem bounded_ofNat (v len : ℕ) : Bounded (ofNat v len) := by
  induction len generalizing v with
  | zero => exact Bounded.nil
  | succ len ih => exact Bounded.cons (Nat.mod_lt _ base_pos) (ih _)

theorem lval_ofNat (v len : ℕ) : lval (ofNat v len) = v % base ^ len := by
  induction len generalizing v with
  | zero => simp [ofNat, Nat.mod_one]
  | succ len ih => rw [ofNat, lval_cons, ih, pow_succ', Nat.mod_mul]

/-- Digit `k` of `ofNat v len`, the form the IR digit programs read it in. -/
theorem getD_ofNat (v len k : ℕ) (hk : k < len) :
    (ofNat v len).getD k 0 = v / base ^ k % base := by
  induction len generalizing v k with
  | zero => omega
  | succ len ih =>
    cases k with
    | zero => simp [ofNat]
    | succ k =>
      rw [ofNat, List.getD_cons_succ, ih _ _ (by omega), pow_succ',
        Nat.div_div_eq_div_mul]

/-- A value that fits `len` digits is exactly what its digits denote. -/
theorem lval_ofNat_of_lt {v len : ℕ} (h : v < base ^ len) : lval (ofNat v len) = v := by
  rw [lval_ofNat, Nat.mod_eq_of_lt h]

/-- Zero is the all-zero register: the shape the division loop's registers start in. -/
theorem ofNat_zero : ∀ len : ℕ, ofNat 0 len = List.replicate len 0
  | 0 => rfl
  | len + 1 => by
      simp only [ofNat, List.replicate_succ, Nat.zero_mod, Nat.zero_div, ofNat_zero len]

/-- **Normalized digit lists are canonical.** A bounded list is the `ofNat` of its own
value at its own length. This is what lets a program whose result is only known through
`lval`/`Bounded`/length (the remainder register of a division, say) be handed to the
next program as a *named* digit list, which is what makes chaining modular
multiplications possible at all. -/
theorem eq_ofNat : ∀ {l : List ℕ}, Bounded l → l = ofNat (lval l) l.length
  | [], _ => rfl
  | d :: ds, h => by
      have hd : d < base := h.head
      have hrec := eq_ofNat h.tail
      rw [List.length_cons, ofNat, lval_cons]
      congr 1
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
      · rw [Nat.add_mul_div_left _ _ base_pos, Nat.div_eq_of_lt hd, Nat.zero_add]
        exact hrec

/-- The digits of a value only see it modulo the register width. -/
theorem ofNat_mod (v len : ℕ) : ofNat (v % base ^ len) len = ofNat v len := by
  induction len generalizing v with
  | zero => rfl
  | succ len ih =>
      rw [ofNat, ofNat, pow_succ', Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ih]

/-- `eq_ofNat` with the value and the length supplied: the shape a program's result is
canonicalised in. -/
theorem eq_ofNat_of {l : List ℕ} (h : Bounded l) {v n : ℕ} (hv : lval l = v)
    (hn : l.length = n) : l = ofNat v n := by
  rw [← hv, ← hn]; exact eq_ofNat h

/-! ## Addition with carry

`a + b + c` with three digits is below `3 * base`, so the carry out is one of `0`, `1`,
`2` — read off by two comparisons rather than a division. -/

/-- The carry out of one addition step. -/
def addCarry (s : ℕ) : ℕ := if s < base then 0 else if s < 2 * base then 1 else 2

/-- The digit produced by one addition step. -/
def addDigit (s : ℕ) : ℕ := s - base * addCarry s

theorem addCarry_lt {s : ℕ} : addCarry s < base := by
  have hb := base_eq
  rw [addCarry]
  split <;> [omega; split] <;> omega

theorem addDigit_lt {s : ℕ} (h : s < 3 * base) : addDigit s < base := by
  have hb := base_eq
  rw [addDigit, addCarry]
  split <;> [omega; split] <;> omega

theorem addDigit_add_carry (s : ℕ) : addDigit s + base * addCarry s = s := by
  have hb := base_eq
  rw [addDigit, addCarry]
  split <;> [omega; split] <;> omega

/-- The digit of an addition step is the remainder: what the u64 program computes with
`.mod`, since the u64 sort has no subtraction. -/
theorem addDigit_eq_mod {s : ℕ} (h : s < 3 * base) : addDigit s = s % base := by
  have hc : base * addCarry s ≤ s ∧ s - base * addCarry s < base := by
    rw [addCarry]; split_ifs <;> omega
  rw [addDigit]
  exact sub_mul_eq_mod hc.1 hc.2

/-- Add two digit lists with an incoming carry, least significant digit first. -/
def addc : List ℕ → List ℕ → ℕ → List ℕ
  | [], [], c => [c]
  | [], b :: bs, c => addDigit (b + c) :: addc [] bs (addCarry (b + c))
  | a :: as, [], c => addDigit (a + c) :: addc as [] (addCarry (a + c))
  | a :: as, b :: bs, c => addDigit (a + b + c) :: addc as bs (addCarry (a + b + c))

theorem lval_addc : ∀ (a b : List ℕ) (c : ℕ), lval (addc a b c) = lval a + lval b + c
  | [], [], c => by simp [addc]
  | [], b :: bs, c => by
    have ih := lval_addc [] bs (addCarry (b + c))
    have hdm := addDigit_add_carry (b + c)
    simp only [addc, lval_cons, ih, lval_nil, Nat.mul_add]
    omega
  | a :: as, [], c => by
    have ih := lval_addc as [] (addCarry (a + c))
    have hdm := addDigit_add_carry (a + c)
    simp only [addc, lval_cons, ih, lval_nil, Nat.mul_add]
    omega
  | a :: as, b :: bs, c => by
    have ih := lval_addc as bs (addCarry (a + b + c))
    have hdm := addDigit_add_carry (a + b + c)
    simp only [addc, lval_cons, ih, Nat.mul_add]
    omega

theorem bounded_addc (a : List ℕ) : ∀ (b : List ℕ) (c : ℕ),
    Bounded a → Bounded b → c < base → Bounded (addc a b c) := by
  induction a with
  | nil =>
    intro b
    induction b with
    | nil =>
      intro c _ _ hc
      simp only [addc]
      exact Bounded.cons hc Bounded.nil
    | cons y ys ihb =>
      intro c _ hy hc
      have hy0 := hy.head
      simp only [addc]
      exact Bounded.cons (addDigit_lt (s := y + c) (by omega))
        (ihb _ Bounded.nil hy.tail addCarry_lt)
  | cons x xs iha =>
    intro b
    cases b with
    | nil =>
      intro c hx _ hc
      have hx0 := hx.head
      simp only [addc]
      exact Bounded.cons (addDigit_lt (s := x + c) (by omega))
        (iha [] _ hx.tail Bounded.nil addCarry_lt)
    | cons y ys =>
      intro c hx hy hc
      have hx0 := hx.head
      have hy0 := hy.head
      simp only [addc]
      exact Bounded.cons (addDigit_lt (s := x + y + c) (by omega))
        (iha ys _ hx.tail hy.tail addCarry_lt)

/-! ## Shift left by one bit

The division loop's remainder register is a fixed-length list, so shifting returns the
digit that falls off the top as an explicit carry-out. -/

/-- The carry out of one doubling step. -/
def dblCarry (s : ℕ) : ℕ := if s < base then 0 else 1

/-- The digit produced by one doubling step. -/
def dblDigit (s : ℕ) : ℕ := s - base * dblCarry s

theorem dblCarry_lt_two {s : ℕ} : dblCarry s < 2 := by rw [dblCarry]; split <;> omega

theorem dblDigit_lt {s : ℕ} (h : s < 2 * base) : dblDigit s < base := by
  have hb := base_eq
  rw [dblDigit, dblCarry]; split <;> omega

theorem dblDigit_add_carry (s : ℕ) : dblDigit s + base * dblCarry s = s := by
  rw [dblDigit, dblCarry]; split <;> omega

/-- The digit of a doubling step is the remainder (see `addDigit_eq_mod`). -/
theorem dblDigit_eq_mod {s : ℕ} (h : s < 2 * base) : dblDigit s = s % base := by
  have hc : base * dblCarry s ≤ s ∧ s - base * dblCarry s < base := by
    rw [dblCarry]; split_ifs <;> omega
  rw [dblDigit]
  exact sub_mul_eq_mod hc.1 hc.2

/-- Digits of `2 * l + c`, keeping the length. -/
def shl1 : List ℕ → ℕ → List ℕ
  | [], _ => []
  | d :: ds, c => dblDigit (2 * d + c) :: shl1 ds (dblCarry (2 * d + c))

/-- The digit that falls off the top of `shl1`. -/
def shl1Out : List ℕ → ℕ → ℕ
  | [], c => c
  | d :: ds, c => shl1Out ds (dblCarry (2 * d + c))

theorem length_shl1 (l : List ℕ) : ∀ c : ℕ, (shl1 l c).length = l.length := by
  induction l with
  | nil => intro _; rfl
  | cons d ds ih => intro c; simp only [shl1, List.length_cons, ih]

theorem bounded_shl1 (l : List ℕ) : ∀ c : ℕ, Bounded l → c < 2 → Bounded (shl1 l c) := by
  induction l with
  | nil => intro _ _ _; exact Bounded.nil
  | cons d ds ih =>
    intro c h hc
    have hd := h.head
    exact Bounded.cons (dblDigit_lt (by omega)) (ih _ h.tail dblCarry_lt_two)

theorem lval_shl1 : ∀ (l : List ℕ) (c : ℕ),
    lval (shl1 l c) + base ^ l.length * shl1Out l c = 2 * lval l + c
  | [], c => by simp [shl1, shl1Out]
  | d :: ds, c => by
    have ih := lval_shl1 ds (dblCarry (2 * d + c))
    have hdm := dblDigit_add_carry (2 * d + c)
    have key : base * (lval (shl1 ds (dblCarry (2 * d + c)))
          + base ^ ds.length * shl1Out ds (dblCarry (2 * d + c)))
        = base * (2 * lval ds + dblCarry (2 * d + c)) := by rw [ih]
    rw [Nat.mul_add, Nat.mul_add] at key
    have hR : base * (2 * lval ds) = 2 * (base * lval ds) := by ring
    have hQ : base ^ (ds.length + 1) * shl1Out ds (dblCarry (2 * d + c))
        = base * (base ^ ds.length * shl1Out ds (dblCarry (2 * d + c))) := by
      rw [pow_succ]; ring
    simp only [shl1, shl1Out, lval_cons, List.length_cons, hQ]
    omega

/-! ## Subtraction with borrow

The division loop needs no separate comparison: subtracting and reading the borrow out
answers "is the remainder at least the divisor?" in the same pass. -/

/-- The borrow out of one subtraction step. -/
def subBorrow (x y b : ℕ) : ℕ := if y + b ≤ x then 0 else 1

/-- The digit produced by one subtraction step. -/
def subDigit (x y b : ℕ) : ℕ := x + base * subBorrow x y b - y - b

theorem subBorrow_lt (x y b : ℕ) : subBorrow x y b < 2 := by
  rw [subBorrow]; split <;> omega

theorem subDigit_lt {x y b : ℕ} (hx : x < base) (hy : y < base) (hb : b < 2) :
    subDigit x y b < base := by
  have hbb := base_eq
  rw [subDigit, subBorrow]; split <;> omega

theorem subDigit_add (x y b : ℕ) (hy : y < base) (hb : b < 2) :
    subDigit x y b + y + b = x + base * subBorrow x y b := by
  have hbb := base_eq
  rw [subDigit, subBorrow]; split <;> omega

/-- The digit of a subtraction step is a remainder of the *borrowed* minuend. The u64
sort has no subtraction, so the program computes `x + base - y - b` by a wrapping add
and takes `% base`; both borrow cases collapse to that one expression. -/
theorem subDigit_eq_mod {x y b : ℕ} (hx : x < base) (hy : y < base) (hb : b < 2) :
    subDigit x y b = (x + base - y - b) % base := by
  have hrw : subDigit x y b = (x + base - y - b) - base * (1 - subBorrow x y b) := by
    rw [subDigit, subBorrow]; split_ifs <;> omega
  rw [hrw]
  refine sub_mul_eq_mod ?_ ?_ <;> (rw [subBorrow]; split_ifs <;> omega)

/-- Digits of `x - y - b`, keeping `x`'s length. The second operand is read through
`headD`/`tail`, so a shorter divisor is zero-padded. -/
def subb : List ℕ → List ℕ → ℕ → List ℕ
  | [], _, _ => []
  | x :: xs, ys, b =>
    subDigit x (ys.headD 0) b :: subb xs ys.tail (subBorrow x (ys.headD 0) b)

/-- The borrow out of `subb`: `1` exactly when what was subtracted exceeded `x`. -/
def subbOut : List ℕ → List ℕ → ℕ → ℕ
  | [], _, b => b
  | x :: xs, ys, b => subbOut xs ys.tail (subBorrow x (ys.headD 0) b)

theorem length_subb (x : List ℕ) : ∀ (y : List ℕ) (b : ℕ),
    (subb x y b).length = x.length := by
  induction x with
  | nil => intro _ _; rfl
  | cons d ds ih => intro ys b; simp only [subb, List.length_cons, ih]

theorem bounded_subb (x : List ℕ) : ∀ (y : List ℕ) (b : ℕ),
    Bounded x → Bounded y → b < 2 → Bounded (subb x y b) := by
  induction x with
  | nil => intro _ _ _ _ _; exact Bounded.nil
  | cons d ds ih =>
    intro ys b hx hy hb
    exact Bounded.cons (subDigit_lt hx.head (headD_lt hy) hb)
      (ih ys.tail _ hx.tail (bounded_tail hy) (subBorrow_lt _ _ _))

theorem subbOut_lt (x : List ℕ) : ∀ (y : List ℕ) (b : ℕ), b < 2 → subbOut x y b < 2 := by
  induction x with
  | nil => intro _ _ hb; exact hb
  | cons d ds ih =>
    intro ys b _
    rw [subbOut]
    exact ih ys.tail _ (subBorrow_lt _ _ _)

/-- The exact value identity: what comes out, plus what was subtracted, is what went
in — up to the borrow out weighted by the register width. The divisor must fit in the
register, which is the division loop's situation. -/
theorem lval_subb (x : List ℕ) : ∀ (y : List ℕ) (b : ℕ),
    Bounded x → Bounded y → b < 2 → y.length ≤ x.length →
    lval (subb x y b) + lval y + b = lval x + base ^ x.length * subbOut x y b := by
  induction x with
  | nil =>
    intro y b _ _ hb hlen
    have hy : y = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hy
    simp [subb, subbOut]
  | cons d ds ih =>
    intro ys b hx hy hb hlen
    have hyh := headD_lt hy
    have hlent : ys.tail.length ≤ ds.length := by
      cases ys with
      | nil => simp
      | cons z zs => simpa using hlen
    have ihh := ih ys.tail (subBorrow d (ys.headD 0) b) hx.tail (bounded_tail hy)
      (subBorrow_lt d (ys.headD 0) b) hlent
    have hdm := subDigit_add d (ys.headD 0) b hyh hb
    have key : base * (lval (subb ds ys.tail (subBorrow d (ys.headD 0) b))
          + lval ys.tail + subBorrow d (ys.headD 0) b)
        = base * (lval ds + base ^ ds.length
            * subbOut ds ys.tail (subBorrow d (ys.headD 0) b)) := by rw [ihh]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add] at key
    have hQ : base ^ (ds.length + 1) * subbOut ds ys.tail (subBorrow d (ys.headD 0) b)
        = base * (base ^ ds.length
            * subbOut ds ys.tail (subBorrow d (ys.headD 0) b)) := by
      rw [pow_succ]; ring
    have hys := lval_headD_tail ys
    simp only [subb, subbOut, lval_cons, List.length_cons, hQ]
    omega

/-! ## Multiplication

A digit product plus a carry is below `base ^ 2`, which is exactly why `W` is half of
the u64 width. The carry here *is* a division by the base, which is fine: the
pathological shape is `(x + base) / base`, where the guard `base ≤ x + base` reduces
structurally and walks the literal. `(y * x + c) / base` has no such guard. -/

/-- `b * x + c`, one pass over `b`'s digits. -/
def mulAdd : List ℕ → ℕ → ℕ → List ℕ
  | [], _, c => [c]
  | y :: ys, x, c => (y * x + c) % base :: mulAdd ys x ((y * x + c) / base)

theorem lval_mulAdd : ∀ (b : List ℕ) (x c : ℕ), lval (mulAdd b x c) = lval b * x + c
  | [], x, c => by simp [mulAdd]
  | y :: ys, x, c => by
    have ih := lval_mulAdd ys x ((y * x + c) / base)
    have hdm := Nat.div_add_mod (y * x + c) base
    have key : base * lval (mulAdd ys x ((y * x + c) / base))
        = base * (lval ys * x + (y * x + c) / base) := by rw [ih]
    rw [Nat.mul_add] at key
    have hR : base * (lval ys * x) = base * lval ys * x := by ring
    simp only [mulAdd, lval_cons, Nat.add_mul]
    omega

theorem bounded_mulAdd (b : List ℕ) : ∀ (x c : ℕ),
    Bounded b → x < base → c < base → Bounded (mulAdd b x c) := by
  induction b with
  | nil => intro _ c _ _ hc; exact Bounded.cons hc Bounded.nil
  | cons y ys ih =>
    intro x c hb hx hc
    have hy := hb.head
    have hprod : y * x + c < base * base := by
      rw [base_eq] at hy hx hc ⊢
      have h1 : y * x ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
      norm_num at h1 ⊢
      omega
    exact Bounded.cons (Nat.mod_lt _ base_pos)
      (ih x _ hb.tail hx ((Nat.div_lt_iff_lt_mul base_pos).mpr hprod))

/-- Schoolbook multiplication: one `mulAdd` pass per digit of the left operand. -/
def mul : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: as, b => addc (mulAdd b a 0) (0 :: mul as b) 0

theorem lval_mul : ∀ (a b : List ℕ), lval (mul a b) = lval a * lval b
  | [], b => by simp [mul]
  | a :: as, b => by
    have ih := lval_mul as b
    have hR : base * (lval as * lval b) = base * lval as * lval b := by ring
    have hC : lval b * a = a * lval b := Nat.mul_comm _ _
    simp only [mul, lval_addc, lval_mulAdd, lval_cons, ih, Nat.add_mul]
    omega

theorem bounded_mul (a : List ℕ) : ∀ b : List ℕ,
    Bounded a → Bounded b → Bounded (mul a b) := by
  induction a with
  | nil => intro _ _ _; exact Bounded.nil
  | cons x xs ih =>
    intro b ha hb
    exact bounded_addc _ _ _ (bounded_mulAdd b _ _ hb ha.head base_pos)
      (Bounded.cons base_pos (ih b ha.tail hb)) base_pos

/-! ## Digit and bit access

The division loop consumes the dividend one bit at a time, most significant first, so
it needs to read bit `i` of a digit list. Both lemmas below say the obvious thing: the
list denotes the number whose digits and bits these are. -/

/-- Digit `k` of a digit list (`0` past the end). -/
def digitAt (x : List ℕ) (k : ℕ) : ℕ := x.getD k 0

theorem lval_digitAt (x : List ℕ) (h : Bounded x) :
    ∀ k, lval x / base ^ k % base = digitAt x k := by
  induction x with
  | nil => intro k; simp [digitAt]
  | cons d ds ih =>
    intro k
    cases k with
    | zero =>
      have hd := h.head
      simp only [pow_zero, Nat.div_one, lval_cons, digitAt, List.getD_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ k =>
      have hd := h.head
      have hdiv : (d + base * lval ds) / base = lval ds := by
        rw [Nat.add_mul_div_left _ _ base_pos, Nat.div_eq_of_lt hd, Nat.zero_add]
      have := ih h.tail k
      simp only [lval_cons, digitAt, List.getD_cons_succ, pow_succ] at this ⊢
      rw [show base ^ k * base = base * base ^ k from Nat.mul_comm _ _,
        ← Nat.div_div_eq_div_mul, hdiv, this]

/-- A power of the base is a power of two: the bridge between the digit view
(`base ^ k`) and the bit view (`2 ^ (W * k)`) the IR readers work in. -/
theorem base_pow (k : ℕ) : base ^ k = 2 ^ (W * k) := by rw [base, ← pow_mul]

/-- A digit product plus a digit fits a u64. This is the exact bound the multiplication
program runs against: `(base - 1)^2 + (base - 1) = (base - 1) * base < base * base`. -/
theorem digit_mul_add_lt {y x c : ℕ} (hy : y < base) (hx : x < base) (hc : c < base) :
    y * x + c < 2 ^ 64 := by
  obtain ⟨k, hk⟩ : ∃ k, base = k + 1 := ⟨base - 1, by have := base_pos; omega⟩
  have h1 : y * x ≤ k * k := Nat.mul_le_mul (by omega) (by omega)
  have h3 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
  rw [← base_mul_base, hk, h3]
  omega

/-- Bit `i` of a digit list. -/
def bitAt (x : List ℕ) (i : ℕ) : ℕ := digitAt x (i / W) / 2 ^ (i % W) % 2

theorem lval_bitAt (x : List ℕ) (h : Bounded x) (i : ℕ) :
    bitAt x i = lval x / 2 ^ i % 2 := by
  have hW : 0 < W := by rw [W]; norm_num
  have hdig := lval_digitAt x h (i / W)
  have hsplit : (2 : ℕ) ^ i = base ^ (i / W) * 2 ^ (i % W) := by
    have hdm := Nat.div_add_mod i W
    rw [base, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [bitAt, ← hdig, hsplit, ← Nat.div_div_eq_div_mul]
  generalize lval x / base ^ (i / W) = N
  have h1 : (N % 2 ^ W).testBit (i % W) = N.testBit (i % W) := by
    rw [Nat.testBit_mod_two_pow]
    simp [Nat.mod_lt _ hW]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_decide] at h1
  have hb1 : N % 2 ^ W / 2 ^ (i % W) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hb2 : N / 2 ^ (i % W) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [base]
  omega

theorem bitAt_lt_two (x : List ℕ) (i : ℕ) : bitAt x i < 2 :=
  Nat.mod_lt _ (by norm_num)

/-! ## Bit windows

Two shapes of "read a range of bits" are needed by the IR layer, and both reduce to
the same little-endian Horner fold:

* a digit written from the bits of a field element (`readBitsAt`), and
* a limb of `B` bits read back out of a digit list (`limbF`), which the u64 sort
  cannot hold in one piece once `B` exceeds 64 (an RSA limb is 121 bits wide), so it
  is assembled from `W`-bit chunks.

`bitWindow` is the fold, `winChunks` the chunked assembly. Both are stated over an
abstract bit function so the u64 program can mirror them step for step. -/

/-- `Σ_{i<w} 2^i · b (lo + i)`, as a Horner fold: the u64 program mirroring it does one
multiply-by-two per bit, and every intermediate stays below `2^w`. -/
def bitWindow (b : ℕ → ℕ) (lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => b lo + 2 * bitWindow b (lo + 1) w

theorem bitWindow_lt {b : ℕ → ℕ} (hb : ∀ i, b i < 2) (lo w : ℕ) :
    bitWindow b lo w < 2 ^ w := by
  induction w generalizing lo with
  | zero => simp [bitWindow]
  | succ w ih =>
    have h1 := hb lo
    have h2 := ih (lo + 1)
    have h3 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    rw [bitWindow, h3]
    omega

/-- On the actual bits of a number the fold is the window it names. -/
theorem bitWindow_bits (v : ℕ) (lo w : ℕ) :
    bitWindow (fun i => v / 2 ^ i % 2) lo w = v / 2 ^ lo % 2 ^ w := by
  induction w generalizing lo with
  | zero => simp [bitWindow, Nat.mod_one]
  | succ w ih =>
    have e1 : v / 2 ^ (lo + 1) = v / 2 ^ lo / 2 := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
    have e2 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    rw [bitWindow, ih (lo + 1), e1, e2, Nat.mod_mul]

/-- The number of `W`-bit chunks a `B`-bit limb needs. -/
def numChunks (B : ℕ) : ℕ := (B + W - 1) / W

theorem le_numChunks (B : ℕ) : B ≤ W * numChunks B := by rw [numChunks, W]; omega

/-- A `B`-bit window of `v` starting at bit `lo`, assembled from `c` chunks of `W`
bits, least significant chunk first. -/
def winChunks (v lo B : ℕ) : ℕ → ℕ
  | 0 => 0
  | c + 1 => v / 2 ^ lo % 2 ^ min W B + 2 ^ W * winChunks v (lo + W) (B - W) c

theorem winChunks_eq (v : ℕ) (c : ℕ) : ∀ lo B : ℕ, B ≤ W * c →
    winChunks v lo B c = v / 2 ^ lo % 2 ^ B := by
  induction c with
  | zero => intro lo B hB; have : B = 0 := by omega
            subst this; simp [winChunks, Nat.mod_one]
  | succ c ih =>
    intro lo B hB
    have hmul : W * (c + 1) = W * c + W := by ring
    rw [hmul] at hB
    rcases Nat.le_total B W with h | h
    · have hz : B - W = 0 := by omega
      rw [winChunks, min_eq_right h, ih (lo + W) (B - W) (by omega), hz]
      simp [Nat.mod_one]
    · have e1 : v / 2 ^ (lo + W) = v / 2 ^ lo / 2 ^ W := by
        rw [pow_add, ← Nat.div_div_eq_div_mul]
      have e2 : (2 : ℕ) ^ B = 2 ^ W * 2 ^ (B - W) := by
        rw [← pow_add]; congr 1; omega
      rw [winChunks, min_eq_left h, ih (lo + W) (B - W) (by omega), e1, e2, Nat.mod_mul]

/-- Bit `j` of `v`'s `nbits`-wide low window shifted up by `off`. This is the spec
`readBitsAt` is proved against: inside the window the program reads bit `j - off` of
the source field element, outside it writes a zero. -/
theorem bit_shifted_window (v off nbits j : ℕ) :
    v % 2 ^ nbits * 2 ^ off / 2 ^ j % 2
      = if off ≤ j ∧ j < off + nbits then v / 2 ^ (j - off) % 2 else 0 := by
  rw [← Nat.toNat_testBit, Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow]
  by_cases h1 : off ≤ j
  · by_cases h2 : j < off + nbits
    · have h3 : j - off < nbits := by omega
      rw [if_pos ⟨h1, h2⟩]
      simp [h1, h3, Nat.toNat_testBit]
    · have h3 : ¬ j - off < nbits := by omega
      rw [if_neg (by omega)]
      simp [h1, h3]
  · rw [if_neg (by omega)]
    simp [h1]

theorem two_pow_le_base_numChunks (X : ℕ) : 2 ^ X ≤ base ^ numChunks X := by
  rw [base_pow]
  exact Nat.pow_le_pow_right (by norm_num) (le_numChunks X)

/-! ## Binary long division

One bit of the dividend per step, most significant first: shift it into the remainder
register, and subtract the divisor if it fits. `subbOut` answers "does it fit?", so the
step is one shift and one subtraction — no comparison pass and no quotient-digit
estimation, which is what keeps the invariant to a few lines.
-/

/-- One step of binary long division, with the quotient register shifted in lockstep. -/
def divStep (n : List ℕ) (bit : ℕ) (st : List ℕ × List ℕ) : List ℕ × List ℕ :=
  if subbOut (shl1 st.2 bit) n 0 = 0 then
    (shl1 st.1 1, subb (shl1 st.2 bit) n 0)
  else
    (shl1 st.1 0, shl1 st.2 bit)

/-- A shift whose result fits in the register loses nothing off the top. -/
theorem shl1Out_eq_zero {r : List ℕ} {bit : ℕ} (hr : Bounded r) (hbit : bit < 2)
    (hfit : 2 * lval r + bit < base ^ r.length) : shl1Out r bit = 0 := by
  have hv := lval_shl1 r bit
  have hlt : lval (shl1 r bit) < base ^ r.length := by
    have := lval_lt (bounded_shl1 r bit hr hbit)
    rwa [length_shl1] at this
  have hpos : 1 ≤ base ^ r.length := Nat.one_le_pow _ _ base_pos
  rcases Nat.eq_zero_or_pos (shl1Out r bit) with h | h
  · exact h
  · exfalso
    have : base ^ r.length * 1 ≤ base ^ r.length * shl1Out r bit :=
      Nat.mul_le_mul_left _ h
    omega

/-- The borrow out of the trial subtraction *is* the comparison. -/
theorem subbOut_eq_zero_iff {s n : List ℕ} (hs : Bounded s) (hn : Bounded n)
    (hlen : n.length ≤ s.length) : subbOut s n 0 = 0 ↔ lval n ≤ lval s := by
  have hv := lval_subb s n 0 hs hn (by norm_num) hlen
  have hout := subbOut_lt s n 0 (by norm_num)
  have hsub : lval (subb s n 0) < base ^ s.length := by
    have := lval_lt (bounded_subb s n 0 hs hn (by norm_num))
    rwa [length_subb] at this
  have hpos : 1 ≤ base ^ s.length := Nat.one_le_pow _ _ base_pos
  have hslt : lval s < base ^ s.length := lval_lt hs
  constructor
  · intro h; rw [h] at hv; omega
  · intro h
    rcases Nat.lt_or_ge (subbOut s n 0) 1 with h1 | h1
    · omega
    · exfalso
      have : base ^ s.length * 1 ≤ base ^ s.length * subbOut s n 0 :=
        Nat.mul_le_mul_left _ h1
      omega

/-- The unconditional value of a subtraction pass: the borrow out is absorbed by one
reduction modulo the register width. -/
theorem lval_subb_mod {x y : List ℕ} (hx : Bounded x) (hy : Bounded y)
    (hlen : y.length ≤ x.length) :
    lval (subb x y 0) = (lval x + base ^ x.length - lval y) % base ^ x.length := by
  have hv := lval_subb x y 0 hx hy (by norm_num) hlen
  have hout := subbOut_lt x y 0 (by norm_num)
  have hd : lval (subb x y 0) < base ^ x.length := by
    have := lval_lt (bounded_subb x y 0 hx hy (by norm_num))
    rwa [length_subb] at this
  have hylt : lval y < base ^ x.length :=
    lt_of_lt_of_le (lval_lt hy) (Nat.pow_le_pow_right base_pos hlen)
  rcases (show subbOut x y 0 = 0 ∨ subbOut x y 0 = 1 by omega) with h | h
  · rw [h, Nat.mul_zero] at hv
    rw [show lval x + base ^ x.length - lval y = base ^ x.length + lval (subb x y 0) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · rw [h, Nat.mul_one] at hv
    rw [show lval x + base ^ x.length - lval y = lval (subb x y 0) by omega,
      Nat.mod_eq_of_lt hd]

/-- No borrow out means the subtraction really was the difference. -/
theorem lval_subb_of_le {x y : List ℕ} (hx : Bounded x) (hy : Bounded y)
    (hlen : y.length ≤ x.length) (hle : lval y ≤ lval x) :
    lval (subb x y 0) = lval x - lval y := by
  have hv := lval_subb x y 0 hx hy (by norm_num) hlen
  rw [(subbOut_eq_zero_iff hx hy hlen).mpr hle] at hv
  omega

/-- Division is determined by a decomposition with a small remainder. -/
theorem div_mod_unique {N k d m : ℕ} (hN : 0 < N) (hd : d < N) (h : m = N * k + d) :
    m / N = k ∧ m % N = d := by
  subst h
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hN, Nat.div_eq_of_lt hd, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hd]

theorem divStep_bounded {n : List ℕ} {bit : ℕ} {q r : List ℕ}
    (hn : Bounded n) (hq : Bounded q) (hr : Bounded r) (hbit : bit < 2) :
    Bounded (divStep n bit (q, r)).1 ∧ Bounded (divStep n bit (q, r)).2
      ∧ (divStep n bit (q, r)).1.length = q.length
      ∧ (divStep n bit (q, r)).2.length = r.length := by
  have hs := bounded_shl1 r bit hr hbit
  rw [divStep]
  split
  · exact ⟨bounded_shl1 q 1 hq (by norm_num), bounded_subb _ n 0 hs hn (by norm_num),
      length_shl1 q 1, by rw [length_subb, length_shl1]⟩
  · exact ⟨bounded_shl1 q 0 hq (by norm_num), hs, length_shl1 q 0, length_shl1 r bit⟩

/-- One step advances the quotient and remainder by one bit of the dividend. -/
theorem divStep_spec {n : List ℕ} {bit : ℕ} {q r : List ℕ} {P : ℕ}
    (hn : Bounded n) (hq : Bounded q) (hr : Bounded r) (hbit : bit < 2)
    (hnpos : 0 < lval n) (hnlen : n.length ≤ r.length)
    (hqv : lval q = P / lval n) (hrv : lval r = P % lval n)
    (hrfit : 2 * lval r + bit < base ^ r.length)
    (hqfit : 2 * lval q + 1 < base ^ q.length) :
    lval (divStep n bit (q, r)).1 = (2 * P + bit) / lval n ∧
      lval (divStep n bit (q, r)).2 = (2 * P + bit) % lval n := by
  have hs : Bounded (shl1 r bit) := bounded_shl1 r bit hr hbit
  have hslen : (shl1 r bit).length = r.length := length_shl1 r bit
  have hsv : lval (shl1 r bit) = 2 * lval r + bit := by
    have := lval_shl1 r bit
    rw [shl1Out_eq_zero hr hbit hrfit] at this
    omega
  have hqsv : lval (shl1 q 1) = 2 * lval q + 1 := by
    have := lval_shl1 q 1
    rw [shl1Out_eq_zero hq (by norm_num) (by omega)] at this
    omega
  have hq0v : lval (shl1 q 0) = 2 * lval q := by
    have := lval_shl1 q 0
    rw [shl1Out_eq_zero hq (by norm_num) (by omega)] at this
    omega
  have hcmp := subbOut_eq_zero_iff hs hn (by omega)
  have hdm := Nat.div_add_mod P (lval n)
  rw [← hqv, ← hrv] at hdm
  have hrlt : lval r < lval n := by rw [hrv]; exact Nat.mod_lt _ hnpos
  rw [divStep]
  split
  · rename_i hz
    have hge : lval n ≤ lval (shl1 r bit) := hcmp.mp hz
    have hsub := lval_subb (shl1 r bit) n 0 hs hn (by norm_num) (by omega)
    rw [hz] at hsub
    have hexp : lval n * (2 * lval q + 1) = 2 * (lval n * lval q) + lval n := by ring
    have hdec : 2 * P + bit = lval n * (2 * lval q + 1)
        + lval (subb (shl1 r bit) n 0) := by omega
    obtain ⟨h1, h2⟩ := div_mod_unique hnpos (by omega) hdec
    exact ⟨by rw [hqsv, h1], h2.symm⟩
  · rename_i hz
    have hlt : lval (shl1 r bit) < lval n := by
      by_contra hcon
      exact hz (hcmp.mpr (by omega))
    have hexp : lval n * (2 * lval q) = 2 * (lval n * lval q) := by ring
    have hdec : 2 * P + bit = lval n * (2 * lval q) + lval (shl1 r bit) := by omega
    obtain ⟨h1, h2⟩ := div_mod_unique hnpos hlt hdec
    exact ⟨by rw [hq0v, h1], h2.symm⟩

/-! ### The loop -/

theorem lval_replicate_zero : ∀ k : ℕ, lval (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by simp only [List.replicate_succ, lval_cons, lval_replicate_zero k, Nat.mul_zero]

theorem bounded_replicate_zero (k : ℕ) : Bounded (List.replicate k 0) := by
  intro d hd
  rw [List.eq_of_mem_replicate hd]
  exact base_pos

/-- `j` steps of binary long division, consuming the top `j` bits of the dividend. -/
def divIter (n x : List ℕ) (bits : ℕ) (q r : List ℕ) : ℕ → List ℕ × List ℕ
  | 0 => (q, r)
  | j + 1 => divStep n (bitAt x (bits - 1 - j)) (divIter n x bits q r j)

/-- After `j` steps the two registers hold the quotient and remainder of the dividend's
top `j` bits. At `j = bits` that is the quotient and remainder of the whole dividend. -/
theorem divIter_spec (n x : List ℕ) (bits qlen rlen : ℕ)
    (hn : Bounded n) (hx : Bounded x) (hnpos : 0 < lval n)
    (hnlen : n.length < rlen) (hxb : lval x < 2 ^ bits)
    (hqbig : 2 ^ bits ≤ base ^ qlen) :
    ∀ j, j ≤ bits →
      Bounded (divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) j).1
      ∧ Bounded (divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) j).2
      ∧ (divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) j).1.length = qlen
      ∧ (divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) j).2.length = rlen
      ∧ lval (divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) j).1
          = lval x / 2 ^ (bits - j) / lval n
      ∧ lval (divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) j).2
          = lval x / 2 ^ (bits - j) % lval n := by
  intro j
  induction j with
  | zero =>
    intro _
    have hz : lval x / 2 ^ bits = 0 := Nat.div_eq_of_lt hxb
    refine ⟨bounded_replicate_zero _, bounded_replicate_zero _,
      by simp [divIter], by simp [divIter], ?_, ?_⟩
    · simp [divIter, lval_replicate_zero, hz]
    · simp [divIter, lval_replicate_zero, hz]
  | succ j ih =>
    intro hj
    obtain ⟨hbq, hbr, hlq, hlr, hvq, hvr⟩ := ih (by omega)
    set st := divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) j with hst
    set P := lval x / 2 ^ (bits - j) with hP
    have hbit := bitAt_lt_two x (bits - 1 - j)
    -- the remainder register is wide enough for one more doubling
    have hrn : lval n ≤ base ^ n.length := le_of_lt (lval_lt hn)
    have hrlt : lval st.2 < lval n := by rw [hvr]; exact Nat.mod_lt _ hnpos
    have hpow : base ^ n.length * base ≤ base ^ rlen := by
      calc base ^ n.length * base = base ^ (n.length + 1) := by rw [pow_succ]
        _ ≤ base ^ rlen := Nat.pow_le_pow_right base_pos (by omega)
    have hb2 : 2 * base ^ n.length ≤ base ^ n.length * base := by
      have : 2 ≤ base := by rw [base_eq]; norm_num
      calc 2 * base ^ n.length = base ^ n.length * 2 := Nat.mul_comm _ _
        _ ≤ base ^ n.length * base := Nat.mul_le_mul_left _ this
    have hrfit : 2 * lval st.2 + bitAt x (bits - 1 - j) < base ^ st.2.length := by
      rw [hlr]; omega
    -- the quotient register is wide enough too
    have hPlt : P < 2 ^ j := by
      rw [hP]
      have hsplit : (2 : ℕ) ^ bits = 2 ^ (bits - j) * 2 ^ j := by
        rw [← pow_add]; congr 1; omega
      exact Nat.div_lt_of_lt_mul (by rw [← hsplit] at *; omega)
    have hqle : lval st.1 ≤ P := by
      rw [hvq]; exact Nat.div_le_self _ _
    have hpj : 2 ^ (j + 1) ≤ 2 ^ bits := Nat.pow_le_pow_right (by norm_num) hj
    have hqfit : 2 * lval st.1 + 1 < base ^ st.1.length := by
      rw [hlq]
      have : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
      omega
    -- the next bit of the dividend
    have hbitv : bitAt x (bits - 1 - j) = lval x / 2 ^ (bits - 1 - j) % 2 :=
      lval_bitAt x hx _
    have hidx : bits - 1 - j = bits - (j + 1) := by omega
    have hstep : lval x / 2 ^ (bits - (j + 1))
        = 2 * P + bitAt x (bits - 1 - j) := by
      rw [hbitv, hidx, hP]
      have hsucc : bits - j = (bits - (j + 1)) + 1 := by omega
      rw [hsucc, pow_succ, ← Nat.div_div_eq_div_mul]
      omega
    obtain ⟨hbq', hbr', hlq', hlr'⟩ :=
      divStep_bounded (n := n) (bit := bitAt x (bits - 1 - j)) (q := st.1) (r := st.2)
        hn hbq hbr hbit
    obtain ⟨h1, h2⟩ :=
      divStep_spec (n := n) (bit := bitAt x (bits - 1 - j)) (q := st.1) (r := st.2) (P := P)
        hn hbq hbr hbit hnpos (by omega) hvq hvr hrfit hqfit
    have hdi : divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) (j + 1)
        = divStep n (bitAt x (bits - 1 - j)) (st.1, st.2) := by
      rw [divIter, ← hst]
    rw [hdi]
    exact ⟨hbq', hbr', by omega, by omega, by rw [h1, ← hstep], by rw [h2, ← hstep]⟩

/-- Quotient and remainder of `x` by `n` as digit lists: the loop run to completion. -/
def divmod (n x : List ℕ) (qlen rlen bits : ℕ) : List ℕ × List ℕ :=
  divIter n x bits (List.replicate qlen 0) (List.replicate rlen 0) bits

/-- The headline fact: the two registers hold `x / n` and `x % n`. -/
theorem divmod_spec (n x : List ℕ) (bits qlen rlen : ℕ)
    (hn : Bounded n) (hx : Bounded x) (hnpos : 0 < lval n)
    (hnlen : n.length < rlen) (hxb : lval x < 2 ^ bits)
    (hqbig : 2 ^ bits ≤ base ^ qlen) :
    Bounded (divmod n x qlen rlen bits).1 ∧ Bounded (divmod n x qlen rlen bits).2
      ∧ (divmod n x qlen rlen bits).1.length = qlen
      ∧ (divmod n x qlen rlen bits).2.length = rlen
      ∧ lval (divmod n x qlen rlen bits).1 = lval x / lval n
      ∧ lval (divmod n x qlen rlen bits).2 = lval x % lval n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    divIter_spec n x bits qlen rlen hn hx hnpos hnlen hxb hqbig bits (le_refl _)
  rw [Nat.sub_self, pow_zero, Nat.div_one] at h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! ## Exponents as bit lists, and Fermat's inverse

Square-and-multiply drives its recursion off a little-endian bit list rather than off
the exponent itself: the exponent is a compile-time constant (`P256 - 2`), so unfolding
it into bits once, here, keeps the *program* a plain structural recursion. The two
modular-power identities below are the two steps of that recursion, and the Fermat
lemma is what makes the chain an inverse.
-/

/-- A little-endian bit list as a number. -/
def ofBitsLE : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * ofBitsLE bs + (if b then 1 else 0)

/-- The `len` low bits of `n`, least-significant first. -/
def bitsLE : ℕ → ℕ → List Bool
  | 0, _ => []
  | len + 1, n => decide (n % 2 = 1) :: bitsLE len (n / 2)

/-- `bitsLE` is a faithful little-endian encoding of any number it has room for. -/
theorem ofBitsLE_bitsLE (len n : ℕ) (h : n < 2 ^ len) : ofBitsLE (bitsLE len n) = n := by
  induction len generalizing n with
  | zero => simp only [pow_zero, Nat.lt_one_iff] at h; simp [bitsLE, ofBitsLE, h]
  | succ len ih =>
      have hdiv : n / 2 < 2 ^ len := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        calc n < 2 ^ (len + 1) := h
          _ = 2 ^ len * 2 := by ring
      have h2 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
      have := Nat.div_add_mod n 2
      simp only [bitsLE, ofBitsLE, ih _ hdiv]
      rcases h2 with h2 | h2 <;> simp [h2] <;> omega

/-- The squaring step: squaring a reduced power and reducing again doubles the
exponent. -/
theorem sq_mod_pow (a e m : ℕ) : a ^ e % m * (a ^ e % m) % m = a ^ (2 * e) % m := by
  have h : a ^ e % m * (a ^ e % m) ≡ a ^ e * a ^ e [MOD m] :=
    Nat.ModEq.mul (Nat.mod_modEq _ _) (Nat.mod_modEq _ _)
  calc a ^ e % m * (a ^ e % m) % m = a ^ e * a ^ e % m := h
    _ = a ^ (2 * e) % m := by rw [← pow_add, two_mul]

/-- The multiply step: multiplying a reduced power by the base and reducing again
increments the exponent. -/
theorem mul_mod_pow_succ (a e m : ℕ) : a ^ e % m * a % m = a ^ (e + 1) % m := by
  have h : a ^ e % m * a ≡ a ^ e * a [MOD m] := (Nat.mod_modEq _ _).mul_right a
  calc a ^ e % m * a % m = a ^ e * a % m := h
    _ = a ^ (e + 1) % m := by rw [pow_succ]

/-- For a prime `q > 2` and **any** `y`, Fermat's exponentiation is the inverse in
`ZMod q`. Unconditional in `y`: at `y ≡ 0` both sides are `0`, which matters because a
caller's denominator may be zero. -/
theorem pow_sub_two_mod_eq_inv_val {q : ℕ} [Fact q.Prime] (hq : 2 < q) (y : ℕ) :
    y ^ (q - 2) % q = ((y : ZMod q)⁻¹).val := by
  have : NeZero q := ⟨by omega⟩
  rw [← ZMod.val_natCast, Nat.cast_pow]
  congr 1
  by_cases hy : (y : ZMod q) = 0
  · rw [hy, zero_pow (by omega), inv_zero]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show q - 2 + 1 = q - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one hy

end WitgenNat
end Solution.Secp256k1ScalarMul
