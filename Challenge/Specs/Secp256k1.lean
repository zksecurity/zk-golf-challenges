import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Specs.ShortWeierstrass

/-- A short Weierstrass curve `y² = x³ + a·x + b` over `F`. -/
structure Curve (F : Type) where
  a : F
  b : F

/-- An affine point (the point at infinity is not affine; see `GroupPoint`). -/
structure Point (F : Type) where
  x : F
  y : F
deriving DecidableEq

/-- A point of the curve group: the point at infinity 𝒪 (the identity) or an
affine point. -/
inductive GroupPoint (F : Type) where
  /-- The point at infinity 𝒪, the identity of the group. -/
  | infinity
  /-- An affine point. -/
  | affine (P : Point F)
deriving DecidableEq

variable {F : Type} [Field F]

/-- `P` lies on the curve. -/
@[reducible] def OnCurve (c : Curve F) (P : Point F) : Prop :=
  P.y ^ 2 = P.x ^ 3 + c.a * P.x + c.b

/-- A group point is valid for the curve when it is either infinity or an
affine point on the curve. -/
@[reducible] def OnCurveOrInfinity (c : Curve F) : GroupPoint F → Prop
  | .infinity => True
  | .affine P => OnCurve c P

/-- There are no affine points of order two. For these short
Weierstrass coordinates, that means no affine on-curve point has `y = 0`. -/
@[reducible] def NoOrderTwo (c : Curve F) : Prop :=
  ∀ P : Point F, OnCurve c P → P.y ≠ 0

/-- The chord rule: affine addition for points with distinct x-coordinates
(incomplete; `add` applies it only there). -/
def chord (P Q : Point F) : Point F :=
  let slope := (Q.y - P.y) / (Q.x - P.x)
  let x := slope ^ 2 - P.x - Q.x
  { x := x, y := slope * (P.x - x) - P.y }

/-- The tangent rule: affine doubling for points with `y ≠ 0` (incomplete;
`add` applies it only there). -/
def tangent (c : Curve F) (P : Point F) : Point F :=
  let slope := (3 * P.x ^ 2 + c.a) / (2 * P.y)
  let x := slope ^ 2 - 2 * P.x
  { x := x, y := slope * (P.x - x) - P.y }

/-- Closure of the chord formula for curves of the form `y² = x³ + b`. -/
theorem chord_onCurve_cubic {K : Type} [Field K] {x1 y1 x2 y2 s x3 y3 b : K}
    (h1 : y1 ^ 2 = x1 ^ 3 + b) (h2 : y2 ^ 2 = x2 ^ 3 + b)
    (hne : x2 - x1 ≠ 0) (hs : s * (x2 - x1) = y2 - y1)
    (hx3 : x3 = s ^ 2 - x1 - x2) (hy3 : y3 = s * (x1 - x3) - y1) :
    y3 ^ 2 = x3 ^ 3 + b := by
  subst hx3; subst hy3
  apply mul_left_cancel₀ hne
  linear_combination ((x2 - x1) - (s ^ 2 - x1 - x2 - x1)) * h1
    + (s ^ 2 - x1 - x2 - x1) * h2
    + (s ^ 2 - x1 - x2 - x1) * (y1 + y2 + s * (x2 - x1)) * hs

/-- Closure of the tangent formula for curves of the form `y² = x³ + b`. -/
theorem tangent_onCurve_cubic {K : Type} [Field K] {x1 y1 s x3 y3 b : K}
    (h1 : y1 ^ 2 = x1 ^ 3 + b) (hs : s * (2 * y1) = 3 * x1 ^ 2)
    (hx3 : x3 = s ^ 2 - x1 - x1) (hy3 : y3 = s * (x1 - x3) - y1) :
    y3 ^ 2 = x3 ^ 3 + b := by
  subst hx3; subst hy3
  linear_combination h1 + (s ^ 2 - x1 - x1 - x1) * hs

/-- The complete group law: the chord/tangent formulas assembled by case
analysis on their exceptional cases (identity, `P + (−P) = 𝒪`, doubling),
realizing the true group operation for on-curve points. -/
def add [DecidableEq F] (c : Curve F) :
    GroupPoint F → GroupPoint F → GroupPoint F
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine P, .affine Q =>
      if P.x = Q.x then
        if P.y = -Q.y then
          .infinity
        else
          .affine (tangent c P)
      else
        .affine (chord P Q)

/-- One MSB-first double-and-add step: double the accumulator, then add the
base point `P` if the bit is set. -/
def step [DecidableEq F] (c : Curve F) (P : Point F)
    (acc : GroupPoint F) (bit : ℕ) : GroupPoint F :=
  let doubled := add c acc acc
  if bit = 1 then add c doubled (.affine P) else doubled

/-- The scalar encoded by a bit sequence, most significant bit first. -/
def scalarOfBits {n : ℕ} (bits : Vector ℕ n) : ℕ :=
  bits.foldl (fun acc bit => 2 * acc + bit) 0

/-- Naive MSB-first double-and-add: for an on-curve `P` this computes
`[scalarOfBits bits]P` (the complete `add` handles every exceptional case),
`.infinity` exactly when that multiple is 𝒪. -/
def scalarMul [DecidableEq F] (c : Curve F) {n : ℕ} (bits : Vector ℕ n)
    (P : Point F) : GroupPoint F :=
  bits.foldl (step c P) .infinity

/-- A scalar presented as a sequence of bits. -/
@[reducible] def IsBitArray {n : ℕ} (bits : Vector ℕ n) : Prop :=
  ∀ i : Fin n, bits[i] < 2

def Assumptions (c : Curve F) {n : ℕ} (bits : Vector ℕ n) (P : Point F) : Prop :=
  IsBitArray bits ∧ OnCurve c P

/-- The scalar multiplication relation. The output is a full group point
(infinity included), so the relation is satisfiable for every bit sequence. -/
def Spec [DecidableEq F] (c : Curve F) {n : ℕ} (bits : Vector ℕ n)
    (P : Point F) (output : GroupPoint F) : Prop :=
  scalarMul c bits P = output

end Specs.ShortWeierstrass


namespace Specs.Secp256k1

open Specs.ShortWeierstrass

/-- The prime `p = 2^256 - 2^32 - 977` of the secp256k1 base field. -/
def p : ℕ :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

/-- `p` is prime (axiom; a challenge instance must whitelist it in its
comparator config). -/
axiom hPrime : p.Prime

instance : Fact p.Prime := ⟨hPrime⟩

/-- The secp256k1 base field `𝔽_p`. -/
abbrev Fp : Type := ZMod p

/-- secp256k1: `y² = x³ + 7`. -/
def curve : Curve Fp := { a := 0, b := 7 }

/-- The secp256k1 curve equation, with the concrete coefficients inlined. -/
lemma onCurve_iff (P : Point Fp) :
    OnCurve curve P ↔ P.y ^ 2 = P.x ^ 3 + 7 := by
  simp [OnCurve, curve]

/-- `2 ≠ 0` in the secp256k1 base field. -/
lemma two_ne_zero_fp : (2 : Fp) ≠ 0 := by
  have h2 : ((2 : ℕ) : Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hp : 2 < p := by norm_num [p]
    exact (Nat.not_lt_of_ge hle) hp
  simpa using h2

/-- The secp256k1 chord formula lands back on the curve. -/
theorem chord_onCurve {P Q : Point Fp} (hP : OnCurve curve P)
    (hQ : OnCurve curve Q) (hx : P.x ≠ Q.x) :
    OnCurve curve (chord P Q) := by
  rcases P with ⟨px, py⟩
  rcases Q with ⟨qx, qy⟩
  rw [onCurve_iff] at hP hQ ⊢
  dsimp [chord]
  have hne : qx - px ≠ 0 := sub_ne_zero.mpr hx.symm
  exact chord_onCurve_cubic hP hQ hne (by rw [div_mul_cancel₀ _ hne]) rfl rfl

/-- The secp256k1 tangent formula lands back on the curve when the tangent
denominator is nonzero. -/
theorem tangent_onCurve {P : Point Fp} (hP : OnCurve curve P) (hy : P.y ≠ 0) :
    OnCurve curve (tangent curve P) := by
  rcases P with ⟨px, py⟩
  rw [onCurve_iff] at hP ⊢
  have hden : (2 : Fp) * py ≠ 0 := mul_ne_zero two_ne_zero_fp hy
  dsimp [tangent, curve]
  exact tangent_onCurve_cubic hP (by rw [div_mul_cancel₀ _ hden]; simp) (by ring) rfl

/-- Complete secp256k1 point addition preserves curve membership, provided
the curve has no affine order-two points. -/
theorem add_onCurve_or_infinity
    (hNoOrderTwo : NoOrderTwo curve)
    {P Q : GroupPoint Fp}
    (hP : OnCurveOrInfinity curve P) (hQ : OnCurveOrInfinity curve Q) :
    OnCurveOrInfinity curve (add curve P Q) := by
  cases P with
  | infinity =>
      simpa [OnCurveOrInfinity, add] using hQ
  | affine P =>
      cases Q with
      | infinity =>
          simpa [OnCurveOrInfinity, add] using hP
      | affine Q =>
          dsimp [OnCurveOrInfinity] at hP hQ
          change OnCurveOrInfinity curve
            (if P.x = Q.x then
              if P.y = -Q.y then .infinity else .affine (tangent curve P)
            else .affine (chord P Q))
          split
          · split
            · trivial
            · exact tangent_onCurve hP (hNoOrderTwo P hP)
          · exact chord_onCurve hP hQ ‹P.x ≠ Q.x›

/-- The standard generator `G`. -/
def G : Point Fp := {
  x := 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
  y := 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
}

/-- The prime order `n` of `G` (cofactor 1, so also the whole group's order). -/
def order : ℕ :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- Scalars are presented as 256 bits, most significant bit first. -/
@[reducible] def scalarBits : ℕ := 256

end Specs.Secp256k1


namespace Specs.Secp256k1ScalarMul

open Specs.ShortWeierstrass Specs.Secp256k1

def Assumptions (bits : Vector ℕ scalarBits) (P : Point Fp) : Prop :=
  Specs.ShortWeierstrass.Assumptions curve bits P

def Spec (bits : Vector ℕ scalarBits) (P : Point Fp)
    (output : GroupPoint Fp) : Prop :=
  Specs.ShortWeierstrass.Spec curve bits P output

end Specs.Secp256k1ScalarMul


namespace Specs.Secp256k1ScalarMulFixedBase

open Specs.ShortWeierstrass Specs.Secp256k1

def Assumptions (bits : Vector ℕ scalarBits) : Prop :=
  IsBitArray bits

def Spec (bits : Vector ℕ scalarBits) (output : GroupPoint Fp) : Prop :=
  Specs.Secp256k1ScalarMul.Spec bits G output

end Specs.Secp256k1ScalarMulFixedBase
