import Challenge.Specs.ShortWeierstrass
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Specs.Secp256k1

open Specs.ShortWeierstrass

/-!
Trusted spec for the secp256k1 challenge instances. The curve-generic
group-law scaffolding lives in `Challenge.Specs.ShortWeierstrass`; this file
pins secp256k1's parameters and derives the challenge-level assumptions and
relation.
-/


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
