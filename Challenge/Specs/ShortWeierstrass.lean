import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Specs.ShortWeierstrass

/-!
Curve-generic scaffolding shared by the short-Weierstrass challenge specs
(secp256k1, BLS12-381 G1, ...): affine points, the complete group law, and
the naive double-and-add relation a solution must reproduce. Curve-specific
parameters (prime, coefficients, generator, order) live in the per-curve
spec files.
-/

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

/-!
## The group law via Mathlib's Weierstrass curves

`add` above is the complete group law, but proving its algebraic laws
(commutativity, associativity, and the scalar-multiplication homomorphism
lemmas built on them) case-by-case is a large endeavor. Mathlib formalizes
the group law for general Weierstrass curves, so instead of redoing it we
transport our points into Mathlib's `WeierstrassCurve.Affine.Point`, which
carries an `AddCommGroup` structure, and pull the algebraic facts back.

The transport covers curves of the form `y² = x³ + b` (the shape of both the
secp256k1 and BLS12-381 G1 challenges) over a field of characteristic other
than 2 or 3 with `b ≠ 0` — enough for every on-curve point to be
nonsingular. The upshot is `curveNsmul_mul`: the `n`-fold sum of a curve
point is multiplicative in `n`, the lemma subgroup arguments are built on.
-/

namespace Specs.ShortWeierstrass

open WeierstrassCurve.Affine

variable {F : Type} [Field F] [DecidableEq F]

/-- The curve `y² = x³ + b` as a Mathlib `WeierstrassCurve` (all
intermediate Weierstrass coefficients zero). -/
def weierstrassCurveOfCubic (b : F) : WeierstrassCurve F :=
  ⟨0, 0, 0, 0, b⟩

/-- The curve `y² = x³ + b` in our `Curve` form. -/
def cubicCurve (b : F) : Curve F :=
  { a := 0, b := b }

lemma equation_weierstrassCurveOfCubic (b x y : F) :
    (WeierstrassCurve.Affine.Equation (weierstrassCurveOfCubic b) x y) ↔ y ^ 2 = x ^ 3 + b := by
  rw [WeierstrassCurve.Affine.equation_iff']
  constructor
  · intro hcon
    simp only [weierstrassCurveOfCubic, zero_mul, mul_zero, add_zero] at hcon
    exact sub_eq_zero.mp hcon
  · intro hcon
    simp only [weierstrassCurveOfCubic, zero_mul, mul_zero, add_zero]
    rw [hcon, sub_self]

/-- Every on-curve point of `y² = x³ + b` (with `b ≠ 0`, in characteristic
other than 2 or 3) is a nonsingular point in Mathlib's sense: if `y ≠ 0` the
`2y` partial holds; if `y = 0` then `x³ = -b ≠ 0`, so the `3x²` partial
holds. -/
theorem nonsingular_weierstrassCurveOfCubic {b x y : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hb : b ≠ 0) (h : y ^ 2 = x ^ 3 + b) : (WeierstrassCurve.Affine.Nonsingular (weierstrassCurveOfCubic b) x y) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, equation_weierstrassCurveOfCubic]
  refine ⟨h, ?_⟩
  simp only [weierstrassCurveOfCubic]
  simp only [zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  by_cases hy : y = 0
  · left
    subst hy
    simp at h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_add] at h
      exact hb h.symm
    intro hcon
    rcases mul_eq_zero.mp hcon.symm with h0 | hx0
    · exact h3 h0
    · exact pow_ne_zero 2 hx hx0
  · right
    intro hcon
    have hzero : (2 : F) * y = 0 := by
      have e : (2 : F) * y = y - (-y) := by ring
      rw [e, ← hcon, sub_self]
    exact h2 ((mul_eq_zero.mp hzero).resolve_right hy)

/-- Transport an on-curve-or-infinity point into Mathlib's affine-point
group. -/
def toMathlibPoint {b : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hb : b ≠ 0) :
    (Q : GroupPoint F) → OnCurveOrInfinity (cubicCurve b) Q →
      WeierstrassCurve.Affine.Point (weierstrassCurveOfCubic b)
  | .infinity, _ => 0
  | .affine P, h =>
      .some _ _ (nonsingular_weierstrassCurveOfCubic (b := b) (x := P.x) (y := P.y) h2 h3 hb
        (by dsimp only [cubicCurve, OnCurveOrInfinity, OnCurve] at h; simpa using h))

/-- The transport is injective. -/
theorem toMathlibPoint_injective {b : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hb : b ≠ 0)
    {Q Q' : GroupPoint F} (hQ : OnCurveOrInfinity (cubicCurve b) Q)
    (hQ' : OnCurveOrInfinity (cubicCurve b) Q') :
    toMathlibPoint h2 h3 hb Q hQ = toMathlibPoint h2 h3 hb Q' hQ' → Q = Q' := by
  cases Q with
  | infinity =>
      cases Q' with
      | infinity =>
          rintro hcon
          rfl
      | affine P' =>
          rintro hcon
          dsimp only [toMathlibPoint] at hcon
          exact absurd hcon.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
  | affine P =>
      cases Q' with
      | infinity =>
          rintro hcon
          dsimp only [toMathlibPoint] at hcon
          exact absurd hcon (WeierstrassCurve.Affine.Point.some_ne_zero _)
      | affine P' =>
          rcases P with ⟨x, y⟩
          rcases P' with ⟨x', y'⟩
          rintro hcon
          dsimp only [toMathlibPoint] at hcon
          injection hcon with hx hy
          simp [hx, hy]

/-- The tangent formula stays on the curve `y² = x³ + b` (when the doubled
point has `y ≠ 0`, which in characteristic other than 2 is exactly what the
complete `add` requires before entering the tangent branch). -/
theorem tangent_onCurve_cubicCurve {b : F} (h2 : (2 : F) ≠ 0) {P : Point F}
    (hP : OnCurve (cubicCurve b) P) (hy : P.y ≠ 0) :
    OnCurve (cubicCurve b) (tangent (cubicCurve b) P) := by
  have hP' : P.y ^ 2 = P.x ^ 3 + (cubicCurve b).a * P.x + (cubicCurve b).b := hP
  simp only [cubicCurve, zero_mul, add_zero] at hP'
  show (tangent (cubicCurve b) P).y ^ 2
      = (tangent (cubicCurve b) P).x ^ 3
        + (cubicCurve b).a * (tangent (cubicCurve b) P).x + (cubicCurve b).b
  simp only [tangent, cubicCurve, zero_mul, add_zero]
  have hs : (3 * P.x ^ 2 / (2 * P.y)) * (2 * P.y) = 3 * P.x ^ 2 :=
    div_mul_cancel₀ _ (mul_ne_zero h2 hy)
  exact tangent_onCurve_cubic hP' hs (by ring) rfl

/-- The chord formula stays on the curve `y² = x³ + b`. -/
theorem chord_onCurve_cubicCurve {b : F} {P Q : Point F}
    (hP : OnCurve (cubicCurve b) P) (hQ : OnCurve (cubicCurve b) Q) (hx : P.x ≠ Q.x) :
    OnCurve (cubicCurve b) (chord P Q) := by
  have hP' : P.y ^ 2 = P.x ^ 3 + (cubicCurve b).a * P.x + (cubicCurve b).b := hP
  have hQ' : Q.y ^ 2 = Q.x ^ 3 + (cubicCurve b).a * Q.x + (cubicCurve b).b := hQ
  simp only [cubicCurve, zero_mul, add_zero] at hP' hQ'
  show (chord P Q).y ^ 2
      = (chord P Q).x ^ 3 + (cubicCurve b).a * (chord P Q).x + (cubicCurve b).b
  simp only [chord, cubicCurve, zero_mul, add_zero]
  exact chord_onCurve_cubic hP' hQ' (sub_ne_zero.mpr hx.symm)
    (div_mul_cancel₀ _ (sub_ne_zero.mpr hx.symm)) rfl rfl

/-- Closure of the complete group law for `y² = x³ + b`: the sum of two
on-curve-or-infinity points stays on the curve or at infinity. The tangent
case needs only `P.y ≠ 0`, which follows from the two on-curve hypotheses
and the branch condition: both points share `x`, so `Q.y² = P.y²`, and
`P.y ≠ -Q.y` rules out `P.y = 0`. -/
theorem add_onCurveOrInfinity {b : F} (h2 : (2 : F) ≠ 0) {P Q : GroupPoint F}
    (hP : OnCurveOrInfinity (cubicCurve b) P) (hQ : OnCurveOrInfinity (cubicCurve b) Q) :
    OnCurveOrInfinity (cubicCurve b) (add (cubicCurve b) P Q) := by
  cases P with
  | infinity => simpa [add, OnCurveOrInfinity] using hQ
  | affine P =>
      cases Q with
      | infinity => simpa [add, OnCurveOrInfinity] using hP
      | affine Q =>
          dsimp only [cubicCurve, OnCurveOrInfinity] at hP hQ
          change OnCurveOrInfinity (cubicCurve b)
            (if P.x = Q.x then
              if P.y = -Q.y then .infinity else .affine (tangent (cubicCurve b) P)
            else .affine (chord P Q))
          by_cases hx : P.x = Q.x
          · by_cases hy : P.y = -Q.y
            · rw [if_pos hx, if_pos hy]
              exact trivial
            · have hPy : P.y ≠ 0 := by
                intro hPy0
                apply hy
                have hQy : Q.y ^ 2 = 0 := by
                  rw [hQ, ← hx, ← hP, hPy0]
                  norm_num
                have hQ0 : Q.y = 0 :=
                  pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hQy
                rw [hPy0, hQ0]
                simp
              rw [if_pos hx, if_neg hy]
              exact tangent_onCurve_cubicCurve h2 hP hPy
          · rw [if_neg hx]
            exact chord_onCurve_cubicCurve hP hQ hx

/-- `[n]Q` on the curve `c`: double-and-add over the binary digits of `n`
(most significant first), so evaluation takes O(log n) group operations. -/
def curveNsmul (c : Curve F) (n : ℕ) (Q : GroupPoint F) : GroupPoint F :=
  match Q with
  | .infinity => .infinity
  | .affine P => (Nat.digits 2 n).reverse.foldl (step c P) .infinity

lemma digits_reverse_double {n : ℕ} (hn : n ≠ 0) :
    (Nat.digits 2 (2 * n)).reverse = (Nat.digits 2 n).reverse ++ [0] := by
  rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits, Nat.bit0_bits n hn]
  simp [List.reverse_cons]

lemma digits_reverse_succ (n : ℕ) :
    (Nat.digits 2 (2 * n + 1)).reverse = (Nat.digits 2 n).reverse ++ [1] := by
  rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits, Nat.bit1_bits]
  simp [List.reverse_cons]

/-- Doubling the scalar doubles the point. -/
theorem curveNsmul_double (c : Curve F) (n : ℕ) (Q : GroupPoint F) :
    curveNsmul c (2 * n) Q = add c (curveNsmul c n Q) (curveNsmul c n Q) := by
  cases Q with
  | infinity => simp [curveNsmul, add]
  | affine P =>
      by_cases hn : n = 0
      · subst hn
        simp [curveNsmul, Nat.digits_zero, add]
      · show (Nat.digits 2 (2 * n)).reverse.foldl (step c P) .infinity
          = add c ((Nat.digits 2 n).reverse.foldl (step c P) .infinity)
              ((Nat.digits 2 n).reverse.foldl (step c P) .infinity)
        rw [digits_reverse_double hn, List.foldl_append]
        rfl

/-- The odd successor: `[2n+1]Q = [2n]Q + Q`. -/
theorem curveNsmul_succ (c : Curve F) (n : ℕ) (Q : GroupPoint F) :
    curveNsmul c (2 * n + 1) Q = add c (curveNsmul c (2 * n) Q) Q := by
  cases Q with
  | infinity => simp [curveNsmul, add]
  | affine P =>
      show (Nat.digits 2 (2 * n + 1)).reverse.foldl (step c P) .infinity
        = add c (curveNsmul c (2 * n) (.affine P)) (.affine P)
      by_cases hn : n = 0
      · subst hn
        rfl
      · rw [digits_reverse_succ n, List.foldl_append, curveNsmul_double, curveNsmul]
        rfl

/-- Two `some` points with propositionally equal coordinates are equal. -/
theorem point_some_congr {b : F} {x x' y y' : F}
    (hns : WeierstrassCurve.Affine.Nonsingular (weierstrassCurveOfCubic b) x y)
    (hns' : WeierstrassCurve.Affine.Nonsingular (weierstrassCurveOfCubic b) x' y')
    (hx : x = x') (hy : y = y') :
    (WeierstrassCurve.Affine.Point.some _ _ hns
        : WeierstrassCurve.Affine.Point (weierstrassCurveOfCubic b))
      = WeierstrassCurve.Affine.Point.some _ _ hns' := by
  subst hx
  subst hy
  rfl

/-- Transport of the addition into Mathlib's group. Stated for an abstract
result point `R` so that no `if`-expressions appear under dependent
arguments; the corollary below recovers the point-valued form. -/
theorem toMathlibPoint_add' {b : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hb : b ≠ 0)
    {P Q : GroupPoint F} (hP : OnCurveOrInfinity (cubicCurve b) P)
    (hQ : OnCurveOrInfinity (cubicCurve b) Q)
    (R : GroupPoint F) (hr : OnCurveOrInfinity (cubicCurve b) R)
    (hReq : R = add (cubicCurve b) P Q) :
    toMathlibPoint h2 h3 hb R hr
      = toMathlibPoint h2 h3 hb P hP + toMathlibPoint h2 h3 hb Q hQ := by
  cases P with
  | infinity =>
      cases Q with
      | infinity => subst hReq; simp [add, toMathlibPoint]
      | affine Q' => subst hReq; simp [add, toMathlibPoint]
  | affine P =>
      cases Q with
      | infinity => subst hReq; simp [add, toMathlibPoint]
      | affine Q =>
          obtain ⟨x₁, y₁⟩ := P
          obtain ⟨x₂, y₂⟩ := Q
          have hP' : y₁ ^ 2 = x₁ ^ 3 + b := by
            dsimp only [cubicCurve, OnCurveOrInfinity, OnCurve] at hP
            simpa using hP
          have hQ' : y₂ ^ 2 = x₂ ^ 3 + b := by
            dsimp only [cubicCurve, OnCurveOrInfinity, OnCurve] at hQ
            simpa using hQ
          have hns1 : WeierstrassCurve.Affine.Nonsingular (weierstrassCurveOfCubic b) x₁ y₁ :=
            nonsingular_weierstrassCurveOfCubic h2 h3 hb hP'
          have hns2 : WeierstrassCurve.Affine.Nonsingular (weierstrassCurveOfCubic b) x₂ y₂ :=
            nonsingular_weierstrassCurveOfCubic h2 h3 hb hQ'
          have hnegY : ∀ x y : F,
              WeierstrassCurve.Affine.negY (weierstrassCurveOfCubic b) x y = -y := by
            intro x y
            simp only [weierstrassCurveOfCubic, WeierstrassCurve.Affine.negY, zero_mul,
              zero_add, sub_zero]
          subst hReq
          simp only [add] at hr ⊢
          split_ifs at hr ⊢ with hx hy
          · simp only [toMathlibPoint]
            rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx (by rw [hnegY]; exact hy)]
          · simp only [toMathlibPoint]
            have hyneg : y₁ ≠ -y₂ := hy
            rw [WeierstrassCurve.Affine.Point.add_of_Y_ne (by rw [hnegY]; exact hyneg)]
            have hslope : WeierstrassCurve.Affine.slope (weierstrassCurveOfCubic b) x₁ x₂ y₁ y₂
                = 3 * x₁ ^ 2 / (2 * y₁) := by
              rw [WeierstrassCurve.Affine.slope_of_Y_ne hx (by rw [hnegY]; exact hyneg)]
              simp only [weierstrassCurveOfCubic, WeierstrassCurve.Affine.negY, zero_mul,
                mul_zero, zero_add, add_zero, sub_zero]
              rw [sub_neg_eq_add]
              ring
            apply point_some_congr
            · rw [hslope]
              simp only [tangent, cubicCurve, WeierstrassCurve.Affine.addX,
                weierstrassCurveOfCubic, zero_mul, mul_zero, zero_add, add_zero, hx]
              ring
            · rw [hslope]
              simp only [tangent, cubicCurve, WeierstrassCurve.Affine.addX,
                WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
                WeierstrassCurve.Affine.negY, weierstrassCurveOfCubic, zero_mul, mul_zero,
                zero_add, add_zero, sub_zero, hx]
              ring
          · simp only [toMathlibPoint]
            rw [WeierstrassCurve.Affine.Point.add_some (fun hxy => hx hxy.1)]
            have hslope : (y₂ - y₁) / (x₂ - x₁) = (y₁ - y₂) / (x₁ - x₂) := by
              rw [div_eq_div_iff (sub_ne_zero.mpr (Ne.symm hx)) (sub_ne_zero.mpr hx)] <;> ring
            apply point_some_congr
            · simp only [chord, cubicCurve, WeierstrassCurve.Affine.addX,
                weierstrassCurveOfCubic, zero_mul, mul_zero, zero_add, add_zero]
              rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hslope]
              ring
            · simp only [chord, cubicCurve, WeierstrassCurve.Affine.addX,
                WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
                WeierstrassCurve.Affine.negY, weierstrassCurveOfCubic, zero_mul, mul_zero,
                zero_add, add_zero, sub_zero]
              rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hslope]
              ring

/-- Transport of the addition into Mathlib's group, for any proof that the
sum is on the curve or at infinity (the value of `toMathlibPoint` does not
depend on the proof, by proof irrelevance). -/
theorem toMathlibPoint_add {b : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hb : b ≠ 0)
    {P Q : GroupPoint F} (hP : OnCurveOrInfinity (cubicCurve b) P)
    (hQ : OnCurveOrInfinity (cubicCurve b) Q) :
    ∀ (h' : OnCurveOrInfinity (cubicCurve b) (add (cubicCurve b) P Q)),
      toMathlibPoint h2 h3 hb (add (cubicCurve b) P Q) h'
        = toMathlibPoint h2 h3 hb P hP + toMathlibPoint h2 h3 hb Q hQ :=
  fun h' => toMathlibPoint_add' h2 h3 hb hP hQ _ h' rfl

/-- Closure: a scalar multiple of an on-curve-or-infinity point stays on
the curve or at infinity. -/
theorem curveNsmul_onCurveOrInfinity {b : F} (h2 : (2 : F) ≠ 0) :
    ∀ (n : ℕ) (Q : GroupPoint F), OnCurveOrInfinity (cubicCurve b) Q →
      OnCurveOrInfinity (cubicCurve b) (curveNsmul (cubicCurve b) n Q) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
      intro Q hQ
      by_cases hn : n = 0
      · subst hn
        cases Q with
        | infinity => exact trivial
        | affine P =>
            simp only [curveNsmul, Nat.digits_zero]
            exact trivial
      · rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · rw [← Nat.two_mul, curveNsmul_double]
          exact add_onCurveOrInfinity h2 (IH k (by omega) Q hQ) (IH k (by omega) Q hQ)
        · rw [curveNsmul_succ]
          exact add_onCurveOrInfinity h2 (IH (2 * k) (by omega) Q hQ) hQ

/-- Transport of `[n]Q` into Mathlib's group: a point `R` equal to `[n]Q`
maps to `n • φ(Q)`. Stated for an abstract `R` so that no dependent proofs
block the rewriting. -/
theorem toMathlibPoint_curveNsmul_eq {b : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hb : b ≠ 0) :
    ∀ (n : ℕ) (Q : GroupPoint F) (hQ : OnCurveOrInfinity (cubicCurve b) Q)
      (R : GroupPoint F) (hr : OnCurveOrInfinity (cubicCurve b) R),
        R = curveNsmul (cubicCurve b) n Q →
          toMathlibPoint h2 h3 hb R hr = (n : ℕ) • toMathlibPoint h2 h3 hb Q hQ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
      intro Q hQ R hr hReq
      by_cases hn : n = 0
      · subst hn
        cases Q with
        | infinity =>
            have hR0 : R = .infinity := by rw [hReq]; rfl
            subst hR0
            simp [toMathlibPoint]
        | affine P =>
            have hR0 : R = .infinity := by
              rw [hReq]
              rfl
            subst hR0
            simp [toMathlibPoint]
      · rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · rw [← Nat.two_mul] at hReq ⊢
          rw [curveNsmul_double] at hReq
          subst hReq
          have hcIk := curveNsmul_onCurveOrInfinity h2 k Q hQ
          rw [toMathlibPoint_add h2 h3 hb hcIk hcIk hr, IH k (by omega) Q hQ _ hcIk rfl,
            mul_nsmul', two_nsmul]
        · rw [curveNsmul_succ] at hReq
          subst hReq
          have hcI2 := curveNsmul_onCurveOrInfinity h2 (2 * k) Q hQ
          rw [toMathlibPoint_add h2 h3 hb hcI2 hQ hr, succ_nsmul,
            IH (2 * k) (by omega) Q hQ _ hcI2 rfl]

/-- Transport of `[n]Q` into Mathlib's group: `[n]Q` maps to `n • φ(Q)`, and
the scalar-multiple of an on-curve-or-infinity point stays on the curve or
at infinity. -/
theorem toMathlibPoint_curveNsmul {b : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hb : b ≠ 0) :
    ∀ (n : ℕ) (Q : GroupPoint F) (hQ : OnCurveOrInfinity (cubicCurve b) Q),
      OnCurveOrInfinity (cubicCurve b) (curveNsmul (cubicCurve b) n Q) ∧
        ∀ (h' : OnCurveOrInfinity (cubicCurve b) (curveNsmul (cubicCurve b) n Q)),
          toMathlibPoint h2 h3 hb (curveNsmul (cubicCurve b) n Q) h'
            = (n : ℕ) • toMathlibPoint h2 h3 hb Q hQ := by
  intro n Q hQ
  exact ⟨curveNsmul_onCurveOrInfinity h2 n Q hQ,
    fun h' => toMathlibPoint_curveNsmul_eq h2 h3 hb n Q hQ _ h' rfl⟩

/-- Additivity of scalar multiplication on the curve group. -/
theorem curveNsmul_add {b : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hb : b ≠ 0)
    (u v : ℕ) (Q : GroupPoint F) (hQ : OnCurveOrInfinity (cubicCurve b) Q) :
    curveNsmul (cubicCurve b) (u + v) Q
      = add (cubicCurve b) (curveNsmul (cubicCurve b) u Q) (curveNsmul (cubicCurve b) v Q) := by
  have hT := toMathlibPoint_curveNsmul h2 h3 hb
  apply toMathlibPoint_injective h2 h3 hb (hT (u + v) Q hQ).1
    (add_onCurveOrInfinity h2 (hT u Q hQ).1 (hT v Q hQ).1)
  rw [hT (u + v) Q hQ |>.2, toMathlibPoint_add h2 h3 hb (hT u Q hQ).1 (hT v Q hQ).1,
    add_nsmul, hT u Q hQ |>.2, hT v Q hQ |>.2]

/-- Multiplicativity of scalar multiplication: `[m·k]Q = [m]([k]Q)`. -/
theorem curveNsmul_mul {b : F} (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hb : b ≠ 0)
    (m k : ℕ) (Q : GroupPoint F) (hQ : OnCurveOrInfinity (cubicCurve b) Q) :
    curveNsmul (cubicCurve b) (m * k) Q
      = curveNsmul (cubicCurve b) m (curveNsmul (cubicCurve b) k Q) := by
  have hT := toMathlibPoint_curveNsmul h2 h3 hb
  obtain ⟨hL, hLe⟩ := hT (m * k) Q hQ
  obtain ⟨hInner, hInnerEq⟩ := hT k Q hQ
  obtain ⟨hR, hRe⟩ := hT m (curveNsmul (cubicCurve b) k Q) hInner
  apply toMathlibPoint_injective h2 h3 hb hL hR
  rw [hLe, mul_nsmul', ← hInnerEq hInner, ← hRe hR]

end Specs.ShortWeierstrass