import Solution.Secp256k1ScalarMulFixedBase.Params
import Mathlib.Tactic.LinearCombination

/-!
# Complete secp256k1 point addition — supporting lemmas for `CompleteAdd`

Pure facts underpinning the `CompleteAdd` soundness/completeness proofs:

* numeric facts about the emulated prime and constant limb vectors
  (`emuOfNat`, `pConst`, `zeroConst`);
* decoded corollaries of the `MulMod` specification;
* the field dichotomies used by the flag analysis (square roots, `2 ≠ 0`);
* the **closure lemmas**: the chord and tangent formulas of the group law
  produce points on the curve (the polynomial identities behind
  `Specs.ShortWeierstrass.add`);
* `soundness_core`, the pure value-level composition argument: the muxed
  output of `CompleteAdd.main` decodes to `Specs.ShortWeierstrass.add`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompleteAdd

/-! ## Numeric facts about the emulated prime -/

lemma P256_pos : 0 < P256 := by decide

/-- The emulated prime fits in the `numLimbs · limbBits = 256` available bits. -/
lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide

/-- A limb value fits in the circuit field. -/
lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

/-! ## `limbOfNat`, `emuOfNat` and constant limb-vector facts -/

lemma limbOfNat_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos limbBits)

lemma val_limbOfNat (v k : ℕ) :
    ((limbOfNat v k : ℕ) : F circomPrime).val = limbOfNat v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNat_lt v k) two_pow_limb_lt)

lemma emuOfNat_getElem (v k : ℕ) (hk : k < numLimbs) :
    (emuOfNat v)[k]'hk = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuOfNat, Vector.getElem_ofFn]

/-- `emuOfNat` produces normalized limbs. -/
lemma emuOfNat_normalized (v : ℕ) : (emuOfNat v).Normalized limbBits := by
  intro i
  rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
  exact limbOfNat_lt v i.val

/-- `emuOfNat` denotes its argument (for values that fit in 256 bits). -/
lemma value_emuOfNat {v : ℕ} (hv : v < 2 ^ (limbBits * numLimbs)) :
    BigInt.value limbBits (emuOfNat v) = v := by
  rw [BigInt.value_eq_sum]
  have hsum : (∑ k : Fin numLimbs, ((emuOfNat v)[k]).val * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range numLimbs,
          (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
    rfl
  rw [hsum, limb_decomp_mod, Nat.mod_eq_of_lt hv]

/-- A canonical (`< P256`) `emuOfNat` is a valid emulated field element. -/
lemma fe_valid_emuOfNat {v : ℕ} (hv : v < P256) : Fe.Valid (emuOfNat v) :=
  ⟨emuOfNat_normalized v, by rw [value_emuOfNat (lt_trans hv P256_lt)]; exact hv⟩

lemma eval_emuConst_getElem (env : Environment (F circomPrime)) (v k : ℕ)
    (hk : k < numLimbs) :
    Expression.eval env ((emuConst v)[k]'hk) = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuConst]
  rw [Vector.getElem_ofFn]
  rfl

/-- Constant limb expressions evaluate to the corresponding value-level limbs
under any environment. -/
lemma eval_emuConst (env : Environment (F circomPrime)) (v : ℕ) :
    Vector.map (Expression.eval env) (emuConst v) = emuOfNat v := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, eval_emuConst_getElem env v k hk, emuOfNat_getElem v k hk]

lemma pConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) := by
  rw [pConst, eval_emuConst]
  exact emuOfNat_normalized P256

lemma pConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) pConst) = P256 := by
  rw [pConst, eval_emuConst]
  exact value_emuOfNat P256_lt

/-- The evaluated `zeroConst` is a valid emulated field element. -/
lemma fe_valid_eval_zeroConst (env : Environment (F circomPrime)) :
    Fe.Valid (Vector.map (Expression.eval env) zeroConst) := by
  rw [zeroConst, eval_emuConst]
  exact fe_valid_emuOfNat P256_pos

/-! ## Decoded corollaries of the subcircuit specs -/

/-- The decoded `MulMod` output (with modulus `P256`) is the base-field
product. -/
lemma decodeFe_of_mulmod {a b out : Emu (F circomPrime)}
    (hout : BigInt.value limbBits out
      = BigInt.value limbBits a * BigInt.value limbBits b % P256) :
    decodeFe out = decodeFe a * decodeFe b := by
  rw [decodeFe, decodeFe, decodeFe, hout, ZMod.natCast_mod, Nat.cast_mul]

/-- A normalized output reduced mod `P256` is a valid emulated field
element. -/
lemma fe_valid_of_mod {x : Emu (F circomPrime)} {v : ℕ}
    (hnorm : x.Normalized limbBits)
    (hval : BigInt.value limbBits x = v % P256) : Fe.Valid x :=
  ⟨hnorm, hval ▸ Nat.mod_lt _ P256_pos⟩

/-! ## Field dichotomies -/

/-- `2 ≠ 0` in the secp256k1 base field (its characteristic is a 256-bit
prime). -/
lemma two_ne_zero_fp : (2 : Specs.Secp256k1.Fp) ≠ 0 := by
  have h2 : ((2 : ℕ) : Specs.Secp256k1.Fp) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle : P256 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have : 2 < P256 := by decide
    omega
  simpa using h2

/-- Two field elements with equal squares agree up to sign. -/
lemma eq_or_eq_neg_of_sq_eq {K : Type} [Field K] {a b : K} (h : a ^ 2 = b ^ 2) :
    a = b ∨ a = -b := by
  have hz : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hz with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (eq_neg_of_add_eq_zero_left h')

/-! ## Closure lemmas: the chord and tangent formulas stay on the curve

Both are polynomial identities in the ideal generated by the hypotheses; the
cofactors were computed offline (Vieta on the line-curve intersection cubic).
The chord case needs one cancellation of the nonzero `x₂ − x₁`. -/

/-- **Chord closure.** If `(x₁, y₁)` and `(x₂, y₂)` lie on `y² = x³ + bb` and
have distinct x-coordinates, the chord formula with any slope `s` satisfying
`s·(x₂ − x₁) = y₂ − y₁` lands on the curve. -/
theorem chord_oncurve {K : Type} [Field K] {x₁ y₁ x₂ y₂ s x₃ y₃ bb : K}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + bb) (h₂ : y₂ ^ 2 = x₂ ^ 3 + bb)
    (hne : x₂ - x₁ ≠ 0) (hs : s * (x₂ - x₁) = y₂ - y₁)
    (hx₃ : x₃ = s * s - x₁ - x₂) (hy₃ : y₃ = s * (x₁ - x₃) - y₁) :
    y₃ ^ 2 = x₃ ^ 3 + bb := by
  subst hx₃; subst hy₃
  apply mul_left_cancel₀ hne
  linear_combination ((x₂ - x₁) - (s * s - x₁ - x₂ - x₁)) * h₁
    + (s * s - x₁ - x₂ - x₁) * h₂
    + (s * s - x₁ - x₂ - x₁) * (y₁ + y₂ + s * (x₂ - x₁)) * hs

/-- **Tangent closure.** If `(x₁, y₁)` lies on `y² = x³ + bb`, the tangent
formula with any slope `s` satisfying `s·(2y₁) = 3x₁²` lands on the curve. -/
theorem tangent_oncurve {K : Type} [Field K] {x₁ y₁ s x₃ y₃ bb : K}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + bb) (hs : s * (2 * y₁) = 3 * x₁ ^ 2)
    (hx₃ : x₃ = s * s - x₁ - x₁) (hy₃ : y₃ = s * (x₁ - x₃) - y₁) :
    y₃ ^ 2 = x₃ ^ 3 + bb := by
  subst hx₃; subst hy₃
  linear_combination h₁ + (s * s - x₁ - x₁ - x₁) * hs

/-! ## Reduction lemmas for the trusted spec and for `decodePoint` -/

open Specs.ShortWeierstrass in
lemma add_inf_left (q : GroupPoint Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve .infinity q = q := rfl

open Specs.ShortWeierstrass in
lemma add_inf_right (p : Point Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve (.affine p) .infinity = .affine p := rfl

open Specs.ShortWeierstrass in
lemma add_affine (px py qx qy : Specs.Secp256k1.Fp) :
    add Specs.Secp256k1.curve (.affine ⟨px, py⟩) (.affine ⟨qx, qy⟩)
      = if px = qx then
          (if py = -qy then .infinity
            else .affine (tangent Specs.Secp256k1.curve ⟨px, py⟩))
        else .affine (chord ⟨px, py⟩ ⟨qx, qy⟩) := rfl

open Specs.ShortWeierstrass in
/-- The secp256k1 curve equation, with the concrete coefficients inlined. -/
lemma onCurve_iff (p : Point Specs.Secp256k1.Fp) :
    OnCurve Specs.Secp256k1.curve p ↔ p.y ^ 2 = p.x ^ 3 + 7 := by
  simp [OnCurve, Specs.Secp256k1.curve]

open Specs.ShortWeierstrass in
/-- The secp256k1 tangent formula, with `a = 0` inlined. -/
lemma tangent_eq (px py : Specs.Secp256k1.Fp) :
    tangent Specs.Secp256k1.curve ⟨px, py⟩
      = { x := (3 * px ^ 2 / (2 * py)) ^ 2 - 2 * px,
          y := 3 * px ^ 2 / (2 * py)
            * (px - ((3 * px ^ 2 / (2 * py)) ^ 2 - 2 * px)) - py } := by
  simp [tangent, Specs.Secp256k1.curve]

open Specs.ShortWeierstrass in
/-- The chord formula, componentwise. -/
lemma chord_eq (px py qx qy : Specs.Secp256k1.Fp) :
    chord ⟨px, py⟩ ⟨qx, qy⟩
      = { x := ((qy - py) / (qx - px)) ^ 2 - px - qx,
          y := (qy - py) / (qx - px)
            * (px - (((qy - py) / (qx - px)) ^ 2 - px - qx)) - py } := rfl

lemma decodePoint_of_isInf {p : FlaggedPoint (F circomPrime)} (h : p.isInf = 1) :
    decodePoint p = .infinity := by
  simp only [decodePoint]
  rw [if_pos h]

lemma decodePoint_of_finite {p : FlaggedPoint (F circomPrime)} (h : p.isInf = 0) :
    decodePoint p = .affine { x := decodeFe p.x, y := decodeFe p.y } := by
  simp only [decodePoint]
  rw [if_neg (by rw [h]; exact zero_ne_one)]

lemma decodePoint_mk_zero (x y : Emu (F circomPrime)) :
    decodePoint ⟨x, y, 0⟩ = .affine { x := decodeFe x, y := decodeFe y } :=
  decodePoint_of_finite rfl

/-- Flags produced by `IsZeroFe` are boolean. -/
lemma isBool_ite {c : Prop} [Decidable c] :
    IsBool (if c then (1 : F circomPrime) else 0) := by
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- A product of boolean flags is boolean. -/
lemma isBool_mul {x y : F circomPrime} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x * y) := by
  rcases hx with h | h <;> rcases hy with h' | h' <;> rw [h, h']
  · exact Or.inl (mul_zero 0)
  · exact Or.inl (zero_mul 1)
  · exact Or.inl (mul_zero 1)
  · exact Or.inr (mul_one 1)

/-- A mux between valid emulated field elements is valid. -/
lemma fe_valid_ite {c : Prop} [Decidable c] {a b : Emu (F circomPrime)}
    (ha : Fe.Valid a) (hb : Fe.Valid b) : Fe.Valid (if c then a else b) := by
  split <;> assumption

/-- A value constrained to an `IsZeroFe`-shaped mux is boolean. -/
lemma isBool_of_eq_ite {x : F circomPrime} {c : Prop} [Decidable c]
    (h : x = if c then (1 : F circomPrime) else 0) : IsBool x := by
  rw [h]; exact isBool_ite

/-- A value constrained to a product of boolean flags is boolean. -/
lemma isBool_of_eq_mul {x a b : F circomPrime} (ha : IsBool a) (hb : IsBool b)
    (h : x = a * b) : IsBool x := by
  rw [h]; exact isBool_mul ha hb

/-- A value constrained to a mux of valid elements is valid. -/
lemma fe_valid_of_eq_ite {x : Emu (F circomPrime)} {c : Prop} [Decidable c]
    {a b : Emu (F circomPrime)} (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h : x = if c then a else b) : Fe.Valid x := by
  rw [h]; exact fe_valid_ite ha hb

/-- The `MulMod` preconditions (with modulus `pConst`) hold for canonical
operands. -/
lemma mulmod_assumptions {a b : Emu (F circomPrime)} (env : Environment (F circomPrime))
    (ha : Fe.Valid a) (hb : Fe.Valid b) :
    BigInt.Normalized limbBits a ∧ BigInt.Normalized limbBits b ∧
      BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) ∧
      BigInt.value limbBits a
        < BigInt.value limbBits (Vector.map (Expression.eval env) pConst) ∧
      BigInt.value limbBits b
        < BigInt.value limbBits (Vector.map (Expression.eval env) pConst) ∧
      0 < BigInt.value limbBits (Vector.map (Expression.eval env) pConst) := by
  refine ⟨ha.1, hb.1, pConst_normalized env, ?_, ?_, ?_⟩ <;> rw [pConst_value env]
  exacts [ha.2, hb.2, P256_pos]

/-! ## The value-level soundness core

Everything the `CompleteAdd.soundness` wiring establishes about the evaluated
intermediate values, composed into the final statement. All hypotheses are at
the level of decoded field elements / evaluated flags; no circuit plumbing
appears. -/

open Specs.ShortWeierstrass in
theorem soundness_core
    {P Q s1 s2 out infv finv : FlaggedPoint (F circomPrime)}
    {dxv dyv syv x1sqv x1sq2v tNumv tDenv numv denv lamv lamSqv xsv x3v xdv yprodv y3v
      : Emu (F circomPrime)}
    {sameX oppY cancel : F circomPrime}
    (hP : P.Valid) (hQ : Q.Valid)
    (hdx : decodeFe dxv = decodeFe Q.x - decodeFe P.x)
    (hdy : decodeFe dyv = decodeFe Q.y - decodeFe P.y)
    (hsameX : sameX = if decodeFe dxv = 0 then 1 else 0)
    (hsy : decodeFe syv = decodeFe P.y + decodeFe Q.y)
    (hoppY : oppY = if decodeFe syv = 0 then 1 else 0)
    (hx1sq : decodeFe x1sqv = decodeFe P.x * decodeFe P.x)
    (hx1sq2 : decodeFe x1sq2v = decodeFe x1sqv + decodeFe x1sqv)
    (htNum : decodeFe tNumv = decodeFe x1sq2v + decodeFe x1sqv)
    (htDen : decodeFe tDenv = decodeFe P.y + decodeFe P.y)
    (hnum : numv = if sameX = 1 then tNumv else dyv)
    (hden : denv = if sameX = 1 then tDenv else dxv)
    (hlam : decodeFe denv ≠ 0 → decodeFe lamv * decodeFe denv = decodeFe numv)
    (hlamSq : decodeFe lamSqv = decodeFe lamv * decodeFe lamv)
    (hxs : decodeFe xsv = decodeFe lamSqv - decodeFe P.x)
    (hx3v : Fe.Valid x3v) (hx3 : decodeFe x3v = decodeFe xsv - decodeFe Q.x)
    (hxd : decodeFe xdv = decodeFe P.x - decodeFe x3v)
    (hyprod : decodeFe yprodv = decodeFe lamv * decodeFe xdv)
    (hy3v : Fe.Valid y3v) (hy3 : decodeFe y3v = decodeFe yprodv - decodeFe P.y)
    (hcancel : cancel = sameX * oppY)
    (hinfx : Fe.Valid infv.x) (hinfy : Fe.Valid infv.y) (hinff : infv.isInf = 1)
    (hfin : finv = ⟨x3v, y3v, 0⟩)
    (hs1 : s1 = if cancel = 1 then infv else finv)
    (hs2 : s2 = if Q.isInf = 1 then P else s1)
    (hout : out = if P.isInf = 1 then Q else s2) :
    out.Valid ∧
      decodePoint out =
        Specs.ShortWeierstrass.add Specs.Secp256k1.curve (decodePoint P) (decodePoint Q) := by
  rcases hP.1 with hPinf | hPinf
  · -- P is finite
    have hPne1 : P.isInf ≠ 1 := by rw [hPinf]; exact zero_ne_one
    rw [hout, if_neg hPne1]
    rcases hQ.1 with hQinf | hQinf
    · -- Q is finite too: the generic affine case analysis
      have hQne1 : Q.isInf ≠ 1 := by rw [hQinf]; exact zero_ne_one
      rw [hs2, if_neg hQne1, decodePoint_of_finite hPinf, decodePoint_of_finite hQinf,
        add_affine]
      have hPc : decodeFe P.y ^ 2 = decodeFe P.x ^ 3 + 7 :=
        (onCurve_iff _).mp (hP.2.2.2 hPinf)
      have hQc : decodeFe Q.y ^ 2 = decodeFe Q.x ^ 3 + 7 :=
        (onCurve_iff _).mp (hQ.2.2.2 hQinf)
      by_cases hxx : decodeFe Q.x = decodeFe P.x
      · -- equal x-coordinates
        have hsx : sameX = 1 := by rw [hsameX, hdx, if_pos (by rw [hxx, sub_self])]
        rw [if_pos hxx.symm]
        by_cases hyy : decodeFe P.y + decodeFe Q.y = 0
        · -- opposite y: cancellation, the output is 𝒪
          have hoy : oppY = 1 := by rw [hoppY, hsy, if_pos hyy]
          have hc1 : cancel = 1 := by rw [hcancel, hsx, hoy, one_mul]
          rw [hs1, if_pos hc1, if_pos (eq_neg_of_add_eq_zero_left hyy),
            decodePoint_of_isInf hinff]
          exact ⟨⟨Or.inr hinff, hinfx, hinfy,
            fun h0 => absurd (hinff.symm.trans h0) one_ne_zero⟩, rfl⟩
        · -- same y ≠ 0: doubling by the tangent rule
          have hoy : oppY = 0 := by rw [hoppY, hsy, if_neg hyy]
          have hc0 : cancel = 0 := by rw [hcancel, hoy, mul_zero]
          rw [hs1, if_neg (by rw [hc0]; exact zero_ne_one), hfin,
            if_neg (fun h => hyy (by rw [h]; ring))]
          -- both points coincide, with nonzero y-coordinate
          have hqy : decodeFe Q.y = decodeFe P.y := by
            rcases eq_or_eq_neg_of_sq_eq (show decodeFe Q.y ^ 2 = decodeFe P.y ^ 2 by
              rw [hQc, hPc, hxx]) with h | h
            · exact h
            · exact absurd (by rw [h]; ring) hyy
          have hpy0 : decodeFe P.y ≠ 0 := by
            intro h0
            exact hyy (by rw [hqy, h0, add_zero])
          have h2py : decodeFe P.y + decodeFe P.y ≠ 0 := by
            rw [← two_mul]
            exact mul_ne_zero two_ne_zero_fp hpy0
          have hdenv : decodeFe denv = decodeFe P.y + decodeFe P.y := by
            rw [hden, if_pos hsx, htDen]
          have hlam' : decodeFe lamv * (decodeFe P.y + decodeFe P.y)
              = decodeFe P.x * decodeFe P.x + decodeFe P.x * decodeFe P.x
                + decodeFe P.x * decodeFe P.x := by
            have h := hlam (by rw [hdenv]; exact h2py)
            rw [hdenv] at h
            rw [h, hnum, if_pos hsx, htNum, hx1sq2, hx1sq]
          have hslope : decodeFe lamv = 3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y) := by
            rw [eq_div_iff (by rw [two_mul]; exact h2py)]
            linear_combination hlam'
          have hX : decodeFe x3v
              = (3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)) ^ 2 - 2 * decodeFe P.x := by
            rw [hx3, hxs, hlamSq, hslope, hxx]; ring
          have hY : decodeFe y3v
              = 3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)
                * (decodeFe P.x
                  - ((3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y)) ^ 2 - 2 * decodeFe P.x))
                - decodeFe P.y := by
            rw [hy3, hyprod, hxd, hslope, hX]
          refine ⟨⟨Or.inl rfl, hx3v, hy3v, fun _ => ?_⟩, ?_⟩
          · rw [onCurve_iff]
            exact tangent_oncurve (s := decodeFe lamv) hPc (by linear_combination hlam')
              (by rw [hx3, hxs, hlamSq, hxx]) (by rw [hy3, hyprod, hxd])
          · rw [decodePoint_mk_zero, tangent_eq]
            simp only [Specs.ShortWeierstrass.GroupPoint.affine.injEq,
              Specs.ShortWeierstrass.Point.mk.injEq]
            exact ⟨hX, hY⟩
      · -- distinct x-coordinates: the chord rule
        have hdne : decodeFe Q.x - decodeFe P.x ≠ 0 := sub_ne_zero.mpr hxx
        have hsx : sameX = 0 := by rw [hsameX, hdx, if_neg hdne]
        have hc0 : cancel = 0 := by rw [hcancel, hsx, zero_mul]
        rw [if_neg (fun h => hxx h.symm), hs1,
          if_neg (by rw [hc0]; exact zero_ne_one), hfin]
        have hdenv : decodeFe denv = decodeFe Q.x - decodeFe P.x := by
          rw [hden, if_neg (by rw [hsx]; exact zero_ne_one), hdx]
        have hlam' : decodeFe lamv * (decodeFe Q.x - decodeFe P.x)
            = decodeFe Q.y - decodeFe P.y := by
          have h := hlam (by rw [hdenv]; exact hdne)
          rw [hdenv] at h
          rw [h, hnum, if_neg (by rw [hsx]; exact zero_ne_one), hdy]
        have hslope : decodeFe lamv
            = (decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x) := by
          rw [eq_div_iff hdne]
          exact hlam'
        have hX : decodeFe x3v
            = ((decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)) ^ 2
              - decodeFe P.x - decodeFe Q.x := by
          rw [hx3, hxs, hlamSq, hslope]; ring
        have hY : decodeFe y3v
            = (decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)
              * (decodeFe P.x
                - (((decodeFe Q.y - decodeFe P.y) / (decodeFe Q.x - decodeFe P.x)) ^ 2
                  - decodeFe P.x - decodeFe Q.x))
              - decodeFe P.y := by
          rw [hy3, hyprod, hxd, hslope, hX]
        refine ⟨⟨Or.inl rfl, hx3v, hy3v, fun _ => ?_⟩, ?_⟩
        · rw [onCurve_iff]
          exact chord_oncurve hPc hQc hdne hlam'
            (by rw [hx3, hxs, hlamSq]) (by rw [hy3, hyprod, hxd])
        · rw [decodePoint_mk_zero, chord_eq]
          simp only [Specs.ShortWeierstrass.GroupPoint.affine.injEq,
            Specs.ShortWeierstrass.Point.mk.injEq]
          exact ⟨hX, hY⟩
    · -- Q = 𝒪: the output is P
      rw [hs2, if_pos hQinf]
      refine ⟨hP, ?_⟩
      rw [decodePoint_of_isInf hQinf, decodePoint_of_finite hPinf, add_inf_right]
  · -- P = 𝒪: the output is Q
    rw [hout, if_pos hPinf]
    refine ⟨hQ, ?_⟩
    rw [decodePoint_of_isInf hPinf, add_inf_left]

end CompleteAdd
end Solution.Secp256k1ScalarMulFixedBase
