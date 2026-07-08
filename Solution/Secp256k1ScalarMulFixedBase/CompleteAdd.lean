import Solution.Secp256k1ScalarMulFixedBase.AddMod
import Solution.Secp256k1ScalarMulFixedBase.SubMod
import Solution.Secp256k1ScalarMulFixedBase.DivOrZero
import Solution.Secp256k1ScalarMulFixedBase.CompleteAddTheorems

/-!
# Complete secp256k1 point addition — `CompleteAdd`

`FormalCircuit` implementing the complete group law of the trusted spec
(`Specs.ShortWeierstrass.add`) on flagged points: for **any** two valid
inputs the output decodes to the true group-law sum, including every
exceptional case (identity, `P + (−P) = 𝒪`, doubling, 2-torsion self-add).

## Strategy

All branches are computed unconditionally over the emulated field, then the
result is selected by boolean flags — the standard "complete formulas via
muxing" construction:

- `sameX = (Q.x − P.x = 0)`, `oppY = (P.y + Q.y = 0)` via `SubMod`/`AddMod` +
  `IsZeroFe`;
- slope numerator/denominator muxed between the chord (`Q.y − P.y`,
  `Q.x − P.x`) and the tangent (`3·P.x²`, `2·P.y` — the curve has `a = 0`)
  by `sameX`, then `λ ← DivOrZero(num, den)`. On the sub-branch where the
  denominator is zero (exactly `sameX ∧ oppY`, given valid on-curve inputs)
  the division is guarded and the affine result is discarded by the flag
  selection below;
- `x₃ = λ² − P.x − Q.x`, `y₃ = λ·(P.x − x₃) − P.y`;
- output selection, mirroring the spec's match order:
  `if P.isInf then Q else if Q.isInf then P else if sameX·oppY then 𝒪 else
  (x₃, y₃)`.

-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace CompleteAdd



/-- Inputs of `CompleteAdd`: the two flagged points. -/
structure Inputs (F : Type) where
  P : FlaggedPoint F
  Q : FlaggedPoint F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let { P, Q } := input

  -- case flags
  let dx ← subcircuit SubMod.circuit { a := Q.x, b := P.x }
  let dy ← subcircuit SubMod.circuit { a := Q.y, b := P.y }
  let sameX ← subcircuit IsZeroFe.circuit dx
  let sy ← subcircuit AddMod.circuit { a := P.y, b := Q.y }
  let oppY ← subcircuit IsZeroFe.circuit sy

  -- tangent slope parts: 3·P.x² and 2·P.y (secp256k1 has a = 0)
  let x1sq ← subcircuit (MulMod.circuit secpParams)
    { a := P.x, b := P.x, modulus := pConst }
  let x1sq2 ← subcircuit AddMod.circuit { a := x1sq, b := x1sq }
  let tNum ← subcircuit AddMod.circuit { a := x1sq2, b := x1sq }
  let tDen ← subcircuit AddMod.circuit { a := P.y, b := P.y }

  -- slope: chord (dy/dx) or tangent (3x²/2y), by sameX
  let num ← subcircuit (Mux.circuit (M := Emu))
    { selector := sameX, ifTrue := tNum, ifFalse := dy }
  let den ← subcircuit (Mux.circuit (M := Emu))
    { selector := sameX, ifTrue := tDen, ifFalse := dx }
  let lam ← subcircuit DivOrZero.circuit { num := num, den := den }

  -- affine result: x₃ = λ² − P.x − Q.x, y₃ = λ·(P.x − x₃) − P.y
  let lamSq ← subcircuit (MulMod.circuit secpParams)
    { a := lam, b := lam, modulus := pConst }
  let xs ← subcircuit SubMod.circuit { a := lamSq, b := P.x }
  let x3 ← subcircuit SubMod.circuit { a := xs, b := Q.x }
  let xd ← subcircuit SubMod.circuit { a := P.x, b := x3 }
  let yprod ← subcircuit (MulMod.circuit secpParams)
    { a := lam, b := xd, modulus := pConst }
  let y3 ← subcircuit SubMod.circuit { a := yprod, b := P.y }

  -- cancellation flag: both finite, same x, opposite y ⇒ 𝒪
  let cancel <== sameX * oppY

  -- output selection, mirroring `Specs.ShortWeierstrass.add`
  let finite : Var FlaggedPoint (F circomPrime) :=
    { x := x3, y := y3, isInf := ((0 : F circomPrime) : Expression (F circomPrime)) }
  let s1 ← subcircuit (Mux.circuit (M := FlaggedPoint))
    { selector := cancel, ifTrue := infConst, ifFalse := finite }
  let s2 ← subcircuit (Mux.circuit (M := FlaggedPoint))
    { selector := Q.isInf, ifTrue := P, ifFalse := s1 }
  let out ← subcircuit (Mux.circuit (M := FlaggedPoint))
    { selector := P.isInf, ifTrue := Q, ifFalse := s2 }
  return out

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

/-- Preconditions: both inputs are well-formed flagged points (boolean flags,
canonical coordinates, on-curve when finite). -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.P.Valid ∧ input.Q.Valid

/-- Postcondition: the output is a well-formed flagged point decoding to the
complete group-law sum of the trusted spec. -/
def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.Valid ∧
    decodePoint out =
      Specs.ShortWeierstrass.add Specs.Secp256k1.curve
        (decodePoint input.P) (decodePoint input.Q)

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [SubMod.circuit, SubMod.Assumptions, SubMod.Spec,
    AddMod.circuit, AddMod.Assumptions, AddMod.Spec,
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZero.circuit, DivOrZero.Assumptions, DivOrZero.Spec, secpParams]
  obtain ⟨hdx, hdy, hsameX, hsy, hoppY, hx1sq, hx1sq2, htNum, htDen, hnum, hden,
    hlam, hlamSq, hxs, hx3, hxd, hyprod, hy3, hcancel, hs1, hs2, hout⟩ := h_holds
  -- input validity components
  have hPx : Fe.Valid input_P_x := h_assumptions.1.2.1
  have hPy : Fe.Valid input_P_y := h_assumptions.1.2.2.1
  have hQx : Fe.Valid input_Q_x := h_assumptions.2.2.1
  have hQy : Fe.Valid input_Q_y := h_assumptions.2.2.2.1
  have hpn := pConst_normalized env
  have hpv := pConst_value env
  -- flag chain
  obtain ⟨hdxv, hdxe⟩ := hdx ⟨hQx, hPx⟩
  obtain ⟨hdyv, hdye⟩ := hdy ⟨hQy, hPy⟩
  have hsameX' := hsameX hdxv
  obtain ⟨hsyv, hsye⟩ := hsy ⟨hPy, hQy⟩
  have hoppY' := hoppY hsyv
  -- tangent numerator/denominator chain
  obtain ⟨hx1sqn, hx1sqe⟩ := hx1sq ⟨hPx.1, hPx.1, hpn,
    by rw [hpv]; exact hPx.2, by rw [hpv]; exact hPx.2, by rw [hpv]; exact P256_pos⟩
  rw [hpv] at hx1sqe
  have hx1sqv : Fe.Valid _ := fe_valid_of_mod hx1sqn hx1sqe
  have hx1sqd := decodeFe_of_mulmod hx1sqe
  obtain ⟨hx1sq2v, hx1sq2e⟩ := hx1sq2 hx1sqv
  obtain ⟨htNumv, htNume⟩ := htNum ⟨hx1sq2v, hx1sqv⟩
  obtain ⟨htDenv, htDene⟩ := htDen hPy
  -- slope
  have hnum' := hnum (by rw [hsameX']; exact isBool_ite)
  have hden' := hden (by rw [hsameX']; exact isBool_ite)
  obtain ⟨hlamv, hlam1, -⟩ := hlam ⟨by rw [hnum']; exact fe_valid_ite htNumv hdyv,
    by rw [hden']; exact fe_valid_ite htDenv hdxv⟩
  -- affine result chain
  obtain ⟨hlamSqn, hlamSqe⟩ := hlamSq ⟨hlamv.1, hlamv.1, hpn,
    by rw [hpv]; exact hlamv.2, by rw [hpv]; exact hlamv.2, by rw [hpv]; exact P256_pos⟩
  rw [hpv] at hlamSqe
  have hlamSqd := decodeFe_of_mulmod hlamSqe
  obtain ⟨hxsv, hxse⟩ := hxs ⟨fe_valid_of_mod hlamSqn hlamSqe, hPx⟩
  obtain ⟨hx3v, hx3e⟩ := hx3 ⟨hxsv, hQx⟩
  obtain ⟨hxdv, hxde⟩ := hxd ⟨hPx, hx3v⟩
  obtain ⟨hyprodn, hyprode⟩ := hyprod ⟨hlamv.1, hxdv.1, hpn,
    by rw [hpv]; exact hlamv.2, by rw [hpv]; exact hxdv.2, by rw [hpv]; exact P256_pos⟩
  rw [hpv] at hyprode
  have hyprodd := decodeFe_of_mulmod hyprode
  obtain ⟨hy3v, hy3e⟩ := hy3 ⟨fe_valid_of_mod hyprodn hyprode, hPy⟩
  -- output selection muxes
  have hs1' := hs1 (by
    rw [hcancel]
    exact isBool_mul (by rw [hsameX']; exact isBool_ite) (by rw [hoppY']; exact isBool_ite))
  have hs2' := hs2 h_assumptions.2.1
  have hout' := hout h_assumptions.1.1
  exact soundness_core h_assumptions.1 h_assumptions.2 hdxe hdye hsameX' hsye hoppY'
    hx1sqd hx1sq2e htNume htDene hnum' hden' hlam1 hlamSqd hxse hx3v hx3e hxde hyprodd
    hy3v hy3e hcancel (fe_valid_eval_zeroConst env) (fe_valid_eval_zeroConst env) rfl rfl
    hs1' hs2' hout'

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [SubMod.circuit, SubMod.Assumptions, SubMod.Spec,
    AddMod.circuit, AddMod.Assumptions, AddMod.Spec,
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    DivOrZero.circuit, DivOrZero.Assumptions, DivOrZero.Spec, secpParams]
  obtain ⟨hdx, hdy, hsameX, hsy, hoppY, hx1sq, hx1sq2, htNum, htDen, hnum, hden,
    hlam, hlamSq, hxs, hx3, hxd, hyprod, hy3, hcancel, hs1, hs2, hout⟩ := h_env
  -- input validity components
  have hPx : Fe.Valid input_P_x := h_assumptions.1.2.1
  have hPy : Fe.Valid input_P_y := h_assumptions.1.2.2.1
  have hQx : Fe.Valid input_Q_x := h_assumptions.2.2.1
  have hQy : Fe.Valid input_Q_y := h_assumptions.2.2.2.1
  have hpn := pConst_normalized env.toEnvironment
  have hpv := pConst_value env.toEnvironment
  -- the same discharge chain as in `soundness`
  obtain ⟨hdxv, -⟩ := hdx ⟨hQx, hPx⟩
  obtain ⟨hdyv, -⟩ := hdy ⟨hQy, hPy⟩
  have hsxb := isBool_of_eq_ite (hsameX hdxv)
  obtain ⟨hsyv, -⟩ := hsy ⟨hPy, hQy⟩
  have hoyb := isBool_of_eq_ite (hoppY hsyv)
  have hx1sqA := mulmod_assumptions env.toEnvironment hPx hPx
  obtain ⟨hx1sqn, hx1sqe⟩ := hx1sq hx1sqA
  rw [hpv] at hx1sqe
  have hx1sqv : Fe.Valid _ := fe_valid_of_mod hx1sqn hx1sqe
  obtain ⟨hx1sq2v, -⟩ := hx1sq2 hx1sqv
  obtain ⟨htNumv, -⟩ := htNum ⟨hx1sq2v, hx1sqv⟩
  obtain ⟨htDenv, -⟩ := htDen hPy
  have hnumv := fe_valid_of_eq_ite htNumv hdyv (hnum hsxb)
  have hdenv := fe_valid_of_eq_ite htDenv hdxv (hden hsxb)
  obtain ⟨hlamv, -, -⟩ := hlam ⟨hnumv, hdenv⟩
  have hlamSqA := mulmod_assumptions env.toEnvironment hlamv hlamv
  obtain ⟨hlamSqn, hlamSqe⟩ := hlamSq hlamSqA
  rw [hpv] at hlamSqe
  have hlamSqv : Fe.Valid _ := fe_valid_of_mod hlamSqn hlamSqe
  obtain ⟨hxsv, -⟩ := hxs ⟨hlamSqv, hPx⟩
  obtain ⟨hx3v, -⟩ := hx3 ⟨hxsv, hQx⟩
  obtain ⟨hxdv, -⟩ := hxd ⟨hPx, hx3v⟩
  have hyprodA := mulmod_assumptions env.toEnvironment hlamv hxdv
  obtain ⟨hyprodn, hyprode⟩ := hyprod hyprodA
  rw [hpv] at hyprode
  have hyprodv : Fe.Valid _ := fe_valid_of_mod hyprodn hyprode
  obtain ⟨hy3v, -⟩ := hy3 ⟨hyprodv, hPy⟩
  have hcb := isBool_of_eq_mul hsxb hoyb hcancel
  exact ⟨⟨hQx, hPx⟩, ⟨hQy, hPy⟩, hdxv, ⟨hPy, hQy⟩, hsyv, hx1sqA, hx1sqv,
    ⟨hx1sq2v, hx1sqv⟩, hPy, hsxb, hsxb, ⟨hnumv, hdenv⟩, hlamSqA,
    ⟨hlamSqv, hPx⟩, ⟨hxsv, hQx⟩, ⟨hPx, hx3v⟩, hyprodA,
    ⟨hyprodv, hPy⟩, by rw [hcancel], hcb,
    h_assumptions.2.1, h_assumptions.1.1⟩

/-- The `CompleteAdd` formal circuit: the complete secp256k1 group law on
flagged points. -/
def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main; elaborated; Assumptions; Spec; soundness; completeness

end CompleteAdd
end Solution.Secp256k1ScalarMulFixedBase

