import Solution.Secp256k1ScalarMulFixedBase.AddMod
import Solution.Secp256k1ScalarMulFixedBase.SubMod
import Solution.Secp256k1ScalarMulFixedBase.DivOrZero
import Solution.Secp256k1ScalarMulFixedBase.CompleteAddTheorems
import Challenge.Utils.ComputableWitnessLemmas

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

/-! ## Computable witnesses

`CompleteAdd` chains 22 subcircuits (`SubMod`/`AddMod`/`MulMod`/`IsZeroFe`/`Mux`/
`DivOrZero`) plus one `<==` field assignment (`cancel`). Every witness generator
is a deterministic function of the parent input and the prior subcircuit outputs,
so the whole circuit is computable. Each subcircuit is discharged through its own
`computableWitnesses` theorem; prior outputs are propagated with the producers'
`eval_output_of_agreesBelow` lemmas at the concrete block offsets. -/

private theorem toFlat_append (a b : Operations (F circomPrime)) :
    (a ++ b).toFlat = a.toFlat ++ b.toFlat := by
  induction a using Operations.induct with
  | empty => simp [Operations.toFlat]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | interact _ _ ih =>
    simp [Operations.toFlat, ih]
  | subcircuit s _ ih => simp [Operations.toFlat, ih, List.append_assoc]

private theorem toFlat_flatten (L : List (Operations (F circomPrime))) :
    Operations.toFlat L.flatten = (L.map Operations.toFlat).flatten := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatten_cons, toFlat_append, ih, List.map_cons, List.flatten_cons]

private theorem flatStructural_of_no_witness
    {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime)) :
    ∀ (ops : List (FlatOperation (F circomPrime))) (offset : ℕ),
      (∀ x ∈ ops, match x with | .witness _ _ => False | _ => True) →
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' offset ops := by
  intro ops
  induction ops with
  | nil => intro offset _; trivial
  | cons x rest ih =>
    intro offset h
    have h_rest : ∀ y ∈ rest, match y with | .witness _ _ => False | _ => True :=
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases x with
    | witness m c => exact absurd (h _ (List.mem_cons_self ..)) (by simp)
    | assert e => exact ih offset h_rest
    | lookup l => exact ih offset h_rest
    | interact i => exact ih offset h_rest

private lemma expression_stable_of_field_eval_eq
    {env env' : ProverEnvironment (F circomPrime)}
    {x : Expression (F circomPrime)}
    (h : eval env x = eval env' x) :
    Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := field),
    CircuitType.eval_expression_prover_to_verifier (M := field)] at h
  rw [CircuitType.eval_var_field, CircuitType.eval_var_field] at h
  exact h

/-- The `<==` output is a fresh witness cell (offset `base`); its value depends
only on `env` below `base + 1`, so it is stable across environments agreeing below
any `k > base`. -/
private lemma assignEq_output_eval_stable (r : Var field (F circomPrime)) {base k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base < k) :
    Expression.eval env.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) =
      Expression.eval env'.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) := by
  simp only [circuit_norm, HasAssignEq.assignEq]
  exact h_agree base hk

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨P, Q⟩ := input
  have hsub : ∀ (X : Var SubMod.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit SubMod.circuit X).localLength o = 1015 := fun _ _ => rfl
  have hadd : ∀ (X : Var AddMod.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit AddMod.circuit X).localLength o = 1015 := fun _ _ => rfl
  have hmul : ∀ (X : Var (MulMod.Inputs numLimbs) (F circomPrime)) (o : ℕ),
      (subcircuit (MulMod.circuit secpParams) X).localLength o = 1306 := fun _ _ => rfl
  have hdiv : ∀ (X : Var DivOrZero.Inputs (F circomPrime)) (o : ℕ),
      (subcircuit DivOrZero.circuit X).localLength o = 1849 := fun _ _ => rfl
  have hmxE : ∀ (X : Var (Mux.Inputs Emu) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = 4 := fun _ _ => rfl
  have hmxF : ∀ (X : Var (Mux.Inputs FlaggedPoint) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := FlaggedPoint)) X).localLength o = 9 := fun _ _ => rfl
  have hisz : ∀ (x : Var Emu (F circomPrime)) (o : ℕ),
      (subcircuit IsZeroFe.circuit x).localLength o = 11 := fun _ _ => rfl
  -- constant modulus limbs are environment-independent
  have hpc : ∀ {e e' : ProverEnvironment (F circomPrime)},
      Vector.map (Expression.eval e.toEnvironment) pConst
        = Vector.map (Expression.eval e'.toEnvironment) pConst := by
    intro e e'; rw [eval_pConst, eval_pConst]
  -- an `IsZeroFe` output flag is stable across environments agreeing past its block
  have iszOut : ∀ (x : Var Emu (F circomPrime)) {e e' : ProverEnvironment (F circomPrime)}
      {O k' : ℕ}, e.AgreesBelow k' e' → O + 11 ≤ k' →
      Expression.eval e.toEnvironment ((subcircuit IsZeroFe.circuit x).output O)
        = Expression.eval e'.toEnvironment ((subcircuit IsZeroFe.circuit x).output O) := by
    intro x e e' O k' hag hk
    exact expression_stable_of_field_eval_eq (IsZeroFe.eval_output_of_agreesBelow x (offset := O) hag hk)
  -- a product of two stable field expressions is stable
  have mulStable : ∀ {e e' : ProverEnvironment (F circomPrime)} (a b : Expression (F circomPrime)),
      Expression.eval e.toEnvironment a = Expression.eval e'.toEnvironment a →
      Expression.eval e.toEnvironment b = Expression.eval e'.toEnvironment b →
      Expression.eval e.toEnvironment (a * b) = Expression.eval e'.toEnvironment (a * b) := by
    intro e e' a b ha hb
    change Expression.eval e.toEnvironment (Expression.mul a b)
      = Expression.eval e'.toEnvironment (Expression.mul a b)
    rw [eval_mul, eval_mul, ha, hb]
  -- concrete sizes so the `omega` offset bounds close
  have hnl : numLimbs = 4 := rfl
  have hsE : size Emu = 4 := rfl
  have hsF : size FlaggedPoint = 9 := rfl
  -- name each block's output at its concrete offset (mirrors `main`), so the
  -- producers' `eval_output_of_agreesBelow` can be applied with explicit inputs
  let dx : Var Emu (F circomPrime) :=
    (subcircuit SubMod.circuit { a := Q.x, b := P.x }).output offset
  let dy : Var Emu (F circomPrime) :=
    (subcircuit SubMod.circuit { a := Q.y, b := P.y }).output (offset + 1015)
  let sameX : Var field (F circomPrime) :=
    (subcircuit IsZeroFe.circuit dx).output (offset + 1015 + 1015)
  let sy : Var Emu (F circomPrime) :=
    (subcircuit AddMod.circuit { a := P.y, b := Q.y }).output (offset + 1015 + 1015 + 11)
  let oppY : Var field (F circomPrime) :=
    (subcircuit IsZeroFe.circuit sy).output (offset + 1015 + 1015 + 11 + 1015)
  let x1sq : Var Emu (F circomPrime) :=
    (subcircuit (MulMod.circuit secpParams) { a := P.x, b := P.x, modulus := pConst }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11)
  let x1sq2 : Var Emu (F circomPrime) :=
    (subcircuit AddMod.circuit { a := x1sq, b := x1sq }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306)
  let tNum : Var Emu (F circomPrime) :=
    (subcircuit AddMod.circuit { a := x1sq2, b := x1sq }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015)
  let tDen : Var Emu (F circomPrime) :=
    (subcircuit AddMod.circuit { a := P.y, b := P.y }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015)
  let num : Var Emu (F circomPrime) :=
    (subcircuit (Mux.circuit (M := Emu)) { selector := sameX, ifTrue := tNum, ifFalse := dy }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015)
  let den : Var Emu (F circomPrime) :=
    (subcircuit (Mux.circuit (M := Emu)) { selector := sameX, ifTrue := tDen, ifFalse := dx }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4)
  let lam : Var Emu (F circomPrime) :=
    (subcircuit DivOrZero.circuit { num := num, den := den }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4)
  let lamSq : Var Emu (F circomPrime) :=
    (subcircuit (MulMod.circuit secpParams) { a := lam, b := lam, modulus := pConst }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849)
  let xs : Var Emu (F circomPrime) :=
    (subcircuit SubMod.circuit { a := lamSq, b := P.x }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849 + 1306)
  let x3 : Var Emu (F circomPrime) :=
    (subcircuit SubMod.circuit { a := xs, b := Q.x }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849 + 1306 + 1015)
  let xd : Var Emu (F circomPrime) :=
    (subcircuit SubMod.circuit { a := P.x, b := x3 }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849 + 1306 + 1015 + 1015)
  let yprod : Var Emu (F circomPrime) :=
    (subcircuit (MulMod.circuit secpParams) { a := lam, b := xd, modulus := pConst }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849 + 1306 + 1015 + 1015 + 1015)
  let y3 : Var Emu (F circomPrime) :=
    (subcircuit SubMod.circuit { a := yprod, b := P.y }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849 + 1306 + 1015 + 1015 + 1015 + 1306)
  let cancel : Var field (F circomPrime) :=
    (HasAssignEq.assignEq (sameX * oppY)).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849 + 1306 + 1015 + 1015 + 1015 + 1306 + 1015)
  let finite : Var FlaggedPoint (F circomPrime) :=
    { x := x3, y := y3, isInf := ((0 : F circomPrime) : Expression (F circomPrime)) }
  let s1 : Var FlaggedPoint (F circomPrime) :=
    (subcircuit (Mux.circuit (M := FlaggedPoint))
      { selector := cancel, ifTrue := infConst, ifFalse := finite }).output
      (offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849 + 1306 + 1015 + 1015 + 1015 + 1306 + 1015 + 1)
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hsub, hadd, hmul, hdiv, hmxE, hmxF, hisz, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. dx ← SubMod { Q.x, P.x }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) SubMod.circuit _ _ _ ?_ SubMod.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, _, _⟩, hQx, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [SubMod.Inputs.mk.injEq]
    exact ⟨hQx, hPx⟩
  -- 2. dy ← SubMod { Q.y, P.y }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) SubMod.circuit _ _ _ ?_ SubMod.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, hPy, _⟩, _, hQy, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [SubMod.Inputs.mk.injEq]
    exact ⟨hQy, hPy⟩
  -- 3. sameX ← IsZeroFe dx
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) IsZeroFe.circuit _
      ((subcircuit SubMod.circuit { a := Q.x, b := P.x }).output offset) _ ?_
      IsZeroFe.computableWitnesses env env'
    intro k e e' hle h_agree _h_in
    exact SubMod.eval_output_of_agreesBelow { a := Q.x, b := P.x } h_agree (by omega)
  -- 4. sy ← AddMod { P.y, Q.y }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) AddMod.circuit _ _ _ ?_ AddMod.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, hPy, _⟩, _, hQy, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [AddMod.Inputs.mk.injEq]
    exact ⟨hPy, hQy⟩
  -- 5. oppY ← IsZeroFe sy
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) IsZeroFe.circuit _
      ((subcircuit AddMod.circuit { a := P.y, b := Q.y }).output (offset + 1015 + 1015 + 11)) _ ?_
      IsZeroFe.computableWitnesses env env'
    intro k e e' hle h_agree _h_in
    exact AddMod.eval_output_of_agreesBelow { a := P.y, b := Q.y } h_agree (by omega)
  -- 6. x1sq ← MulMod { P.x, P.x, pConst }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (MulMod.circuit secpParams) _ _ _ ?_ (MulMod.computableWitnesses secpParams) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, _, _⟩, _, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [MulMod.Inputs.mk.injEq]
    exact ⟨hPx, hPx, hpc⟩
  -- 7. x1sq2 ← AddMod { x1sq, x1sq }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) AddMod.circuit _ _ _ ?_ AddMod.computableWitnesses env env'
    intro k e e' hle h_agree _h_in
    simp only [circuit_norm] at ⊢; rw [AddMod.Inputs.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (MulMod.eval_output_of_agreesBelow secpParams
        { a := P.x, b := P.x, modulus := pConst } h_agree (by omega)),
      emu_map_eval_eq_of_eval_eq (MulMod.eval_output_of_agreesBelow secpParams
        { a := P.x, b := P.x, modulus := pConst } h_agree (by omega))⟩
  -- 8. tNum ← AddMod { x1sq2, x1sq }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) AddMod.circuit _ _ _ ?_ AddMod.computableWitnesses env env'
    intro k e e' hle h_agree _h_in
    simp only [circuit_norm] at ⊢; rw [AddMod.Inputs.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (AddMod.eval_output_of_agreesBelow { a := x1sq, b := x1sq } h_agree (by omega)),
      emu_map_eval_eq_of_eval_eq (MulMod.eval_output_of_agreesBelow secpParams
        { a := P.x, b := P.x, modulus := pConst } h_agree (by omega))⟩
  -- 9. tDen ← AddMod { P.y, P.y }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) AddMod.circuit _ _ _ ?_ AddMod.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, hPy, _⟩, _, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [AddMod.Inputs.mk.injEq]
    exact ⟨hPy, hPy⟩
  -- 10. num ← Mux { sameX, tNum, dy }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_ (Mux.computableWitnesses (M := Emu)) env env'
    intro k e e' hle h_agree _h_in
    simp only [circuit_norm] at ⊢; rw [Mux.Inputs.mk.injEq]
    exact ⟨iszOut dx h_agree (by omega),
      emu_map_eval_eq_of_eval_eq (AddMod.eval_output_of_agreesBelow { a := x1sq2, b := x1sq } h_agree (by omega)),
      emu_map_eval_eq_of_eval_eq (SubMod.eval_output_of_agreesBelow { a := Q.y, b := P.y } h_agree (by omega))⟩
  -- 11. den ← Mux { sameX, tDen, dx }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _ _ _ ?_ (Mux.computableWitnesses (M := Emu)) env env'
    intro k e e' hle h_agree _h_in
    simp only [circuit_norm] at ⊢; rw [Mux.Inputs.mk.injEq]
    exact ⟨iszOut dx h_agree (by omega),
      emu_map_eval_eq_of_eval_eq (AddMod.eval_output_of_agreesBelow { a := P.y, b := P.y } h_agree (by omega)),
      emu_map_eval_eq_of_eval_eq (SubMod.eval_output_of_agreesBelow { a := Q.x, b := P.x } h_agree (by omega))⟩
  -- 12. lam ← DivOrZero { num, den }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) DivOrZero.circuit _ _ _ ?_ DivOrZero.computableWitnesses env env'
    intro k e e' hle h_agree _h_in
    simp only [circuit_norm] at ⊢; rw [DivOrZero.Inputs.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (Mux.eval_output_of_agreesBelow (M := Emu)
        { selector := sameX, ifTrue := tNum, ifFalse := dy } h_agree (by omega)),
      emu_map_eval_eq_of_eval_eq (Mux.eval_output_of_agreesBelow (M := Emu)
        { selector := sameX, ifTrue := tDen, ifFalse := dx } h_agree (by omega))⟩
  -- 13. lamSq ← MulMod { lam, lam, pConst }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (MulMod.circuit secpParams) _ _ _ ?_ (MulMod.computableWitnesses secpParams) env env'
    intro k e e' hle h_agree _h_in
    simp only [circuit_norm] at ⊢; rw [MulMod.Inputs.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (DivOrZero.eval_output_of_agreesBelow { num := num, den := den } h_agree (by omega)),
      emu_map_eval_eq_of_eval_eq (DivOrZero.eval_output_of_agreesBelow { num := num, den := den } h_agree (by omega)), hpc⟩
  -- 14. xs ← SubMod { lamSq, P.x }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) SubMod.circuit _ _ _ ?_ SubMod.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, _, _⟩, _, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [SubMod.Inputs.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (MulMod.eval_output_of_agreesBelow secpParams
      { a := lam, b := lam, modulus := pConst } h_agree (by omega)), hPx⟩
  -- 15. x3 ← SubMod { xs, Q.x }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) SubMod.circuit _ _ _ ?_ SubMod.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, _, _⟩, hQx, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [SubMod.Inputs.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (SubMod.eval_output_of_agreesBelow { a := lamSq, b := P.x } h_agree (by omega)), hQx⟩
  -- 16. xd ← SubMod { P.x, x3 }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) SubMod.circuit _ _ _ ?_ SubMod.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, _, _⟩, _, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [SubMod.Inputs.mk.injEq]
    exact ⟨hPx, emu_map_eval_eq_of_eval_eq (SubMod.eval_output_of_agreesBelow { a := xs, b := Q.x } h_agree (by omega))⟩
  -- 17. yprod ← MulMod { lam, xd, pConst }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (MulMod.circuit secpParams) _ _ _ ?_ (MulMod.computableWitnesses secpParams) env env'
    intro k e e' hle h_agree _h_in
    simp only [circuit_norm] at ⊢; rw [MulMod.Inputs.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (DivOrZero.eval_output_of_agreesBelow { num := num, den := den } h_agree (by omega)),
      emu_map_eval_eq_of_eval_eq (SubMod.eval_output_of_agreesBelow { a := P.x, b := x3 } h_agree (by omega)), hpc⟩
  -- 18. y3 ← SubMod { yprod, P.y }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) SubMod.circuit _ _ _ ?_ SubMod.computableWitnesses env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, hPy, _⟩, _, _, _⟩ := h_in
    simp only [circuit_norm] at ⊢; rw [SubMod.Inputs.mk.injEq]
    exact ⟨emu_map_eval_eq_of_eval_eq (MulMod.eval_output_of_agreesBelow secpParams
      { a := lam, b := xd, modulus := pConst } h_agree (by omega)), hPy⟩
  -- 19. cancel <== sameX * oppY (ProvableType witness + `===` equality assertion)
  · simp only [HasAssignEq.assignEq,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
      and_true]
    refine ⟨?_, ?_⟩
    · -- the witnessed cancellation flag `sameX * oppY` is stable
      intro h_agree _h_in
      rw [CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_expression_prover_to_verifier (M := field),
        CircuitType.eval_var_field, CircuitType.eval_var_field]
      exact mulStable _ _
        (iszOut dx (O := offset + 1015 + 1015) h_agree (by omega))
        (iszOut sy (O := offset + 1015 + 1015 + 11 + 1015) h_agree (by omega))
    · -- the `===` equality assertion carries no witnesses
      simp only [HasAssertEq.assert_eq, assertEquals,
        Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
      apply flatStructural_of_no_witness
      simp only [Gadgets.Equality.circuit, Gadgets.Equality.main]
      intro x hx
      rw [Circuit.forEach.operations_eq, toFlat_flatten, List.map_ofFn, List.mem_flatten] at hx
      obtain ⟨l, hl, hxl⟩ := hx
      rw [List.mem_ofFn] at hl
      obtain ⟨i, rfl⟩ := hl
      simp only [Function.comp, Circuit.assertZero, circuit_norm, Operations.toFlat,
        List.mem_cons, List.not_mem_nil, or_false] at hxl
      subst hxl
      trivial
  -- 20. s1 ← Mux { cancel, infConst, finite (x3, y3, 0) }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := FlaggedPoint)) _ _ _ ?_
      (Mux.computableWitnesses (M := FlaggedPoint)) env env'
    intro k e e' hle h_agree _h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm] at ⊢
    rw [Mux.Inputs.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · -- selector = cancel, a fresh witness cell
      exact assignEq_output_eval_stable (sameX * oppY)
        (base := offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849
          + 1306 + 1015 + 1015 + 1015 + 1306 + 1015) h_agree (by omega)
    · -- ifTrue = infConst (constant point at infinity)
      rw [FlaggedPoint.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · simp only [infConst]; rw [DivOrZero.eval_zeroConst, DivOrZero.eval_zeroConst]
      · simp only [infConst]; rw [DivOrZero.eval_zeroConst, DivOrZero.eval_zeroConst]
      · simp only [infConst, Expression.eval]
    · -- ifFalse = finite (x3, y3, 0)
      rw [FlaggedPoint.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · exact emu_map_eval_eq_of_eval_eq (SubMod.eval_output_of_agreesBelow { a := xs, b := Q.x } h_agree (by omega))
      · exact emu_map_eval_eq_of_eval_eq (SubMod.eval_output_of_agreesBelow { a := yprod, b := P.y } h_agree (by omega))
      · rfl
  -- 21. s2 ← Mux { Q.isInf, P, s1 }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := FlaggedPoint)) _ _ _ ?_
      (Mux.computableWitnesses (M := FlaggedPoint)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨hPx, hPy, hPi⟩, _, _, hQi⟩ := h_in
    simp only [circuit_norm] at ⊢
    rw [Mux.Inputs.mk.injEq]
    refine ⟨hQi, ?_, ?_⟩
    · -- ifTrue = P (raw input point)
      rw [FlaggedPoint.mk.injEq]; exact ⟨hPx, hPy, hPi⟩
    · -- ifFalse = s1, a fresh `Mux` witness block
      have hs1 := Mux.eval_output_of_agreesBelow (M := FlaggedPoint)
        { selector := cancel, ifTrue := infConst, ifFalse := finite }
        (offset := offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849
          + 1306 + 1015 + 1015 + 1015 + 1306 + 1015 + 1) h_agree (by omega)
      simp only [circuit_norm] at hs1
      exact hs1
  -- 22. out ← Mux { P.isInf, Q, s2 }
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := FlaggedPoint)) _ _ _ ?_
      (Mux.computableWitnesses (M := FlaggedPoint)) env env'
    intro k e e' hle h_agree h_in
    simp only [circuit_norm] at hle
    simp only [circuit_norm, Inputs.mk.injEq, FlaggedPoint.mk.injEq] at h_in
    obtain ⟨⟨_, _, hPi⟩, hQx, hQy, hQi⟩ := h_in
    simp only [circuit_norm] at ⊢
    rw [Mux.Inputs.mk.injEq]
    refine ⟨hPi, ?_, ?_⟩
    · -- ifTrue = Q (raw input point)
      rw [FlaggedPoint.mk.injEq]; exact ⟨hQx, hQy, hQi⟩
    · -- ifFalse = s2, a fresh `Mux` witness block
      have hs2 := Mux.eval_output_of_agreesBelow (M := FlaggedPoint)
        { selector := Q.isInf, ifTrue := P, ifFalse := s1 }
        (offset := offset + 1015 + 1015 + 11 + 1015 + 11 + 1306 + 1015 + 1015 + 1015 + 4 + 4 + 1849
          + 1306 + 1015 + 1015 + 1015 + 1306 + 1015 + 1 + 9) h_agree (by omega)
      simp only [circuit_norm] at hs2
      exact hs2

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

/-- A fresh `FlaggedPoint` witness block reads only its own `size FlaggedPoint`
cells, so it is stable across environments agreeing below `off + size FlaggedPoint`. -/
private lemma fpVar_stable {off k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : off + size FlaggedPoint ≤ k) :
    eval env ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))))
      = eval env' ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime)))) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint),
    CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  exact h_agree (off + i) (by omega)

/-- The output of `CompleteAdd.main` is the final `Mux` witness block (the flagged
point `out`), allocated at `offset + 15966` and reading only its `size FlaggedPoint = 9`
cells. Environments agreeing below any `k ≥ offset + 15975` (the full local length)
evaluate the output identically. Consumed by `Step`. -/
lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 15975 ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  rw [elaborated.output_eq input offset]
  have hsz : size FlaggedPoint = 9 := rfl
  exact fpVar_stable (off := offset + 15966) h_agree (by rw [hsz]; omega)

end CompleteAdd
end Solution.Secp256k1ScalarMulFixedBase
