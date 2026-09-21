import Solution.Secp256k1ScalarMul.IsZeroFe
import Solution.Secp256k1ScalarMul.Mux
import Solution.Secp256k1ScalarMul.DivOrZeroTheorems

/-!
# Emulated field division by witnessing — `DivOrZero`

`FormalCircuit` computing `λ = num / den mod P256` when `den ≠ 0`, and `λ = 0`
when `den = 0`. This is the "inversion by witnessing" gadget: the quotient is
witnessed and certified by one emulated multiplication.

## Strategy

- `z ← IsZeroFe den` — the boolean zero flag of the denominator;
- `denSafe ← mux z 1 den`, `numSafe ← mux z 0 num` — guard the degenerate
  case so the certifying multiplication is always meaningful;
- witness `λ` (`num · den⁻¹ mod P256`, or `0` when `den = 0`), normalize and
  range-check it;
- certify `λ · denSafe ≡ numSafe (mod P256)` with one `MulMod` and a
  limb-wise `Equal`.

When `den = 0` this forces `λ · 1 = 0`, i.e. `λ = 0`; otherwise
`λ · den = num` in the emulated field.

The caller (`CompleteAdd`) only uses `λ` on the branch where `den ≠ 0`, but
the constraints are satisfiable on every input, which is what makes the
enclosing complete-addition gadget total.

-/

namespace Solution.Secp256k1ScalarMul
namespace DivOrZero

/-- Inputs of `DivOrZero`: numerator and denominator, both canonical. -/
structure Inputs (F : Type) where
  num : Emu F
  den : Emu F
deriving ProvableStruct

/-! ## Witness program for `λ`

`λ = num · den⁻¹ mod P256` is the only witness in this solution that needs a modular
**inverse in the emulated field**, so `Witgen.FExpr.inv` (which inverts in the *circuit*
field) is useless. It is computed by Fermat's little theorem, `den^(P256−2) mod P256`,
as a square-and-multiply chain of digit-layer modular multiplications
(`WitgenBigNat.invModP`): one `letU` chain per multiplication keeps the program linear
in the 256-bit exponent where a nested expression would duplicate the base once per bit.

The denominator is reduced modulo `P256` first. That costs one extra modular
multiplication and buys the whole specification back unconditionally: `invModP`'s
correctness wants a reduced base, and the reduction makes that true of *every*
environment rather than only the ones the gadget's `Assumptions` cover, so
`computesV_lamProgram` stays the unconditional statement it was. A zero denominator
needs no special casing either, since `(0 : Fp)⁻¹ = 0`.
-/

section Generator
open Witgen WitgenNat WitgenBigNat IRLimbs IREmu

/-- Digits of the modulus register. -/
@[reducible] def nlen : ℕ := emuLen

/-- Digits of a reduced value: one more than the modulus needs. -/
@[reducible] def rlen : ℕ := nlen + 1

/-- Width of a product of two reduced values. -/
@[reducible] def pbits : ℕ := 2 * (WitgenNat.W * nlen)

/-- Digits of the quotient register. -/
@[reducible] def qlen : ℕ := numChunks pbits

theorem modulus_lt_nlen : P256 < base ^ nlen := by decide

theorem pow_le_pbits : base ^ (2 * nlen) ≤ 2 ^ pbits := by
  rw [base_pow]
  exact Nat.pow_le_pow_right (by norm_num) (le_of_eq (by rw [pbits]; ring))

theorem pbits_le_qlen : 2 ^ pbits ≤ base ^ qlen := two_pow_le_base_numChunks _

/-- The modulus as a digit register. -/
def pDigits : List (U64Expr (F circomPrime)) := constDigits P256 nlen

theorem lval_pDigits : lval (ofNat P256 nlen) = P256 := lval_ofNat_of_lt modulus_lt_nlen

/-- Witness program for `λ`: reduce the denominator, invert it by Fermat, multiply by
the numerator, and decompose. -/
def lamProgram (num den : Var Emu (F circomPrime)) :
    M (F circomPrime) (VExpr (F circomPrime) numLimbs) := do
  let dred ← mulModP pDigits (emuDigits den) (constDigits 1 rlen) qlen rlen pbits
  let dinv ← invModP P256 nlen qlen rlen pbits 256 dred
  let lam ← mulModP pDigits (emuDigits num) dinv qlen rlen pbits
  Pure.pure (emuOutF lam)

/-- The intended `λ` value: the emulated-field quotient (`0` at a zero
denominator, since `(0 : Fp)⁻¹ = 0`). -/
def lamNat (nv dv : ℕ) : ℕ :=
  ZMod.val ((nv : Specs.Secp256k1.Fp) * ((dv : Specs.Secp256k1.Fp))⁻¹)

/-- The intended contents of the `λ` cells. -/
def lamValue (nv dv : ℕ) : Emu (F circomPrime) := emuOfNat (lamNat nv dv)

theorem computesV_lamProgram (num den : Var Emu (F circomPrime)) :
    ComputesV #[] (lamProgram num den)
      (fun env => lamValue (bigVal limbBits num env) (bigVal limbBits den env)) := by
  have hn : ∀ {S : Array (Step (F circomPrime))},
      EvalsBig S pDigits (fun _ : ProverEnvironment (F circomPrime) => ofNat P256 nlen) :=
    evalsBig_constDigits P256 nlen
  have hnpos : ∀ (env : ProverEnvironment (F circomPrime)),
      0 < lval (ofNat P256 nlen) := fun _ => by rw [lval_pDigits]; decide
  have hnlen : pDigits.length < rlen := by
    rw [pDigits, length_constDigits]; exact Nat.lt_succ_self nlen
  have hspan : ∀ (x : Var Emu (F circomPrime)) (env : ProverEnvironment (F circomPrime)),
      lval (ofNat (bigVal limbBits x env) emuLen) = bigVal limbBits x env :=
    fun x env => lval_ofNat_emu (bigVal_lt_span x env)
  have hsmall : ∀ (x : Var Emu (F circomPrime)) (env : ProverEnvironment (F circomPrime)),
      bigVal limbBits x env < 2 ^ 256 := fun x env => bigVal_lt_span x env
  -- the reduced denominator
  refine Computes.bind (computesBig_mulModP pDigits (emuDigits den) (constDigits 1 rlen)
    qlen rlen pbits hn (evalsBig_emuDigits den) (evalsBig_constDigits 1 rlen)
    hnpos hnlen (fun env => ?_) pbits_le_qlen) ?_
  · rw [hspan den env, lval_ofNat]
    have h1 : (1 : ℕ) % base ^ rlen ≤ 1 := Nat.mod_le _ _
    have h2 := hsmall den env
    have h3 : (2 : ℕ) ^ 256 ≤ 2 ^ pbits := Nat.pow_le_pow_right (by norm_num) (by decide)
    calc bigVal limbBits den env * (1 % base ^ rlen) ≤ bigVal limbBits den env * 1 :=
          Nat.mul_le_mul_left _ h1
      _ < 2 ^ pbits := by omega
  intro S1 dred hS1 hdred
  replace hdred : EvalsBig S1 dred
      (fun env => ofNat (bigVal limbBits den env % P256) rlen) :=
    hdred.congr fun env => by
      rw [hspan den env, lval_ofNat, lval_pDigits,
        Nat.mod_eq_of_lt (show (1:ℕ) < base ^ rlen by decide), Nat.mul_one]
  -- the Fermat inverse
  refine Computes.bind (computesBig_invModP (q := P256) (by decide) nlen qlen rlen pbits 256
    modulus_lt_nlen (Nat.lt_succ_self nlen) pow_le_pbits pbits_le_qlen (by decide) hdred (fun env => ?_)) ?_
  · rw [lval_ofNat_of_lt (lt_trans (Nat.mod_lt _ (by decide : 0 < P256))
      (by have := modulus_lt_nlen
          exact lt_of_lt_of_le this (Nat.pow_le_pow_right base_pos (Nat.le_succ nlen))))]
    exact Nat.mod_lt _ (by decide)
  intro S2 dinv hS2 hdinv
  replace hdinv : EvalsBig S2 dinv
      (fun env => ofNat (((bigVal limbBits den env : ZMod P256)⁻¹).val) rlen) :=
    hdinv.congr fun env => by
      rw [lval_ofNat_of_lt (lt_trans (Nat.mod_lt _ (by decide : 0 < P256))
        (lt_of_lt_of_le modulus_lt_nlen (Nat.pow_le_pow_right base_pos (Nat.le_succ nlen)))),
        ZMod.natCast_mod]
  -- the product with the numerator
  refine Computes.bind (computesBig_mulModP pDigits (emuDigits num) dinv qlen rlen pbits
    (hn.mono (hS1.trans hS2)) ((evalsBig_emuDigits num).mono (hS1.trans hS2)) hdinv
    hnpos hnlen (fun env => ?_) pbits_le_qlen) ?_
  · rw [hspan num env, lval_ofNat_of_lt (lt_trans (ZMod.val_lt _)
      (lt_of_lt_of_le modulus_lt_nlen (Nat.pow_le_pow_right base_pos (Nat.le_succ nlen))))]
    have h1 := hsmall num env
    have h2 : ((bigVal limbBits den env : ZMod P256)⁻¹).val < P256 := ZMod.val_lt _
    have h3 : P256 < 2 ^ 256 := by decide
    calc bigVal limbBits num env * ((bigVal limbBits den env : ZMod P256)⁻¹).val
        < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul_of_lt_of_le h1 (le_of_lt (by omega))
          (Nat.two_pow_pos _)
      _ = 2 ^ pbits := by rw [← pow_add]; rfl
  intro S3 lam hS3 hlam
  refine Computes.pure ((evalsV_emuOutF hlam).congr fun env => ?_)
  have hlt : ∀ v : ℕ, v < P256 → lval (ofNat v rlen) = v := fun v hv =>
    lval_ofNat_of_lt (lt_trans hv (lt_of_lt_of_le modulus_lt_nlen
      (Nat.pow_le_pow_right base_pos (Nat.le_succ nlen))))
  have hinv : lval (ofNat (((bigVal limbBits den env : ZMod P256)⁻¹).val) rlen)
      = ((bigVal limbBits den env : ZMod P256)⁻¹).val := hlt _ (ZMod.val_lt _)
  rw [hspan num env, lval_pDigits, hinv,
    hlt _ (Nat.mod_lt _ (by decide : 0 < P256)),
    lamValue, lamNat, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]


/-! ### Sealing the witness site

The `λ` chain is *data*, and a couple of million `letU` steps of it: 256 squarings and
about as many multiplies, each a schoolbook product and a 512-step binary division. It
must never be evaluated, and `circuit_norm` would evaluate it, because
`Witgen.M.toIR` is one of its unfoldings and the witness operation carries
`(lamProgram num den).toIR`.

So the site carries `lamIR` instead, the IR computed once and then sealed. Nothing in
`circuit_norm` unfolds it, so nothing ever asks for the program's steps; everything the
rest of the file needs is proved here, before the seal. (`irreducible` alone would not
do: the *kernel* ignores it when it rechecks a `simp` step's `rfl`.)
-/

/-- The `λ` witness site's IR, written as the `.ir` constructor directly rather than
through `Witgen.M.toIR`. That is what keeps `IsIR` a one-step `iota` reduction instead
of a reduction of the program itself. -/
def lamIR (num den : Var Emu (F circomPrime)) :
    Witgen.WitgenIR (F circomPrime) numLimbs :=
  .ir (lamProgram num den #[]).2.toList (lamProgram num den #[]).1

/-- `lamIR` is the program's IR. First-order, through the projection lemma proved for a
*variable* program: no defeq step ever looks inside the program. -/
theorem lamIR_eq (num den : Var Emu (F circomPrime)) :
    lamIR num den = (lamProgram num den).toIR :=
  (IRLimbs.toIR_eq (lamProgram num den)).symm

theorem isIR_lamIR (num den : Var Emu (F circomPrime)) :
    Challenge.WitgenIR.IsIR (lamIR num den) := trivial

/-- Bridge for the `λ` witness site: the witnessed cells hold `lamValue`. -/
theorem eval_lamIR (num den : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) :
    (lamIR num den).eval env
      = lamValue (bigVal limbBits num env) (bigVal limbBits den env) :=
  IRLimbs.eval_ir_of_eq_toIR (lamIR_eq num den) (computesV_lamProgram num den) env

/-- The site reads the operands only through their limb values. -/
theorem eval_lamIR_congr (num den : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (hn : bigVal limbBits num env = bigVal limbBits num env')
    (hd : bigVal limbBits den env = bigVal limbBits den env') :
    (lamIR num den).eval env = (lamIR num den).eval env' := by
  rw [eval_lamIR, eval_lamIR, hn, hd]

attribute [irreducible] lamProgram lamIR

end Generator

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let num := input.num
  let den := input.den

  -- boolean zero flag of the denominator
  let z ← subcircuit IsZeroFe.circuit den

  -- guarded denominator/numerator: (1, 0) in the degenerate case
  let denSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := oneConst, ifFalse := den }
  let numSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := zeroConst, ifFalse := num }

  -- witness the quotient λ = num · den⁻¹ mod P256 (0 when den = 0)
  let lam ← witnessIR (fields numLimbs) (lamIR num den)

  -- λ is normalized and canonical
  Normalize.circuit secpParams lam
  LessThan.circuit secpParams { lhs := lam, rhs := pConst }

  -- certify λ · denSafe ≡ numSafe (mod P256)
  let prod ← subcircuit (MulMod.circuit secpParams)
    { a := lam, b := denSafe, modulus := pConst }
  Equal.circuit secpParams { lhs := prod, rhs := numSafe }

  return lam

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

/-- Preconditions: numerator and denominator are canonical. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.num ∧ Fe.Valid input.den

/-- Postcondition: the output is canonical; it is the field quotient when the
denominator is nonzero, and `0` otherwise. -/
def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧
    (decodeFe input.den ≠ 0 →
      decodeFe out * decodeFe input.den = decodeFe input.num) ∧
    (decodeFe input.den = 0 → decodeFe out = 0)

/-- Reduce a `Mux.Spec` hypothesis stated at an *evaluated* `Inputs` struct.
`eval` on a `ProvableStruct` literal no longer iota-reduces under `simp`/`rw`, so
the `if`-condition stays `(fromComponents …).selector = 1` and `if_pos`/`if_neg`
cannot fire. Both forms are definitionally equal, so this `id`-style lemma
transports the hypothesis to the projected form. -/
private lemma mux_spec_reduce {s : F circomPrime} {t f out : Emu (F circomPrime)}
    (h : Mux.Spec (M := Emu) ⟨s, t, f⟩ out) :
    out = if s = 1 then t else f := h

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    Normalize.circuit, Normalize.Assumptions, Normalize.Spec,
    LessThan.circuit, LessThan.Assumptions, LessThan.Spec,
    Equal.circuit, Equal.Assumptions, Equal.Spec]
  obtain ⟨h_num_valid, h_den_valid⟩ := h_assumptions
  obtain ⟨hz, hden, hnum, hlam_norm, hlt, hmul, heq⟩ := h_holds
  simp only [secpParams_B] at hlam_norm hlt hmul heq
  specialize hz h_den_valid
  have hz_bool : IsBool (env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1)) := by
    rw [hz]
    split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hden hz_bool
  specialize hnum hz_bool
  have hp_norm := pConst_normalized env
  have hp_val := pConst_value env
  have hlam_lt := hlt ⟨hlam_norm, hp_norm⟩
  rw [hp_val] at hlam_lt
  rw [hp_val] at hmul
  by_cases hd0 : decodeFe input_den = 0
  · -- zero denominator: `λ · 1 ≡ 0` forces `λ = 0`
    rw [if_pos hd0] at hz
    have hden := mux_spec_reduce (s := env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1))
      (t := Vector.map (Expression.eval env) oneConst) (f := input_den) hden
    rw [hz, if_pos rfl, eval_oneConst] at hden
    have hnum := mux_spec_reduce (s := env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1))
      (t := Vector.map (Expression.eval env) zeroConst) (f := input_num) hnum
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one] at hmul
    rw [hnum, value_emuOfNat_zero] at heq
    obtain ⟨hprod_norm, hprod_val⟩ :=
      hmul ⟨hlam_norm, emuOfNat_normalized 1, hp_norm, hlam_lt, one_lt_P256, P256_pos⟩
    have hpn := heq ⟨hprod_norm, emuOfNat_normalized 0⟩
    rw [hpn, mul_one, Nat.mod_eq_of_lt hlam_lt] at hprod_val
    exact ⟨⟨hlam_norm, hlam_lt⟩, fun h => absurd hd0 h,
      fun _ => decodeFe_of_value_eq_zero hprod_val.symm⟩
  · -- nonzero denominator: `MulMod` + `Equal` give `λ · den ≡ num (mod P256)`
    rw [if_neg hd0] at hz
    have hden := mux_spec_reduce (s := env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1))
      (t := Vector.map (Expression.eval env) oneConst) (f := input_den) hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    have hnum := mux_spec_reduce (s := env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1))
      (t := Vector.map (Expression.eval env) zeroConst) (f := input_num) hnum
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden] at hmul
    rw [hnum] at heq
    obtain ⟨hprod_norm, hprod_val⟩ :=
      hmul ⟨hlam_norm, h_den_valid.1, hp_norm, hlam_lt, h_den_valid.2, P256_pos⟩
    have hpn := heq ⟨hprod_norm, h_num_valid.1⟩
    rw [hprod_val] at hpn
    refine ⟨⟨hlam_norm, hlam_lt⟩, fun _ => ?_, fun h => absurd h hd0⟩
    simp only [decodeFe]
    exact mul_cast_of_mod_eq hpn

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [IsZeroFe.circuit, IsZeroFe.Assumptions, IsZeroFe.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec,
    MulMod.circuit, MulMod.Assumptions, MulMod.Spec,
    Normalize.circuit, Normalize.Assumptions, Normalize.Spec,
    LessThan.circuit, LessThan.Assumptions, LessThan.Spec,
    Equal.circuit, Equal.Assumptions, Equal.Spec]
  obtain ⟨h_num_valid, h_den_valid⟩ := h_assumptions
  obtain ⟨h_input_num, h_input_den⟩ := h_input
  obtain ⟨hz, hden, hnum, hlam, hmul⟩ := h_env
  simp only [secpParams_B] at hmul ⊢
  specialize hz h_den_valid
  have hz_bool : IsBool (env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1)) := by
    rw [hz]
    split
    · exact IsBool.one
    · exact IsBool.zero
  specialize hden hz_bool
  specialize hnum hz_bool
  -- the witnessed λ evaluates to the canonical quotient
  have hev_num : evalEmu env input_var_num = BigInt.value limbBits input_num := by
    rw [evalEmu, BigInt.value, ← h_input_num]
  have hev_den : evalEmu env input_var_den = BigInt.value limbBits input_den := by
    rw [evalEmu, BigInt.value, ← h_input_den]
  have hlam_eval : Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i })
      = emuOfNat (ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)) := by
    rw [← hev_num, ← hev_den]
    -- the witness-IR bridge: project the element-wise obligation back to the vector
    refine Vector.ext fun i hi => ?_
    rw [Vector.getElem_map, Vector.getElem_mapRange]
    have hbn : IRLimbs.bigVal limbBits input_var_num env = evalEmu env input_var_num :=
      IREmu.bigVal_eq_evalEmu _ _ (by rw [h_input_num]; exact h_num_valid.1)
    have hbd : IRLimbs.bigVal limbBits input_var_den env = evalEmu env input_var_den :=
      IREmu.bigVal_eq_evalEmu _ _ (by rw [h_input_den]; exact h_den_valid.1)
    have h := hlam ⟨i, hi⟩
    rw [eval_lamIR, hbn, hbd] at h
    simpa only [circuit_norm, lamValue, lamNat] using h
  have hq_lt : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
      * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) < P256 :=
    ZMod.val_lt _
  have hlam_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i })) := by
    rw [hlam_eval]
    exact emuOfNat_normalized _
  have hlam_val : BigInt.value limbBits (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i }))
      = ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
          * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) := by
    rw [hlam_eval]
    exact value_emuOfNat (lt_trans hq_lt P256_lt)
  have hp_norm := pConst_normalized env.toEnvironment
  have hp_val := pConst_value env.toEnvironment
  rw [hp_val] at hmul ⊢
  rw [hlam_val] at hmul ⊢
  by_cases hd0 : decodeFe input_den = 0
  · -- zero denominator: λ = 0 certifies against (1, 0)
    rw [if_pos hd0] at hz
    have hden := mux_spec_reduce (s := env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1))
      (t := Vector.map (Expression.eval env.toEnvironment) oneConst) (f := input_den) hden
    rw [hz, if_pos rfl, eval_oneConst] at hden
    have hnum := mux_spec_reduce (s := env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1))
      (t := Vector.map (Expression.eval env.toEnvironment) zeroConst) (f := input_num) hnum
    rw [hz, if_pos rfl, eval_zeroConst] at hnum
    rw [hden, value_emuOfNat_one] at hmul ⊢
    rw [hnum, value_emuOfNat_zero] at *
    have hq0 : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹) = 0 := by
      simp only [decodeFe] at hd0
      rw [hd0]
      exact witness_val_den_zero _
    obtain ⟨hprod_norm, hprod_val⟩ :=
      hmul ⟨hlam_norm, emuOfNat_normalized 1, hp_norm, hq_lt, one_lt_P256, P256_pos⟩
    refine ⟨h_den_valid, hz_bool, hz_bool, hlam_norm, ⟨⟨hlam_norm, hp_norm⟩, hq_lt⟩,
      ⟨hlam_norm, emuOfNat_normalized 1, hp_norm, hq_lt, one_lt_P256, P256_pos⟩,
      ⟨hprod_norm, emuOfNat_normalized 0⟩, ?_⟩
    rw [hprod_val, hq0, Nat.zero_mul, Nat.zero_mod]
  · -- nonzero denominator: λ · den ≡ num certifies against (den, num)
    rw [if_neg hd0] at hz
    have hden := mux_spec_reduce (s := env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1))
      (t := Vector.map (Expression.eval env.toEnvironment) oneConst) (f := input_den) hden
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
    have hnum := mux_spec_reduce (s := env.get (i₀ + 2 + 2 + 2 + 2 + 1 + 1))
      (t := Vector.map (Expression.eval env.toEnvironment) zeroConst) (f := input_num) hnum
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hnum
    rw [hden] at hmul ⊢
    rw [hnum] at *
    have hcert : ZMod.val (((BigInt.value limbBits input_num : ℕ) : Specs.Secp256k1.Fp)
        * ((BigInt.value limbBits input_den : ℕ) : Specs.Secp256k1.Fp)⁻¹)
          * BigInt.value limbBits input_den % P256 = BigInt.value limbBits input_num := by
      simp only [decodeFe] at hd0
      exact witness_cert_nonzero h_num_valid.2 hd0
    obtain ⟨hprod_norm, hprod_val⟩ :=
      hmul ⟨hlam_norm, h_den_valid.1, hp_norm, hq_lt, h_den_valid.2, P256_pos⟩
    refine ⟨h_den_valid, hz_bool, hz_bool, hlam_norm, ⟨⟨hlam_norm, hp_norm⟩, hq_lt⟩,
      ⟨hlam_norm, h_den_valid.1, hp_norm, hq_lt, h_den_valid.2, P256_pos⟩,
      ⟨hprod_norm, h_num_valid.1⟩, ?_⟩
    rw [hprod_val, hcert]

/-- The `DivOrZero` formal circuit: witnessed field division with a
zero-denominator guard. -/
def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

/-- An `Emu` witness output depends only on its own `numLimbs` cells, so it is
stable across environments agreeing below any `k ≥ offset + numLimbs`. -/
private theorem emuWitnessOutput_stable
    (ir : Witgen.WitgenIR (F circomPrime) numLimbs)
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((witnessIR (fields numLimbs) ir).output offset) =
      eval env' ((witnessIR (fields numLimbs) ir).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((witnessIR (fields numLimbs) ir).output offset) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((witnessIR (fields numLimbs) ir).output offset) i hi]
  simp only [circuit_norm]
  exact h_agree (offset + i) (by omega)

/-! ## Computable witnesses

`DivOrZero` chains a zero-flag (`IsZeroFe`), two `Mux` guards, a witnessed
quotient `λ`, and a certifying `MulMod`, with `Normalize`/`LessThan`/`Equal`
assertions in between. Every witness generator is a deterministic function of
the parent input and the prior subcircuit outputs, so the whole circuit is
computable. Each subcircuit is discharged through its own `computableWitnesses`
theorem; prior outputs are propagated with the producers'
`eval_output_of_agreesBelow` lemmas. -/

/-! The per-block local lengths, as standalone declarations so that the (costly)
`rfl` evaluations of the child circuits' lengths do not eat into
`computableWitnesses`' own elaboration budget. -/

private lemma hz (y : Var Emu (F circomPrime)) (o : ℕ) :
    (subcircuit IsZeroFe.circuit y).localLength o = 11 := by
  simp only [circuit_norm, IsZeroFe.circuit]

private lemma hmx (X : Var (Mux.Inputs Emu) (F circomPrime)) (o : ℕ) :
    (subcircuit (Mux.circuit (M := Emu)) X).localLength o = numLimbs := by
  simp only [circuit_norm, Mux.circuit]

private lemma hw (ir : Witgen.WitgenIR (F circomPrime) numLimbs)
    (o : ℕ) : (witnessIR (fields numLimbs) ir).localLength o = numLimbs := by
  simp only [circuit_norm]

private lemma hnl : ∀ (x : Var Emu (F circomPrime)) (o : ℕ),
    (Normalize.circuit secpParams x).localLength o = numLimbs * secpParams.B := fun _ _ => rfl

private lemma hltl : ∀ (X : Var (LessThan.Inputs numLimbs) (F circomPrime)) (o : ℕ),
    (LessThan.circuit secpParams X).localLength o
      = numLimbs + numLimbs * secpParams.B + numLimbs := fun _ _ => rfl

private lemma hmml : ∀ (X : Var (MulMod.Inputs numLimbs) (F circomPrime)) (o : ℕ),
    (subcircuit (MulMod.circuit secpParams) X).localLength o
      = numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
        + numLimbs * numLimbs + numLimbs * numLimbs
        + ((2 * numLimbs - 1) * secpParams.W + (2 * numLimbs - 1))
        + (numLimbs + numLimbs * secpParams.B + numLimbs) := fun _ _ => rfl

/-- Output agreement for a `MulMod` subcircuit block, stated for an *arbitrary*
input struct so that the (large) concrete argument is solved by unification
instead of being re-elaborated. -/
private lemma mulModOutAgree (X : Var (MulMod.Inputs numLimbs) (F circomPrime)) (o k : ℕ)
    {e e' : ProverEnvironment (F circomPrime)} (h_agree : e.AgreesBelow k e')
    (hk : o + numLimbs + numLimbs ≤ k) :
    eval e ((subcircuit (MulMod.circuit secpParams) X).output o)
      = eval e' ((subcircuit (MulMod.circuit secpParams) X).output o) := by
  have h := MulMod.eval_output_of_agreesBelow secpParams X h_agree hk
  rw [(MulMod.elaborated secpParams).output_eq X o] at h
  simp only [circuit_norm] at h ⊢
  exact h

/-- Pack per-field agreement into an `eval`-agreement on a literal `Mux.Inputs`. -/
private lemma hmux_in (e e' : ProverEnvironment (F circomPrime))
    (s : Var field (F circomPrime)) (cst f : Var Emu (F circomPrime))
    (hs : Expression.eval e.toEnvironment s = Expression.eval e'.toEnvironment s)
    (hcst : Vector.map (Expression.eval e.toEnvironment) cst
      = Vector.map (Expression.eval e'.toEnvironment) cst)
    (hf : Vector.map (Expression.eval e.toEnvironment) f
      = Vector.map (Expression.eval e'.toEnvironment) f) :
    eval e ({ selector := s, ifTrue := cst, ifFalse := f } : Var (Mux.Inputs Emu) (F circomPrime))
      = eval e' ({ selector := s, ifTrue := cst, ifFalse := f } : Var (Mux.Inputs Emu) (F circomPrime)) := by
  simp only [circuit_norm]
  simp only [hs, hcst, hf]
  exact ⟨trivial, trivial, trivial⟩

/-- Block offsets (all constant per the elaborated lengths):
`z` at `offset`, `denSafe` at `offset+11`, `numSafe` at `offset+11+numLimbs`,
`λ` at `offset+11+numLimbs+numLimbs`. -/
theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨num, den⟩ := input
  have hsize : size Emu = numLimbs := rfl
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hz, hmx, hw, hnl, hltl, hmml, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- z ← IsZeroFe den : input is the raw denominator
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (Parent := Inputs) IsZeroFe.circuit _ den offset
      (fun e e' h => by
        have hden := congrArg (fun x : Inputs (F circomPrime) => x.den) h
        simpa [circuit_norm] using hden)
      IsZeroFe.computableWitnesses env env'
  · -- denSafe ← Mux { z, oneConst, den } : selector is the prior IsZeroFe output
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _
      { selector := (subcircuit IsZeroFe.circuit den).output offset,
        ifTrue := oneConst, ifFalse := den }
      (offset + 11)
      (by
        intro k e e' hle h_agree h_in
        have hsel := IsZeroFe.eval_output_of_agreesBelow den (offset := offset) h_agree (by omega)
        rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at hsel
        have hden := congrArg (fun x : Inputs (F circomPrime) => x.den) h_in
        have hden' : Vector.map (Expression.eval e.toEnvironment) den
            = Vector.map (Expression.eval e'.toEnvironment) den := by
          simpa [circuit_norm] using hden
        exact hmux_in e e' _ oneConst den hsel (by rw [eval_oneConst, eval_oneConst]) hden')
      (Mux.computableWitnesses (M := Emu)) env env'
  · -- numSafe ← Mux { z, zeroConst, num } : selector is the prior IsZeroFe output
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Mux.circuit (M := Emu)) _
      { selector := (subcircuit IsZeroFe.circuit den).output offset,
        ifTrue := zeroConst, ifFalse := num }
      (offset + 11 + numLimbs)
      (by
        intro k e e' hle h_agree h_in
        have hsel := IsZeroFe.eval_output_of_agreesBelow den (offset := offset) h_agree (by omega)
        rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at hsel
        have hnum := congrArg (fun x : Inputs (F circomPrime) => x.num) h_in
        have hnum' : Vector.map (Expression.eval e.toEnvironment) num
            = Vector.map (Expression.eval e'.toEnvironment) num := by
          simpa [circuit_norm] using hnum
        exact hmux_in e e' _ zeroConst num hsel (by rw [eval_zeroConst, eval_zeroConst]) hnum')
      (Mux.computableWitnesses (M := Emu)) env env'
  · -- λ witness : reads only the raw input limbs (via evalEmu)
    rw [Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessIR_structuralComputableWitnesses_iff]
    intro _ h_input
    have hden : IRLimbs.bigVal limbBits den env = IRLimbs.bigVal limbBits den env' :=
      IREmu.bigVal_stable _ (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.den) h_input)
    have hnum : IRLimbs.bigVal limbBits num env = IRLimbs.bigVal limbBits num env' :=
      IREmu.bigVal_stable _ (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.num) h_input)
    exact eval_lamIR_congr num den hnum hden
  · -- Normalize λ : input is the prior witness `λ` (a single `Var Emu`)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Normalize.circuit secpParams) _
      ((witnessIR (fields numLimbs) (lamIR num den)).output
        (offset + 11 + numLimbs + numLimbs))
      _
      (by
        intro k e e' hle h_agree _
        exact emuWitnessOutput_stable _ h_agree
          (offset := offset + 11 + numLimbs + numLimbs) (by omega))
      (Normalize.computableWitnesses secpParams) env env'
  · -- LessThan { λ, pConst } : λ prior witness, pConst constant
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (LessThan.circuit secpParams) _
      { lhs := (witnessIR (fields numLimbs) (lamIR num den)).output
          (offset + 11 + numLimbs + numLimbs),
        rhs := pConst }
      _
      (by
        intro k e e' hle h_agree _
        have hlam := emuWitnessOutput_stable (lamIR num den)
          h_agree (offset := offset + 11 + numLimbs + numLimbs) (k := k) (by omega)
        simp only [circuit_norm] at hlam ⊢
        simp only [hlam, eval_pConst]
        exact ⟨trivial, trivial⟩)
      (LessThan.computableWitnesses secpParams) env env'
  · -- prod ← MulMod { λ, denSafe, pConst } : λ prior witness, denSafe prior Mux output
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (MulMod.circuit secpParams) _
      { a := (witnessIR (fields numLimbs) (lamIR num den)).output
          (offset + 11 + numLimbs + numLimbs),
        b := (subcircuit (Mux.circuit (M := Emu))
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := oneConst, ifFalse := den }).output (offset + 11),
        modulus := pConst }
      _
      (by
        intro k e e' hle h_agree _
        have hlam := emuWitnessOutput_stable (lamIR num den)
          h_agree (offset := offset + 11 + numLimbs + numLimbs) (k := k) (by omega)
        have hden := Mux.eval_output_of_agreesBelow (M := Emu)
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := oneConst, ifFalse := den }
          h_agree (offset := offset + 11) (k := k) (by omega)
        simp only [circuit_norm]
        refine ⟨?_, ?_, ?_⟩
        · exact emu_map_eval_eq_of_eval_eq hlam
        · exact emu_map_eval_eq_of_eval_eq hden
        · rw [eval_pConst, eval_pConst])
      (MulMod.computableWitnesses secpParams) env env'
  · -- Equal { prod, numSafe } : prod the MulMod output, numSafe the prior Mux output
    apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (circuit := Equal.circuit secpParams)
      (n := offset + 11 + numLimbs + numLimbs + numLimbs + numLimbs * secpParams.B
          + (numLimbs + numLimbs * secpParams.B + numLimbs)
        + (numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
            + numLimbs * numLimbs + numLimbs * numLimbs
            + ((2 * numLimbs - 1) * secpParams.W + (2 * numLimbs - 1))
            + (numLimbs + numLimbs * secpParams.B + numLimbs)))
      (hcircuit := Equal.computableWitnesses secpParams)
    intro k e e' hle h_agree _
    -- split first, so each field's agreement is unified against a small goal
    refine Equal.eval_inputs_mk ?_ ?_
    · refine emu_map_eval_eq_of_eval_eq (mulModOutAgree _
        (offset + 11 + numLimbs + numLimbs + numLimbs + numLimbs * secpParams.B
          + (numLimbs + numLimbs * secpParams.B + numLimbs)) k h_agree ?_)
      -- `omega` unfolds the parameter projections into four-digit literals here and
      -- blows the heartbeat budget; keep them symbolic.
      generalize secpParams.B = B at hle ⊢
      generalize secpParams.W = W at hle ⊢
      generalize numLimbs = nl at hle ⊢
      omega
    · refine emu_map_eval_eq_of_eval_eq
        (Mux.eval_output_of_agreesBelow (M := Emu)
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := zeroConst, ifFalse := num } h_agree
          (offset := offset + 11 + numLimbs) (k := k) ?_)
      rw [hsize]
      generalize secpParams.B = B at hle ⊢
      generalize secpParams.W = W at hle ⊢
      generalize numLimbs = nl at hle ⊢
      omega

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

/-- The output of `DivOrZero.main` is the witnessed quotient `λ`, allocated at
`offset + 11 + numLimbs + numLimbs` (after the zero flag and the two `Mux`
guards) and reading only its `numLimbs` cells. Environments agreeing below any
`k ≥ offset + 11 + numLimbs + numLimbs + numLimbs` evaluate the output
identically. Consumed by `CompleteAdd`. -/
lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env')
    (hk : offset + 11 + numLimbs + numLimbs + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  obtain ⟨num, den⟩ := input
  have hout : (main ⟨num, den⟩).output offset
      = (witnessIR (fields numLimbs) (lamIR num den)).output
          (offset + 11 + numLimbs + numLimbs) := rfl
  rw [hout]
  exact emuWitnessOutput_stable _ h_agree (by omega)

end DivOrZero
end Solution.Secp256k1ScalarMul
