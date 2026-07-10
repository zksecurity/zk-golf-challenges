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

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { num, den } := input

  -- boolean zero flag of the denominator
  let z ← subcircuit IsZeroFe.circuit den

  -- guarded denominator/numerator: (1, 0) in the degenerate case
  let denSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := oneConst, ifFalse := den }
  let numSafe ← subcircuit (Mux.circuit (M := Emu))
    { selector := z, ifTrue := zeroConst, ifFalse := num }

  -- witness the quotient λ = num · den⁻¹ mod P256 (0 when den = 0)
  let lam ← ProvableType.witness (α := Emu) fun env =>
    let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
    let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
    emuOfNat (numFp * denFp⁻¹).val

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
    rw [hz, if_pos rfl, eval_oneConst] at hden
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
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
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
    apply Vector.ext
    intro k hk
    have hentry : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + 11 + numLimbs + numLimbs + i }))[k]'hk
        = env.get (i₀ + 11 + numLimbs + numLimbs + k) := by
      simp [circuit_norm]
    rw [hentry]
    exact hlam ⟨k, hk⟩
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
    rw [hz, if_pos rfl, eval_oneConst] at hden
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
    rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden
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
    (compute : ProverEnvironment (F circomPrime) → Emu (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((ProvableType.witness (α := Emu) compute).output offset) =
      eval env' ((ProvableType.witness (α := Emu) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((ProvableType.witness (α := Emu) compute).output offset) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((ProvableType.witness (α := Emu) compute).output offset) i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)

/-! ## Computable witnesses

`DivOrZero` chains a zero-flag (`IsZeroFe`), two `Mux` guards, a witnessed
quotient `λ`, and a certifying `MulMod`, with `Normalize`/`LessThan`/`Equal`
assertions in between. Every witness generator is a deterministic function of
the parent input and the prior subcircuit outputs, so the whole circuit is
computable. Each subcircuit is discharged through its own `computableWitnesses`
theorem; prior outputs are propagated with the producers'
`eval_output_of_agreesBelow` lemmas. -/

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
  -- constant local lengths, so the running offset stays concrete up to `λ`
  have hz : ∀ (o : ℕ), (subcircuit IsZeroFe.circuit den).localLength o = 11 := by
    intro o; simp only [circuit_norm, IsZeroFe.circuit]
  have hmx : ∀ (X : Var (Mux.Inputs Emu) (F circomPrime)) (o : ℕ),
      (subcircuit (Mux.circuit (M := Emu)) X).localLength o = numLimbs := by
    intro X o; simp only [circuit_norm, Mux.circuit]
  have hw : ∀ (c : ProverEnvironment (F circomPrime) → Emu (F circomPrime)) (o : ℕ),
      (ProvableType.witness (α := Emu) c).localLength o = numLimbs := by
    intro c o; simp only [circuit_norm]
  have hsize : size Emu = numLimbs := rfl
  have hnl : ∀ (x : Var Emu (F circomPrime)) (o : ℕ),
      (Normalize.circuit secpParams x).localLength o = numLimbs * secpParams.B := fun _ _ => rfl
  have hltl : ∀ (X : Var (LessThan.Inputs numLimbs) (F circomPrime)) (o : ℕ),
      (LessThan.circuit secpParams X).localLength o
        = numLimbs + numLimbs * secpParams.B + numLimbs := fun _ _ => rfl
  have hmml : ∀ (X : Var (MulMod.Inputs numLimbs) (F circomPrime)) (o : ℕ),
      (subcircuit (MulMod.circuit secpParams) X).localLength o
        = numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
          + numLimbs * numLimbs + numLimbs * numLimbs
          + ((2 * numLimbs - 1) * secpParams.W + (2 * numLimbs - 1))
          + (numLimbs + numLimbs * secpParams.B + numLimbs) := fun _ _ => rfl
  -- the guarded denominator/numerator `Mux` blocks (constant `size Emu`)
  have hmux_in : ∀ (e e' : ProverEnvironment (F circomPrime))
      (s : Var field (F circomPrime)) (cst f : Var Emu (F circomPrime)),
      Expression.eval e.toEnvironment s = Expression.eval e'.toEnvironment s →
      Vector.map (Expression.eval e.toEnvironment) cst
        = Vector.map (Expression.eval e'.toEnvironment) cst →
      Vector.map (Expression.eval e.toEnvironment) f
        = Vector.map (Expression.eval e'.toEnvironment) f →
      eval e ({ selector := s, ifTrue := cst, ifFalse := f } : Var (Mux.Inputs Emu) (F circomPrime))
        = eval e' ({ selector := s, ifTrue := cst, ifFalse := f } : Var (Mux.Inputs Emu) (F circomPrime)) := by
    intro e e' s cst f hs hcst hf
    simp only [circuit_norm]
    simp only [hs, hcst, hf]
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
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
    intro _ h_input
    have hden : evalEmu env den = evalEmu env' den :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.den) h_input)
    have hnum : evalEmu env num = evalEmu env' num :=
      evalEmu_eq_of_eval_eq (by
        simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.num) h_input)
    simp only [hden, hnum]
  · -- Normalize λ : input is the prior witness `λ` (a single `Var Emu`)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Normalize.circuit secpParams) _
      ((ProvableType.witness (α := Emu) fun env =>
        let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
        let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
        emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs))
      _
      (by
        intro k e e' hle h_agree _
        exact emuWitnessOutput_stable _ h_agree
          (offset := offset + 11 + numLimbs + numLimbs) (by omega))
      (Normalize.computableWitnesses secpParams) env env'
  · -- LessThan { λ, pConst } : λ prior witness, pConst constant
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (LessThan.circuit secpParams) _
      { lhs := (ProvableType.witness (α := Emu) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs),
        rhs := pConst }
      _
      (by
        intro k e e' hle h_agree _
        have hlam := emuWitnessOutput_stable
          (fun env =>
            let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
            let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
            emuOfNat (numFp * denFp⁻¹).val)
          h_agree (offset := offset + 11 + numLimbs + numLimbs) (k := k) (by omega)
        simp only [circuit_norm] at hlam ⊢
        simp only [hlam, eval_pConst])
      (LessThan.computableWitnesses secpParams) env env'
  · -- prod ← MulMod { λ, denSafe, pConst } : λ prior witness, denSafe prior Mux output
    exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (MulMod.circuit secpParams) _
      { a := (ProvableType.witness (α := Emu) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs),
        b := (subcircuit (Mux.circuit (M := Emu))
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := oneConst, ifFalse := den }).output (offset + 11),
        modulus := pConst }
      _
      (by
        intro k e e' hle h_agree _
        have hlam := emuWitnessOutput_stable
          (fun env =>
            let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
            let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
            emuOfNat (numFp * denFp⁻¹).val)
          h_agree (offset := offset + 11 + numLimbs + numLimbs) (k := k) (by omega)
        have hden := Mux.eval_output_of_agreesBelow (M := Emu)
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := oneConst, ifFalse := den }
          h_agree (offset := offset + 11) (k := k) (by omega)
        simp only [circuit_norm]
        congr 1
        · exact emu_map_eval_eq_of_eval_eq hlam
        · exact emu_map_eval_eq_of_eval_eq hden
        · rw [eval_pConst, eval_pConst])
      (MulMod.computableWitnesses secpParams) env env'
  · -- Equal { prod, numSafe } : prod the MulMod output, numSafe the prior Mux output
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Parent := Inputs) (Equal.circuit secpParams) _
      { lhs := (subcircuit (MulMod.circuit secpParams)
          { a := (ProvableType.witness (α := Emu) fun env =>
              let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
              let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
              emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs),
            b := (subcircuit (Mux.circuit (M := Emu))
              { selector := (subcircuit IsZeroFe.circuit den).output offset,
                ifTrue := oneConst, ifFalse := den }).output (offset + 11),
            modulus := pConst }).output _,
        rhs := (subcircuit (Mux.circuit (M := Emu))
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := zeroConst, ifFalse := num }).output (offset + 11 + numLimbs) }
      _
      (by
        intro k e e' hle h_agree _
        have hnum := Mux.eval_output_of_agreesBelow (M := Emu)
          { selector := (subcircuit IsZeroFe.circuit den).output offset,
            ifTrue := zeroConst, ifFalse := num }
          h_agree (offset := offset + 11 + numLimbs) (k := k) (by omega)
        simp only [circuit_norm]
        congr 1
        · -- λ · denSafe product : the `MulMod` remainder block
          exact emu_map_eval_eq_of_eval_eq
            (MulMod.eval_output_of_agreesBelow secpParams
              { a := (ProvableType.witness (α := Emu) fun env =>
                  let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
                  let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
                  emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs),
                b := (subcircuit (Mux.circuit (M := Emu))
                  { selector := (subcircuit IsZeroFe.circuit den).output offset,
                    ifTrue := oneConst, ifFalse := den }).output (offset + 11),
                modulus := pConst }
              h_agree (offset := offset + 11 + numLimbs + numLimbs + numLimbs
                + numLimbs * secpParams.B + (numLimbs + numLimbs * secpParams.B + numLimbs))
              (k := k) (by omega))
        · exact emu_map_eval_eq_of_eval_eq hnum)
      (Equal.computableWitnesses secpParams) env env'

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
      = (ProvableType.witness (α := Emu) fun env =>
          let denFp : Specs.Secp256k1.Fp := ((evalEmu env den : ℕ) : Specs.Secp256k1.Fp)
          let numFp : Specs.Secp256k1.Fp := ((evalEmu env num : ℕ) : Specs.Secp256k1.Fp)
          emuOfNat (numFp * denFp⁻¹).val).output (offset + 11 + numLimbs + numLimbs) := rfl
  rw [hout]
  exact emuWitnessOutput_stable _ h_agree (by omega)

end DivOrZero
end Solution.Secp256k1ScalarMul
