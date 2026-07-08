import Solution.Secp256k1ScalarMulFixedBase.IsZeroFe
import Solution.Secp256k1ScalarMulFixedBase.Mux
import Solution.Secp256k1ScalarMulFixedBase.DivOrZeroTheorems

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

namespace Solution.Secp256k1ScalarMulFixedBase
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

end DivOrZero
end Solution.Secp256k1ScalarMulFixedBase
