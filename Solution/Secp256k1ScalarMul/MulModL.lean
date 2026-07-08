import Solution.Secp256k1ScalarMul.MulModLTheorems
import Solution.Secp256k1ScalarMul.AddModTheorems

/-!
# Emulated field multiplication, *lazy* variant — `MulModL`

`FormalCircuit` computing `c ≡ a · b (mod P256)` with the modulus fixed to the
secp256k1 prime (`pConst`). Like `AddModL`/`SubModL` it omits the `LessThan`
canonical check: the output is normalized-only, spec via `decodeFe`.

The first operand `a` must be canonical (`< P256`) so the honest quotient
`q = a·b / P256 < 2^256` fits in `numLimbs` limbs; the second operand `b` may be
loose (merely normalized), which is what lets a `MulModL` sit at the end of a
lazy chain.
-/

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

namespace MulModL

/-- Inputs of `MulModL`: canonical `a` and normalized (loose) `b`. -/
structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  let q ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (evalEmu env a * evalEmu env b / P256)
  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (evalEmu env a * evalEmu env b % P256)

  Normalize.circuit secpParams q
  Normalize.circuit secpParams r

  let Pc ← MulMod.witnessedMul a b
  let Sqn ← MulMod.witnessedMul q pConst
  let S : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then Sqn[k.val] + r[k.val]'h else Sqn[k.val]
  EqViaCarries.circuit secpParams { lhs := Pc, rhs := S }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main where
  localLength _ :=
    numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
      + (numLimbs * numLimbs) + (numLimbs * numLimbs)
      + ((2 * numLimbs - 1) * secpParams.W + (2 * numLimbs - 1))
  output _ i0 := varFromOffset Emu (i0 + numLimbs)
  localLength_eq := by
    intro input offset
    simp only [main, MulMod.witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, MulMod.witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, MulMod.witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, MulMod.witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      Gadgets.ToBits.rangeCheck]

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.a ∧ input.b.Normalized limbBits

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  out.Normalized limbBits ∧ decodeFe out = decodeFe input.a * decodeFe input.b

set_option maxHeartbeats 1000000 in
def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main
  elaborated
  Assumptions
  Spec
  soundness := by
    circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
      Normalize.Assumptions, Normalize.Spec,
      EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      EqViaCarries.Assumptions, EqViaCarries.Spec]
    obtain ⟨ha_valid, hb_norm⟩ := h_assumptions
    obtain ⟨hq_norm, hr_norm, hAB_ops, hQN_ops, h_eq_impl⟩ := h_holds
    have hp := secpParams.hp
    have h_pAB := MulMod.witnessedMul_soundness
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)
      input_var_a input_var_b env hAB_ops
    have h_pQN := MulMod.witnessedMul_soundness
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
        + Operations.localLength (MulMod.witnessedMul input_var_a input_var_b
          (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).2)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }) pConst env hQN_ops
    refine ⟨?_, MulMod.witnessedMul_requirements _ _ _ _, MulMod.witnessedMul_requirements _ _ _ _⟩
    have h_input' : (Vector.map (Expression.eval env) input_var_a,
        Vector.map (Expression.eval env) input_var_b,
        Vector.map (Expression.eval env) pConst)
          = ((input_a, input_b, Vector.map (Expression.eval env) pConst) :
            ProvablePair (BigInt numLimbs) (ProvablePair (BigInt numLimbs) (BigInt numLimbs))
              (F circomPrime)) := by
      simp only [h_input.1, h_input.2]
    have heqAB_get := MulMod.witnessedMul_eval_bridge env
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)
      input_var_a input_var_b h_pAB
    have heqQN_get := MulMod.witnessedMul_eval_bridge env
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
        + Operations.localLength (MulMod.witnessedMul input_var_a input_var_b
          (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).2)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }) pConst h_pQN
    obtain ⟨hrn, hid⟩ := MulMod.mulMod_soundness_core_wm_loose (B := secpParams.B) hp i₀ env
      input_var_a input_var_b pConst
      (MulMod.witnessedMul input_var_a input_var_b
        (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).1
      (MulMod.witnessedMul (Vector.mapRange numLimbs fun i => var { index := i₀ + i }) pConst
        (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
          + Operations.localLength (MulMod.witnessedMul input_var_a input_var_b
            (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).2)).1
      (input_a, input_b, Vector.map (Expression.eval env) pConst) h_input'
      ha_valid.1 hb_norm (pConst_normalized env) hq_norm hr_norm heqAB_get heqQN_get h_eq_impl
    refine ⟨hrn, ?_⟩
    rw [show BigInt.value secpParams.B (Vector.map (Expression.eval env) pConst) = P256 from
      pConst_value env] at hid
    have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) hid
    push_cast at hcast
    rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _,
      mul_zero, zero_add] at hcast
    simp only [decodeFe]
    exact hcast.symm
  completeness := by
    circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
      Normalize.Assumptions, Normalize.Spec,
      EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      EqViaCarries.Assumptions, EqViaCarries.Spec]
    obtain ⟨ha_valid, hb_norm⟩ := h_assumptions
    obtain ⟨hq_env, hr_env, hAB_uses, hQN_uses⟩ := h_env
    have hp := secpParams.hp
    have h_pvAB := MulMod.witnessedMul_usesLocalWitnesses
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)
      input_var_a input_var_b env rfl hAB_uses
    have h_pvQN := MulMod.witnessedMul_usesLocalWitnesses
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
        + Operations.localLength (MulMod.witnessedMul input_var_a input_var_b
          (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).2)
      (Operations.localLength (MulMod.witnessedMul input_var_a input_var_b
          (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).2
        + (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B))
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }) pConst env
      (Nat.add_comm _ _) hQN_uses
    have h_pAB : ∀ t : Fin (numLimbs * numLimbs),
        Expression.eval env.toEnvironment (input_var_a[t.val / numLimbs]'(Nat.div_lt_of_lt_mul t.isLt))
            * Expression.eval env.toEnvironment (input_var_b[t.val % numLimbs]'(Nat.mod_lt _ (Nat.pos_of_neZero numLimbs)))
          = env.toEnvironment.get
              ((i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B) + t.val) :=
      fun t => (h_pvAB t).symm
    have h_pQN : ∀ t : Fin (numLimbs * numLimbs),
        Expression.eval env.toEnvironment
            ((Vector.mapRange numLimbs fun i => var { index := i₀ + i })[t.val / numLimbs]'(Nat.div_lt_of_lt_mul t.isLt))
            * Expression.eval env.toEnvironment (pConst[t.val % numLimbs]'(Nat.mod_lt _ (Nat.pos_of_neZero numLimbs)))
          = env.toEnvironment.get
              ((i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
                + Operations.localLength (MulMod.witnessedMul input_var_a input_var_b
                  (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).2) + t.val) :=
      fun t => (h_pvQN t).symm
    have heva : evalEmu env input_var_a = BigInt.value limbBits input_a := by
      rw [evalEmu, BigInt.value, ← h_input.1]
    have hevb : evalEmu env input_var_b = BigInt.value limbBits input_b := by
      rw [evalEmu, BigInt.value, ← h_input.2]
    have hpv : BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) pConst) = P256 :=
      pConst_value env.toEnvironment
    have hqwit : ∀ i : Fin numLimbs, env.toEnvironment.get (i₀ + i.val)
        = ((BigInt.value secpParams.B input_a * BigInt.value secpParams.B input_b
            / BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) pConst)
            / 2 ^ (secpParams.B * i.val) % 2 ^ secpParams.B : ℕ) : F circomPrime) := by
      intro i
      rw [hq_env i, emuOfNat_getElem _ i.val i.isLt, heva, hevb, hpv]
      rfl
    have hrwit : ∀ i : Fin numLimbs, env.toEnvironment.get (i₀ + numLimbs + i.val)
        = ((BigInt.value secpParams.B input_a * BigInt.value secpParams.B input_b
            % BigInt.value secpParams.B (Vector.map (Expression.eval env.toEnvironment) pConst)
            / 2 ^ (secpParams.B * i.val) % 2 ^ secpParams.B : ℕ) : F circomPrime) := by
      intro i
      rw [hr_env i, emuOfNat_getElem _ i.val i.isLt, heva, hevb, hpv]
      rfl
    have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var_a,
        Vector.map (Expression.eval env.toEnvironment) input_var_b,
        Vector.map (Expression.eval env.toEnvironment) pConst)
          = ((input_a, input_b, Vector.map (Expression.eval env.toEnvironment) pConst) :
            ProvablePair (BigInt numLimbs) (ProvablePair (BigInt numLimbs) (BigInt numLimbs))
              (F circomPrime)) := by
      simp only [h_input.1, h_input.2]
    have heqAB_get := MulMod.witnessedMul_eval_bridge env.toEnvironment
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)
      input_var_a input_var_b h_pAB
    have heqQN_get := MulMod.witnessedMul_eval_bridge env.toEnvironment
      (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
        + Operations.localLength (MulMod.witnessedMul input_var_a input_var_b
          (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).2)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }) pConst h_pQN
    have core := MulMod.mulMod_completeness_core_wm_loose (B := secpParams.B) secpParams.hB hp i₀
      env.toEnvironment input_var_a input_var_b pConst
      (MulMod.witnessedMul input_var_a input_var_b
        (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).1
      (MulMod.witnessedMul (Vector.mapRange numLimbs fun i => var { index := i₀ + i }) pConst
        (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B
          + Operations.localLength (MulMod.witnessedMul input_var_a input_var_b
            (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)).2)).1
      (input_a, input_b, Vector.map (Expression.eval env.toEnvironment) pConst) h_input'
      ha_valid.1 hb_norm (pConst_normalized env.toEnvironment)
      (by rw [hpv]; exact ha_valid.2) (by rw [hpv]; exact P256_pos)
      hqwit hrwit heqAB_get heqQN_get
    exact ⟨core.1, core.2.1,
      MulMod.witnessedMul_completeness
        (i₀ + numLimbs + numLimbs + numLimbs * secpParams.B + numLimbs * secpParams.B)
        input_var_a input_var_b env h_pvAB,
      MulMod.witnessedMul_completeness _
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i }) pConst env h_pvQN,
      core.2.2⟩

end MulModL

end Solution.Secp256k1ScalarMul
