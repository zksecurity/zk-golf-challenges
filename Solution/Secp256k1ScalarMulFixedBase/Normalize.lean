import Solution.Secp256k1ScalarMulFixedBase.Theorems
import Challenge.Utils.ComputableWitnessLemmas

/-!
# RSA big-integer range-check gadget — `Normalize`

The `BigInt m` type, its denotation (`BigInt.value`, `BigInt.Normalized`) and the
supporting lemmas live in `Circuits.RSA.Theorems`; here we define the `Normalize`
gadget (**G1**): a `FormalAssertion` that range-checks every limb to `B` bits,
establishing `Normalized`.

Soundness and completeness are fully proved.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

/-! ## G1 — `Normalize`

Range-check every limb of a `BigInt m` to `B` bits, establishing `Normalized`.
-/

namespace Normalize

/-- The `main` circuit of `Normalize`: range-check every limb of the big integer
`x` to `B` bits, reusing `Gadgets.ToBits.rangeCheck B hB` (a per-limb
bit-decomposition range check) as a subcircuit on each limb. -/
def main (P : BigIntParams p m) [Fact (p > 2)] (x : Var (BigInt m) (F p)) :
    Circuit (F p) Unit :=
  Circuit.forEach x (fun xi => Gadgets.ToBits.rangeCheck P.B P.hB xi)

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (BigInt m) unit (main P) where
  localLength _ := m * P.B
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]

/-- No preconditions: any big integer can be range-checked. -/
def Assumptions (_ : BigInt m (F p)) : Prop := True

/-- Postcondition: every limb is a canonical `B`-bit value. -/
def Spec (B : ℕ) (x : BigInt m (F p)) : Prop := BigInt.Normalized B x

/-- The `Normalize` formal assertion (gadget **G1**): each limb of `x` is a
`B`-bit value, establishing `Normalized`. -/
def circuit (P : BigIntParams p m) [Fact (p > 2)] : FormalAssertion (F p) (BigInt m) where
  main := main P
  Assumptions := Assumptions
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    simp_all only [circuit_norm, Gadgets.ToBits.rangeCheck, BigInt.Normalized]
    intro i
    rw [← h_input, Vector.getElem_map]
    exact h_holds i
  completeness := by
    circuit_proof_start
    simp_all only [circuit_norm, Gadgets.ToBits.rangeCheck, BigInt.Normalized]
    intro i
    have := h_spec i
    rwa [← h_input, Vector.getElem_map] at this

theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  intro i
  apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses
  · intro env₁ env₂ h_input
    have h : (eval env₁ input)[i.val] = (eval env₂ input)[i.val] := by
      simpa only [Fin.getElem_fin] using congrArg (fun x : BigInt m (F p) => x[i]) h_input
    rw [← ProvableType.getElem_eval_fields_prover (env := env₁) input i.val i.isLt,
      ← ProvableType.getElem_eval_fields_prover (env := env₂) input i.val i.isLt] at h
    simpa [CircuitType.eval_expression_prover_to_verifier (M := field),
      CircuitType.eval_expression (M := field), ProvableType.eval, explicit_provable_type] using h
  · exact rangeCheckComputableWitnesses P.B P.hB

theorem computableWitness (P : BigIntParams p m) [Fact (p > 2)] : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main P input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P)

end Normalize

end

end Solution.Secp256k1ScalarMulFixedBase
