import Solution.Secp256k1ScalarMulFixedBase.Theorems
import Challenge.Utils.ComputableWitnessLemmas

/-!
# RSA big-integer equality gadget — `Equal`

`Equal` is a `FormalAssertion` asserting two normalized big integers are limb-wise
equal (hence denote the same natural number). The `BigInt m` type and its
denotation live in `Circuits.RSA.Theorems`.

Soundness and completeness are fully proved.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

/-! ## `Equal`

Assert two normalized big integers are limb-wise equal, hence denote the same
natural number.
-/

namespace Equal

private theorem equalityComputableWitnesses (M : TypeMap) [ProvableType M] :
    (Gadgets.Equality.circuit (F := F p) M).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((Gadgets.Equality.circuit (F := F p) M).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  obtain ⟨x, y⟩ := input
  simp only [Gadgets.Equality.circuit, Gadgets.Equality.main, circuit_norm]

/-- Inputs of `Equal`: the two big integers `lhs` and `rhs` to compare. -/
structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

/-- Per-field projection of an `eval`-agreement hypothesis on the `Inputs` struct.
The `Var Inputs` `match` no longer iota-reduces on a struct *variable*, so the
destructuring has to happen here, once. -/
lemma eval_inputs_parts {input : Var (Inputs m) (F p)} {env env' : Environment (F p)}
    (h : eval env input = eval env' input) :
    eval env input.lhs = eval env' input.lhs ∧ eval env input.rhs = eval env' input.rhs := by
  obtain ⟨lhs, rhs⟩ := input
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h ⊢
  exact h

/-- Build an `eval`-agreement on a literal `Inputs` struct out of per-field
agreement. The `Var Inputs` components list no longer iota-reduces on its own, so
the packing happens here, once. -/
lemma eval_inputs_mk {lhs rhs : Var (BigInt m) (F p)}
    {env env' : ProverEnvironment (F p)}
    (hl : Vector.map (Expression.eval env.toEnvironment) lhs
        = Vector.map (Expression.eval env'.toEnvironment) lhs)
    (hr : Vector.map (Expression.eval env.toEnvironment) rhs
        = Vector.map (Expression.eval env'.toEnvironment) rhs) :
    eval env ({ lhs := lhs, rhs := rhs } : Var (Inputs m) (F p))
      = eval env' ({ lhs := lhs, rhs := rhs } : Var (Inputs m) (F p)) := by
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq]
  exact ⟨hl, hr⟩

/-- The `main` circuit of `Equal`: assert the two big integers are limb-wise
equal (`lhs === rhs`). -/
def main (input : Var (Inputs m) (F p)) : Circuit (F p) Unit :=
  input.lhs === input.rhs

instance elaborated : ElaboratedCircuit (F p) (Inputs m) unit main where
  localLength _ := 0

/-- Preconditions: both big integers are normalized. -/
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B

/-- Postcondition: the two big integers denote the same natural number. -/
def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B = input.rhs.value B

/-- The `Equal` formal assertion: two normalized big integers are limb-wise
equal, hence denote the same natural number. -/
def circuit (P : BigIntParams p m) : FormalAssertion (F p) (Inputs m) where
  main := main
  Assumptions := Assumptions P.B
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    rw [h_holds]
  completeness := by
    circuit_proof_start
    exact BigInt.value_inj h_assumptions.1 h_assumptions.2 h_spec

theorem computableWitnesses (P : BigIntParams p m) : (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [HasAssertEq.assert_eq, assertEquals, Gadgets.Equality.circuit]
  rw [Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses
  · intro _ _ h_input
    rw [
      CircuitType.eval_expression_prover_to_verifier (M := ProvablePair (fields m) (fields m)),
      CircuitType.eval_expression_prover_to_verifier (M := ProvablePair (fields m) (fields m))]
    rw [eval_pair, eval_pair]
    rw [
      CircuitType.eval_expression_prover_to_verifier (M := Inputs m),
      CircuitType.eval_expression_prover_to_verifier (M := Inputs m)] at h_input
    apply Prod.ext
    · exact (eval_inputs_parts h_input).1
    · exact (eval_inputs_parts h_input).2
  · exact equalityComputableWitnesses (p := p) (fields m)

theorem computableWitness (P : BigIntParams p m) : ∀ n (input : Var (Inputs m) (F p)),
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P)

end Equal

end

end Solution.Secp256k1ScalarMulFixedBase
