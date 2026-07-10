import Solution.KeccakF1600.XorLane
import Solution.KeccakF1600.AndLane

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace ChiLane

structure Inputs (F : Type) where
  a : fields 64 F
  b : fields 64 F
  c : fields 64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let t ← AndLane.circuit ⟨notBits input.b, input.c⟩
  XorLane.circuit ⟨input.a, t⟩

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c

def Spec (input : Inputs (F p)) (z : fields 64 (F p)) : Prop :=
  valueBits z =
    (valueBits input.a ^^^
      (Specs.Keccak.notLane 64 (valueBits input.b) &&& valueBits input.c))
  ∧ Normalized z

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 64) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main, AndLane.circuit, XorLane.circuit]
  simp only [AndLane.Assumptions, AndLane.Spec, XorLane.Assumptions, XorLane.Spec,
    and_imp] at h_holds
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  obtain ⟨c1, c2⟩ := h_holds
  obtain ⟨v1, n1⟩ := c1 (Normalized_eval_notBits env input_var_b input_b h_input_b hb) hc
  obtain ⟨v2, n2⟩ := c2 ha n1
  refine ⟨?_, n2⟩
  rw [v2, v1, valueBits_eval_notBits env input_var_b input_b h_input_b hb]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [main, AndLane.circuit, XorLane.circuit]
  simp only [AndLane.Assumptions, AndLane.Spec, XorLane.Assumptions, XorLane.Spec,
    and_imp] at h_env ⊢
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  obtain ⟨c1, _⟩ := h_env
  obtain ⟨_, n1⟩ := c1
    (Normalized_eval_notBits env.toEnvironment input_var_b input_b h_input_b hb) hc
  exact ⟨⟨Normalized_eval_notBits env.toEnvironment input_var_b input_b h_input_b hb, hc⟩,
    ha, n1⟩

def circuit : FormalCircuit (F p) Inputs (fields 64) where
  main; elaborated; Assumptions; Spec; soundness; completeness

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let firstInput : Var AndLane.Inputs (F p) := ⟨notBits input.b, input.c⟩
  let first : Circuit (F p) (Var (fields 64) (F p)) := AndLane.circuit firstInput
  let r1 := first.output offset
  let n1 := offset + first.localLength offset
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  and_intros
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      AndLane.circuit input firstInput offset
      (by
        intro env env' h_input
        simp [circuit_norm] at h_input ⊢
        constructor
        · intro a ha
          simp only [firstInput, notBits, Vector.mem_map] at ha
          obtain ⟨b, hb, rfl⟩ := ha
          have heq := h_input.2.1 b hb
          simp [Expression.eval, heq]
        · exact h_input.2.2)
      AndLane.computableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      XorLane.circuit input ⟨input.a, r1⟩ n1
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm] at h_input
        simp [circuit_norm]
        constructor
        · exact h_input.1
        · have hlen : first.localLength offset = 64 := by
            dsimp [first, firstInput, AndLane.circuit]
            rfl
          exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
            h_agree (by omega))
      XorLane.computableWitnesses env env'

end ChiLane
end Solution.KeccakF1600
end
