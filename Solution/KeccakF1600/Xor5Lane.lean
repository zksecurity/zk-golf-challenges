import Solution.KeccakF1600.XorLane

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace Xor5Lane

structure Inputs (F : Type) where
  a : fields 64 F
  b : fields 64 F
  c : fields 64 F
  d : fields 64 F
  e : fields 64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let t ← XorLane.circuit ⟨input.a, input.b⟩
  let t ← XorLane.circuit ⟨t, input.c⟩
  let t ← XorLane.circuit ⟨t, input.d⟩
  XorLane.circuit ⟨t, input.e⟩

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c ∧
    Normalized input.d ∧ Normalized input.e

def Spec (input : Inputs (F p)) (z : fields 64 (F p)) : Prop :=
  valueBits z =
    valueBits input.a ^^^ valueBits input.b ^^^ valueBits input.c ^^^
      valueBits input.d ^^^ valueBits input.e
  ∧ Normalized z

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 64) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [XorLane.circuit]
  simp only [XorLane.Assumptions, XorLane.Spec, and_imp] at h_holds
  obtain ⟨ha, hb, hc, hd, he⟩ := h_assumptions
  obtain ⟨c1, c2, c3, c4⟩ := h_holds
  obtain ⟨v1, n1⟩ := c1 ha hb
  obtain ⟨v2, n2⟩ := c2 n1 hc
  obtain ⟨v3, n3⟩ := c3 n2 hd
  obtain ⟨v4, n4⟩ := c4 n3 he
  refine ⟨?_, n4⟩
  rw [v4, v3, v2, v1]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [XorLane.circuit]
  simp only [XorLane.Assumptions, XorLane.Spec, and_imp] at h_env ⊢
  obtain ⟨ha, hb, hc, hd, he⟩ := h_assumptions
  obtain ⟨c1, c2, c3, _⟩ := h_env
  obtain ⟨_, n1⟩ := c1 ha hb
  obtain ⟨_, n2⟩ := c2 n1 hc
  obtain ⟨_, n3⟩ := c3 n2 hd
  exact ⟨⟨ha, hb⟩, ⟨n1, hc⟩, ⟨n2, hd⟩, n3, he⟩

def circuit : FormalCircuit (F p) Inputs (fields 64) where
  main; elaborated; Assumptions; Spec; soundness; completeness

attribute [local irreducible] main

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let firstInput : Var XorLane.Inputs (F p) := ⟨input.a, input.b⟩
  let first : Circuit (F p) (Var (fields 64) (F p)) := XorLane.circuit firstInput
  let n1 := offset + first.localLength offset
  let t1 := first.output offset
  let secondInput : Var XorLane.Inputs (F p) := ⟨t1, input.c⟩
  let second : Circuit (F p) (Var (fields 64) (F p)) := XorLane.circuit secondInput
  let n2 := n1 + second.localLength n1
  let t2 := second.output n1
  let thirdInput : Var XorLane.Inputs (F p) := ⟨t2, input.d⟩
  let third : Circuit (F p) (Var (fields 64) (F p)) := XorLane.circuit thirdInput
  let n3 := n2 + third.localLength n2
  let t3 := third.output n2
  have hlen1 : first.localLength offset = 64 := by
    simp [first, firstInput, XorLane.circuit, circuit_norm]
  have hlen2 : second.localLength n1 = 64 := by
    simp [second, secondInput, XorLane.circuit, circuit_norm]
  have hlen3 : third.localLength n2 = 64 := by
    simp [third, thirdInput, XorLane.circuit, circuit_norm]
  have hn1 : n1 = offset + 64 := by simp only [n1, hlen1]
  have hn2 : n2 = n1 + 64 := by simp only [n2, hlen2]
  have hn3 : n3 = n2 + 64 := by simp only [n3, hlen3]
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  and_intros
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      XorLane.circuit input ⟨input.a, input.b⟩ offset
      (by
        intro env env' h_input
        simp [circuit_norm] at h_input ⊢
        exact ⟨h_input.1, h_input.2.1⟩)
      XorLane.computableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      XorLane.circuit input ⟨t1, input.c⟩ n1
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm] at h_input ⊢
        refine ⟨?_, ?_⟩
        · exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
            h_agree (by omega)
        · exact h_input.2.2.1)
      XorLane.computableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      XorLane.circuit input ⟨t2, input.d⟩ n2
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm] at h_input ⊢
        refine ⟨?_, ?_⟩
        · exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
            h_agree (by omega)
        · exact h_input.2.2.2.1)
      XorLane.computableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      XorLane.circuit input ⟨t3, input.e⟩ n3
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm] at h_input ⊢
        refine ⟨?_, ?_⟩
        · exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
            h_agree (by omega)
        · exact h_input.2.2.2.2)
      XorLane.computableWitnesses env env'

end Xor5Lane
end Solution.KeccakF1600
end
