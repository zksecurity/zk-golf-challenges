import Solution.KeccakF1600.ChiLane

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace Chi

def main (state : Var KeccakBitState (F p)) : Circuit (F p) (Var KeccakBitState (F p)) :=
  .mapFinRange 25 fun j =>
    ChiLane.circuit ⟨state[j.val], state[(chiSource1 j).val], state[(chiSource2 j).val]⟩

def Assumptions (state : KeccakBitState (F p)) : Prop := StateNormalized state

def Spec (state : KeccakBitState (F p)) (out : KeccakBitState (F p)) : Prop :=
  StateNormalized out ∧ stateValue out = chiSpec (stateValue state)

instance elaborated : ElaboratedCircuit (F p) KeccakBitState KeccakBitState main := by
  elaborate_circuit

lemma chiSpec_loop (A : Vector ℕ 25) :
    chiSpec A = .ofFn fun j =>
      A[j.val] ^^^
        (Specs.Keccak.notLane 64 A[(chiSource1 j).val] &&& A[(chiSource2 j).val]) := rfl

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ChiLane.circuit, ChiLane.Assumptions, ChiLane.Spec]
  have hs := h_input
  apply stateNormalized_value_ext
  simp only [chiSpec_loop, circuit_norm, eval_vector, stateValue]
  intro j
  have hb : ∀ k (hk : k < 25),
      Vector.map (Expression.eval env) input_var[k] = input[k] := by
    intro k hk
    have h := getElem_eval_vector (α := fields 64) env input_var k hk
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  have harg : Normalized (Vector.map (Expression.eval env) input_var[j.val])
      ∧ Normalized (Vector.map (Expression.eval env) input_var[(chiSource1 j).val])
      ∧ Normalized (Vector.map (Expression.eval env) input_var[(chiSource2 j).val]) := by
    rw [hb _ j.isLt, hb _ (chiSource1 j).isLt, hb _ (chiSource2 j).isLt]
    exact ⟨h_assumptions j, h_assumptions (chiSource1 j), h_assumptions (chiSource2 j)⟩
  obtain ⟨h_val, h_norm⟩ := h_holds j harg
  refine ⟨h_norm, ?_⟩
  rw [Vector.getElem_ofFn, h_val, hb _ j.isLt, hb _ (chiSource1 j).isLt, hb _ (chiSource2 j).isLt]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [ChiLane.circuit, ChiLane.Assumptions, ChiLane.Spec]
  have hs := h_input
  intro j
  have hb : ∀ k (hk : k < 25),
      Vector.map (Expression.eval env.toEnvironment) input_var[k] = input[k] := by
    intro k hk
    have h := getElem_eval_vector (α := fields 64) env.toEnvironment input_var k hk
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  rw [hb _ j.isLt, hb _ (chiSource1 j).isLt, hb _ (chiSource2 j).isLt]
  exact ⟨h_assumptions j, h_assumptions (chiSource1 j), h_assumptions (chiSource2 j)⟩

def circuit : FormalCircuit (F p) KeccakBitState KeccakBitState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.mapFinRange_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  intro j
  refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    ChiLane.circuit input
    ⟨input[j.val], input[(chiSource1 j).val], input[(chiSource2 j).val]⟩ _ ?_
    ChiLane.computableWitnesses env env'
  intro e1 e2 h_input
  simp [circuit_norm] at h_input ⊢
  have hword : ∀ (k : ℕ) (hk : k < 25),
      Vector.map (Expression.eval e1.toEnvironment) (input[k]'hk)
        = Vector.map (Expression.eval e2.toEnvironment) (input[k]'hk) := by
    intro k hk
    rw [← CircuitType.eval_var_fields e1.toEnvironment (input[k]'hk),
      ← CircuitType.eval_var_fields e2.toEnvironment (input[k]'hk),
      getElem_eval_vector e1.toEnvironment input k hk,
      getElem_eval_vector e2.toEnvironment input k hk]
    exact congrArg (fun v : KeccakBitState (F p) => v[k]'hk) h_input
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · simp only [Vector.mem_iff_getElem] at ha
    rcases ha with ⟨b, hb, hget⟩
    rw [← hget]
    simpa [Vector.getElem_map] using
      Vector.ext_iff.mp (hword j.val j.isLt) b hb
  · simp only [Vector.mem_iff_getElem] at ha
    rcases ha with ⟨b, hb, hget⟩
    rw [← hget]
    simpa [Vector.getElem_map] using
      Vector.ext_iff.mp (hword (chiSource1 j).val (chiSource1 j).isLt) b hb
  · simp only [Vector.mem_iff_getElem] at ha
    rcases ha with ⟨b, hb, hget⟩
    rw [← hget]
    simpa [Vector.getElem_map] using
      Vector.ext_iff.mp (hword (chiSource2 j).val (chiSource2 j).isLt) b hb

end Chi
end Solution.KeccakF1600
end
