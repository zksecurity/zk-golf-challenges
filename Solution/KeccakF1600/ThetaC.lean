import Solution.KeccakF1600.Xor5Lane

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace ThetaC

def main (state : Var KeccakBitState (F p)) : Circuit (F p) (Var KeccakBitRow (F p)) :=
  .mapFinRange 5 fun x =>
    Xor5Lane.circuit
      ⟨state[x.val], state[x.val + 5], state[x.val + 10], state[x.val + 15], state[x.val + 20]⟩

def Assumptions (state : KeccakBitState (F p)) : Prop := StateNormalized state

def Spec (state : KeccakBitState (F p)) (out : KeccakBitRow (F p)) : Prop :=
  RowNormalized out ∧ rowValue out = thetaCSpec (stateValue state)

instance elaborated : ElaboratedCircuit (F p) KeccakBitState KeccakBitRow main := by
  elaborate_circuit

-- rewrite `thetaCSpec` as the loop the circuit computes
lemma thetaCSpec_loop (A : Vector ℕ 25) :
    thetaCSpec A = .ofFn fun x =>
      A[x.val] ^^^ A[x.val + 5] ^^^ A[x.val + 10] ^^^ A[x.val + 15] ^^^ A[x.val + 20] := rfl

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [Xor5Lane.circuit, Xor5Lane.Assumptions, Xor5Lane.Spec]
  have hs := h_input
  apply rowNormalized_value_ext
  simp only [thetaCSpec_loop, circuit_norm, eval_vector, stateValue]
  intro x
  have hb : ∀ j (hj : j < 25),
      Vector.map (Expression.eval env) input_var[j] = input[j] := by
    intro j hj
    have h := getElem_eval_vector (α := fields 64) env input_var j hj
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  have harg : Normalized (Vector.map (Expression.eval env) input_var[x.val])
      ∧ Normalized (Vector.map (Expression.eval env) input_var[x.val + 5])
      ∧ Normalized (Vector.map (Expression.eval env) input_var[x.val + 10])
      ∧ Normalized (Vector.map (Expression.eval env) input_var[x.val + 15])
      ∧ Normalized (Vector.map (Expression.eval env) input_var[x.val + 20]) := by
    rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]
    exact ⟨h_assumptions ⟨x.val, by omega⟩, h_assumptions ⟨x.val + 5, by omega⟩,
      h_assumptions ⟨x.val + 10, by omega⟩, h_assumptions ⟨x.val + 15, by omega⟩,
      h_assumptions ⟨x.val + 20, by omega⟩⟩
  obtain ⟨h_val, h_norm⟩ := h_holds x harg
  refine ⟨h_norm, ?_⟩
  rw [Vector.getElem_ofFn, h_val, hb _ (by omega), hb _ (by omega), hb _ (by omega),
    hb _ (by omega), hb _ (by omega)]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [Xor5Lane.circuit, Xor5Lane.Assumptions, Xor5Lane.Spec]
  have hs := h_input
  intro x
  have hb : ∀ j (hj : j < 25),
      Vector.map (Expression.eval env.toEnvironment) input_var[j] = input[j] := by
    intro j hj
    have h := getElem_eval_vector (α := fields 64) env.toEnvironment input_var j hj
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]
  exact ⟨h_assumptions ⟨x.val, by omega⟩, h_assumptions ⟨x.val + 5, by omega⟩,
    h_assumptions ⟨x.val + 10, by omega⟩, h_assumptions ⟨x.val + 15, by omega⟩,
    h_assumptions ⟨x.val + 20, by omega⟩⟩

def circuit : FormalCircuit (F p) KeccakBitState KeccakBitRow where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

attribute [local irreducible] main

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
  intro x
  refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    Xor5Lane.circuit input
    ⟨input[x.val], input[x.val + 5], input[x.val + 10], input[x.val + 15], input[x.val + 20]⟩
    _ ?_ Xor5Lane.computableWitnesses env env'
  intro e1 e2 h_input
  simp [circuit_norm] at h_input ⊢
  have hword : ∀ (j : ℕ) (hj : j < 25),
      Vector.map (Expression.eval e1.toEnvironment) (input[j]'hj)
        = Vector.map (Expression.eval e2.toEnvironment) (input[j]'hj) := by
    intro j hj
    rw [← CircuitType.eval_var_fields e1.toEnvironment (input[j]'hj),
      ← CircuitType.eval_var_fields e2.toEnvironment (input[j]'hj),
      getElem_eval_vector e1.toEnvironment input j hj,
      getElem_eval_vector e2.toEnvironment input j hj]
    exact congrArg (fun v : KeccakBitState (F p) => v[j]'hj) h_input
  have hmem : ∀ (j : ℕ) (hj : j < 25),
      ∀ a ∈ (input[j]'hj), Expression.eval e1.toEnvironment a = Expression.eval e2.toEnvironment a := by
    intro j hj a ha
    simp only [Vector.mem_iff_getElem] at ha
    rcases ha with ⟨b, hb, hget⟩
    rw [← hget]
    simpa [Vector.getElem_map] using Vector.ext_iff.mp (hword j hj) b hb
  exact ⟨hmem _ (by omega), hmem _ (by omega), hmem _ (by omega),
    hmem _ (by omega), hmem _ (by omega)⟩

end ThetaC
end Solution.KeccakF1600
end
