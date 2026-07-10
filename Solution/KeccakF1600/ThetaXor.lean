import Solution.KeccakF1600.XorLane

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace ThetaXor

structure Inputs (F : Type) where
  state : KeccakBitState F
  d : KeccakBitRow F
deriving ProvableStruct

def main : Var Inputs (F p) → Circuit (F p) (Var KeccakBitState (F p))
  | { state, d } => .mapFinRange 25 fun i =>
    XorLane.circuit ⟨state[i.val], d[i.val % 5]⟩

def Assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  StateNormalized state ∧ RowNormalized d

def Spec (inputs : Inputs (F p)) (out : KeccakBitState (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  StateNormalized out ∧ stateValue out = thetaXorSpec (stateValue state) (rowValue d)

instance elaborated : ElaboratedCircuit (F p) Inputs KeccakBitState main := by
  elaborate_circuit

lemma thetaXorSpec_loop (A : Vector ℕ 25) (D : Vector ℕ 5) :
    thetaXorSpec A D = .ofFn fun i => A[i.val] ^^^ D[i.val % 5] := rfl

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [XorLane.circuit, XorLane.Assumptions, XorLane.Spec]
  obtain ⟨state_norm, d_norm⟩ := h_assumptions
  obtain ⟨hs, hd⟩ := h_input
  apply stateNormalized_value_ext
  simp only [circuit_norm, thetaXorSpec_loop, eval_vector, stateValue, rowValue]
  intro i
  have hsi : Vector.map (Expression.eval env) input_var_state[i.val]
      = input_state[i.val] := by
    have h := getElem_eval_vector (α := fields 64) env input_var_state i.val i.isLt
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  have hdi : Vector.map (Expression.eval env) input_var_d[i.val % 5]
      = input_d[i.val % 5] := by
    have h := getElem_eval_vector (α := fields 64) env input_var_d (i.val % 5) (by omega)
    rw [CircuitType.eval_var_fields] at h; rw [hd] at h; exact h
  have harg : Normalized (Vector.map (Expression.eval env) input_var_state[i.val])
      ∧ Normalized (Vector.map (Expression.eval env) input_var_d[i.val % 5]) := by
    rw [hsi, hdi]; exact ⟨state_norm i, d_norm ⟨i.val % 5, by omega⟩⟩
  obtain ⟨h_val, h_norm⟩ := h_holds i harg
  refine ⟨h_norm, ?_⟩
  rw [Vector.getElem_ofFn, h_val, hsi, hdi]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [XorLane.circuit, XorLane.Assumptions, XorLane.Spec]
  obtain ⟨state_norm, d_norm⟩ := h_assumptions
  obtain ⟨hs, hd⟩ := h_input
  intro i
  have hsi : Vector.map (Expression.eval env.toEnvironment) input_var_state[i.val]
      = input_state[i.val] := by
    have h := getElem_eval_vector (α := fields 64) env.toEnvironment input_var_state i.val i.isLt
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  have hdi : Vector.map (Expression.eval env.toEnvironment) input_var_d[i.val % 5]
      = input_d[i.val % 5] := by
    have h := getElem_eval_vector (α := fields 64) env.toEnvironment input_var_d (i.val % 5) (by omega)
    rw [CircuitType.eval_var_fields] at h; rw [hd] at h; exact h
  exact ⟨by rw [hsi]; exact state_norm i,
    by rw [hdi]; exact d_norm ⟨i.val % 5, by omega⟩⟩

def circuit : FormalCircuit (F p) Inputs KeccakBitState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

attribute [local irreducible] main XorLane.circuit

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
  intro i
  refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    XorLane.circuit input ⟨input.state[i.val], input.d[i.val % 5]⟩ _ ?_ XorLane.computableWitnesses env env'
  intro e1 e2 h_input
  simp [circuit_norm] at h_input ⊢
  refine ⟨?_, ?_⟩
  · intro a ha
    have hword :
        Vector.map (Expression.eval e1.toEnvironment) input.state[i.val] =
          Vector.map (Expression.eval e2.toEnvironment) input.state[i.val] := by
      rw [← CircuitType.eval_var_fields e1.toEnvironment (input.state[i.val]),
        ← CircuitType.eval_var_fields e2.toEnvironment (input.state[i.val])]
      simpa [getElem_eval_vector] using
        congrArg (fun s : KeccakBitState (F p) => s[i.val]'i.isLt) h_input.1
    simp only [Vector.mem_iff_getElem] at ha
    rcases ha with ⟨b, hb, hget⟩
    rw [← hget]
    simpa [Vector.getElem_map] using Vector.ext_iff.mp hword b hb
  · intro a ha
    have hword :
        Vector.map (Expression.eval e1.toEnvironment) input.d[i.val % 5] =
          Vector.map (Expression.eval e2.toEnvironment) input.d[i.val % 5] := by
      rw [← CircuitType.eval_var_fields e1.toEnvironment (input.d[i.val % 5]),
        ← CircuitType.eval_var_fields e2.toEnvironment (input.d[i.val % 5])]
      simpa [getElem_eval_vector] using
        congrArg (fun s : KeccakBitRow (F p) => s[i.val % 5]'(by omega)) h_input.2
    simp only [Vector.mem_iff_getElem] at ha
    rcases ha with ⟨b, hb, hget⟩
    rw [← hget]
    simpa [Vector.getElem_map] using Vector.ext_iff.mp hword b hb

end ThetaXor
end Solution.KeccakF1600
end
