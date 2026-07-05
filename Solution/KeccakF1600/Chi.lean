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

end Chi
end Solution.KeccakF1600
end
