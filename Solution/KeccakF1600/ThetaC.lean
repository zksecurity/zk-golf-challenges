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

end ThetaC
end Solution.KeccakF1600
end
