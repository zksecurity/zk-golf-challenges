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

end ThetaXor
end Solution.KeccakF1600
end
