import Solution.KeccakF1600.ThetaC
import Solution.KeccakF1600.ThetaD
import Solution.KeccakF1600.ThetaXor

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace Theta

def main (state : Var KeccakBitState (F p)) : Circuit (F p) (Var KeccakBitState (F p)) := do
  let c ← ThetaC.circuit state
  let d ← ThetaD.circuit c
  ThetaXor.circuit ⟨state, d⟩

def Assumptions (state : KeccakBitState (F p)) : Prop := StateNormalized state

def Spec (state : KeccakBitState (F p)) (out : KeccakBitState (F p)) : Prop :=
  StateNormalized out ∧
  stateValue out =
    thetaXorSpec (stateValue state) (thetaDSpec (thetaCSpec (stateValue state)))

instance elaborated : ElaboratedCircuit (F p) KeccakBitState KeccakBitState main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ThetaC.circuit, ThetaC.Assumptions, ThetaC.Spec,
    ThetaD.circuit, ThetaD.Assumptions, ThetaD.Spec,
    ThetaXor.circuit, ThetaXor.Assumptions, ThetaXor.Spec]
  obtain ⟨h_c, h_d, h_x⟩ := h_holds
  obtain ⟨c_norm, c_val⟩ := h_c h_assumptions
  obtain ⟨d_norm, d_val⟩ := h_d c_norm
  obtain ⟨out_norm, out_val⟩ := h_x ⟨h_assumptions, d_norm⟩
  refine ⟨out_norm, ?_⟩
  rw [out_val, d_val, c_val]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [ThetaC.circuit, ThetaC.Assumptions, ThetaC.Spec,
    ThetaD.circuit, ThetaD.Assumptions, ThetaD.Spec,
    ThetaXor.circuit, ThetaXor.Assumptions, ThetaXor.Spec]
  obtain ⟨h_c, h_d, _⟩ := h_env
  obtain ⟨c_norm, _⟩ := h_c h_assumptions
  obtain ⟨d_norm, _⟩ := h_d c_norm
  exact ⟨h_assumptions, c_norm, h_assumptions, d_norm⟩

def circuit : FormalCircuit (F p) KeccakBitState KeccakBitState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end Theta
end Solution.KeccakF1600
end
