import Solution.KeccakF1600.Theta
import Solution.KeccakF1600.Chi
import Solution.KeccakF1600.KeccakRoundTheorems

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace KeccakRound

def main (rc : ℕ) (state : Var KeccakBitState (F p)) :
    Circuit (F p) (Var KeccakBitState (F p)) := do
  let state ← Theta.circuit state
  let state ← Chi.circuit (rhoPiWire state)
  return iotaWire rc state

def Assumptions (state : KeccakBitState (F p)) : Prop := StateNormalized state

def Spec (rc : ℕ) (state : KeccakBitState (F p)) (out : KeccakBitState (F p)) : Prop :=
  StateNormalized out ∧
  stateValue out = Specs.Keccak.keccakRound 64 rc (stateValue state)

instance elaborated (rc : ℕ) : ElaboratedCircuit (F p) KeccakBitState KeccakBitState (main rc) := by
  elaborate_circuit

theorem soundness (rc : ℕ) (hrc : rc < 2^64) :
    Soundness (F p) (main rc) Assumptions (Spec rc) := by
  circuit_proof_start [Theta.circuit, Theta.Assumptions, Theta.Spec,
    Chi.circuit, Chi.Assumptions, Chi.Spec]
  obtain ⟨h_theta, h_chi⟩ := h_holds
  obtain ⟨theta_norm, theta_val⟩ := h_theta h_assumptions
  -- rewrite the χ subcircuit's ρ/π-wired input to `rhoPiWire (eval env θ)`
  rw [eval_keccakState, eval_rhoPiWire_vec, ← eval_keccakState] at h_chi
  obtain ⟨chi_norm, chi_val⟩ := h_chi (StateNormalized_rhoPiWire _ theta_norm)
  rw [stateValue_rhoPiWire _ theta_norm, theta_val] at chi_val
  rw [eval_keccakState] at chi_norm chi_val
  -- the output is the per-lane ι map over the χ output
  rw [keccakRound_decompose rc, eval_keccakState, map_iotaWire]
  refine ⟨StateNormalized_iotaMap rc _ chi_norm, ?_⟩
  rw [stateValue_iotaMap rc hrc _ chi_norm, chi_val]

theorem completeness (rc : ℕ) : Completeness (F p) (main rc) Assumptions := by
  circuit_proof_start [Theta.circuit, Theta.Assumptions, Theta.Spec,
    Chi.circuit, Chi.Assumptions, Chi.Spec]
  obtain ⟨h_theta, h_chi⟩ := h_env
  obtain ⟨theta_norm, _⟩ := h_theta h_assumptions
  rw [eval_keccakState, eval_rhoPiWire_vec, ← eval_keccakState] at h_chi ⊢
  exact ⟨h_assumptions, StateNormalized_rhoPiWire _ theta_norm⟩

def circuit (rc : ℕ) (hrc : rc < 2^64) : FormalCircuit (F p) KeccakBitState KeccakBitState where
  main := main rc
  elaborated := elaborated rc
  Assumptions := Assumptions
  Spec := Spec rc
  soundness := soundness rc hrc
  completeness := completeness rc

end KeccakRound
end Solution.KeccakF1600
end
