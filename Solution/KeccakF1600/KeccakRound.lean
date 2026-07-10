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

/-- A full `KeccakBitState` value assembled from per-lane `varFromOffset (fields 64)`
blocks evaluates identically under two environments that agree below `k`, as long as
each lane block lies below `k`. The 25-lane analogue of `Theta.eval_row_of_agreesBelow`,
used for the (θ-produced) χ subcircuit input. -/
lemma eval_state_of_agreesBelow {k : ℕ}
    {env env' : ProverEnvironment (F p)} (base : Fin 25 → ℕ)
    (hbound : ∀ i : Fin 25, base i + 64 ≤ k)
    (h : env.AgreesBelow k env') (v : Var KeccakBitState (F p))
    (hv : v = Vector.mapFinRange 25 fun i =>
      (varFromOffset (fields 64) (base i) : Var (fields 64) (F p))) :
    eval env v = eval env' v := by
  simp only [CircuitType.eval_var_prover_to_verifier]
  rw [hv]
  apply Vector.ext
  intro i hi
  rw [← getElem_eval_vector env.toEnvironment
        (Vector.mapFinRange 25 fun i => (varFromOffset (fields 64) (base i) : Var (fields 64) (F p))) i hi,
      ← getElem_eval_vector env'.toEnvironment
        (Vector.mapFinRange 25 fun i => (varFromOffset (fields 64) (base i) : Var (fields 64) (F p))) i hi,
      Vector.getElem_mapFinRange]
  apply Vector.ext
  intro j hj
  rw [← ProvableType.getElem_eval_fields env.toEnvironment
        (varFromOffset (fields 64) (base ⟨i, hi⟩)) j hj,
      ← ProvableType.getElem_eval_fields env'.toEnvironment
        (varFromOffset (fields 64) (base ⟨i, hi⟩)) j hj,
      ProvableType.varFromOffset_fields, Vector.getElem_mapRange]
  simp only [Expression.eval]
  exact h (base ⟨i, hi⟩ + j) (by have := hbound ⟨i, hi⟩; omega)

attribute [local irreducible] main

theorem computableWitnesses (rc : ℕ) (hrc : rc < 2 ^ 64) :
    (circuit (p := p) rc hrc).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main rc input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let first : Circuit (F p) (Var KeccakBitState (F p)) := Theta.circuit input
  let θ := first.output offset
  let n1 := offset + first.localLength offset
  have hlen : first.localLength offset = 3200 := by
    simp [first, Theta.circuit, circuit_norm]
  have hn1 : n1 = offset + 3200 := by simp only [n1, hlen]
  have hθ : θ = (Vector.mapFinRange 25 fun i =>
      (varFromOffset (fields 64) (offset + 1600 + i.val * 64) : Var (fields 64) (F p))) := by
    simp [θ, first, Theta.circuit, circuit_norm]
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff, and_true]
  and_intros
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Theta.circuit input input offset
      (fun _ _ h => h)
      Theta.computableWitnesses env env'
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Chi.circuit input (rhoPiWire θ) n1 ?_ Chi.computableWitnesses env env'
    intro k e e' hle h_agree _h_input
    have hθeval : eval e θ = eval e' θ :=
      eval_state_of_agreesBelow
        (fun i => offset + 1600 + i.val * 64)
        (fun i => by
          show offset + 1600 + i.val * 64 + 64 ≤ k
          have := i.isLt; rw [hn1] at hle; omega)
        h_agree θ hθ
    simp only [CircuitType.eval_var_prover_to_verifier] at hθeval
    rw [CircuitType.eval_var_prover_to_verifier (M := KeccakBitState) (env := e) (v := rhoPiWire θ),
      CircuitType.eval_var_prover_to_verifier (M := KeccakBitState) (env := e') (v := rhoPiWire θ),
      eval_keccakState e.toEnvironment (rhoPiWire θ),
      eval_keccakState e'.toEnvironment (rhoPiWire θ),
      eval_rhoPiWire_vec, eval_rhoPiWire_vec,
      ← eval_keccakState e.toEnvironment θ, ← eval_keccakState e'.toEnvironment θ, hθeval]

end KeccakRound
end Solution.KeccakF1600
end
