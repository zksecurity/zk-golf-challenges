import Solution.KeccakF1600.PermutationDefs

namespace Solution.KeccakF1600.Permutation

open Challenge.Instances.KeccakF1600.Interface

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [KeccakRound.circuit, KeccakRound.Assumptions, KeccakRound.Spec]
  simp only [body, KeccakRound.circuit, circuit_norm, KeccakRound.Assumptions,
    KeccakRound.Spec] at h_env ⊢
  -- each round's input state is normalized
  have key : ∀ (k : ℕ) (hk : k < 24),
      StateNormalized (eval env.toEnvironment (acc i₀ input_var ⟨k, hk⟩)) := by
    intro k
    induction k with
    | zero => intro hk; rw [acc_zero, h_input]; exact h_assumptions
    | succ k ih =>
      intro hk
      have hk1 : k < 24 := by omega
      rw [acc_succ input_var i₀ k hk, stateVar,
        show rcN k = rc ⟨k, hk1⟩ from rcN_eq ⟨k, hk1⟩]
      exact (h_env ⟨k, hk1⟩ (ih hk1)).1
  intro i
  exact key i.val i.isLt

end Solution.KeccakF1600.Permutation
