import Solution.KeccakF1600.PermutationDefs

namespace Solution.KeccakF1600.Permutation

open Challenge.Instances.KeccakF1600.Interface

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [KeccakRound.circuit, KeccakRound.Assumptions, KeccakRound.Spec]
  simp only [body, KeccakRound.circuit, circuit_norm, KeccakRound.Assumptions,
    KeccakRound.Spec] at h_holds ⊢
  -- chain the per-round spec through the fold accumulator
  have key : ∀ (k : ℕ) (hk : k < 24),
      StateNormalized (eval env (acc i₀ input_var ⟨k, hk⟩)) ∧
      stateValue (eval env (acc i₀ input_var ⟨k, hk⟩)) = vfold (stateValue input) k := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [acc_zero, h_input]
      exact ⟨h_assumptions, by simp only [vfold, Fin.foldl_zero]⟩
    | succ k ih =>
      intro hk
      have hk1 : k < 24 := by omega
      obtain ⟨nk, vk⟩ := ih hk1
      have hh := h_holds ⟨k, hk1⟩ nk
      rw [acc_succ input_var i₀ k hk, stateVar,
        show rcN k = rc ⟨k, hk1⟩ from rcN_eq ⟨k, hk1⟩] at *
      refine ⟨hh.1, ?_⟩
      rw [hh.2, vk, vfold_succ, show rcN k = rc ⟨k, hk1⟩ from rcN_eq ⟨k, hk1⟩]
  -- the output is round-23's output
  obtain ⟨n23, v23⟩ := key 23 (by norm_num)
  have hh := h_holds ⟨23, by norm_num⟩ n23
  have h24 : vfold (stateValue input) 24 =
      Specs.Keccak.keccakRound 64 (rcN 23) (vfold (stateValue input) 23) :=
    vfold_succ (stateValue input) 23
  refine ⟨hh.1, Eq.trans hh.2 ?_⟩
  rw [v23, ← vfold_24 (stateValue input), h24]
  congr 1

end Solution.KeccakF1600.Permutation
