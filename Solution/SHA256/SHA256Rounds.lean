import Solution.SHA256.SHA256Round
import Solution.SHA256.SHA256RoundsTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^33)]

instance fact_p_gt_2_of_2_pow_33 : Fact (p > 2) := .mk (by
  have h : (2 : ℕ) < 2^33 := by decide
  exact h.trans (Fact.out (p := p > 2^33)))

namespace Solution.SHA256

/-!
# SHA-256 Compression: 64-round loop

Applies 64 rounds of the SHA-256 compression function.

This file builds the `FormalCircuit`:
  * `SHA256Rounds.circuit`     — the 64-round inner loop
-/

/-!
## FormalCircuit for 64-round compression loop
-/

namespace SHA256Rounds

structure Inputs (F : Type) where
  state : SHA256State F
  schedule : SHA256Schedule F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  Circuit.foldlRange 64 input.state (fun s i =>
    SHA256Round.circuit ⟨s, constWord32 Specs.SHA256.K[i].toNat, input.schedule[i]⟩)

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 64, Normalized input.schedule[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Compress (input.state.map valueBits) (input.schedule.map valueBits)
  ∧ ∀ i : Fin 8, Normalized out[i]

/-! ## Helper definitions and lemmas

The `stateVar` / `valStateAfterRound` descriptions and their `foldl`/spec
bridging lemmas live in `SHA256RoundsTheorems`. -/

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit_with {
    output input i₀ := stateVar i₀ input.state 64
  } using by
    simp only [circuit_norm]
    intros
    apply fin_foldl_eq_stateVar

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  rw [sha256Compress_eq_valStateAfterRound]
  -- Inductive invariant. We phrase normalization as `eval env ((stateVar k)[i])`
  -- (indexing INSIDE eval) which has type `fields 32 (F p) = Vector (F p) 32`
  -- and works smoothly with `Normalized` since the type alias issue is sidestepped.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 64),
      Vector.map valueBits (eval env (stateVar i₀ input_var_state k)) =
        valStateAfterRound (Vector.map valueBits input_state)
          (Vector.map valueBits input_schedule) k ∧
      (∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env ((stateVar i₀ input_var_state k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [stateVar, valStateAfterRound]; rw [h_input_state]
      · intro j hj
        simp only [stateVar]
        rw [getElem_eval_vector, h_input_state]
        exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 64 := by omega
      have hk'' : k < 64 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      specialize h_holds ⟨k, hk''⟩
      rw [foldlAcc_eq_stateVar i₀ input_var_state input_var_schedule k hk''] at h_holds
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_holds
      have h2 : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) Specs.SHA256.K[k].toNat)) := normalized_constWord32 env _
      have h3 : Normalized (Vector.map (Expression.eval env) input_var_schedule[k]) := by
        rw [show Vector.map (Expression.eval env) input_var_schedule[k]
              = eval env (input_var_schedule[k]'hk'') from (CircuitType.eval_var_fields env _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨k, hk''⟩
      -- Provide the IH-derived normalization assumption via a tactic that bridges
      -- via `getElem_eval_vector`.
      have h_spec := h_holds ⟨by
        intro i
        have h := ih_norm i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨h_value, h_norm⟩ := h_spec
      rw [stateVar, valStateAfterRound, dif_pos hk'']
      refine ⟨?_, ?_⟩
      · -- Value equality: h_value gives the LHS = sha256Round (...)
        rw [h_value, ih_val,
          valueBits_constWord32_of_lt env Specs.SHA256.K[k].toNat_lt,
          show Vector.map (Expression.eval env) input_var_schedule[k]
            = eval env (input_var_schedule[k]'hk'') from (CircuitType.eval_var_fields env _).symm,
          getElem_eval_vector, h_input_schedule,
          show (Vector.map valueBits input_schedule)[k]'hk''
            = valueBits (input_schedule[k]'hk'') from Vector.getElem_map _ _]
      · -- Normalization for round k+1.
        intro j hj
        -- h_norm gives Normalized (eval env <new state>)[↑i_1] for i_1 : Fin 8.
        -- We need Normalized (eval env <new state>[j]'hj).
        rw [getElem_eval_vector]
        exact h_norm ⟨j, hj⟩
  obtain ⟨h_val_64, h_norm_64⟩ := h_inv 64 (le_refl 64)
  refine ⟨⟨h_val_64, ?_⟩, ?_⟩
  · intro i
    rw [← getElem_eval_vector]
    exact h_norm_64 i.val i.isLt
  · intro _
    left; rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  -- Inductive invariant: at every round k, the state going in is normalized.
  -- This requires us to know the output of each round k is normalized — which
  -- follows from h_env when we provide the antecedents.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 64),
      ∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env.toEnvironment ((stateVar i₀ input_var_state k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [stateVar]
      rw [getElem_eval_vector, h_input_state]
      exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 64 := by omega
      have hk'' : k < 64 := by omega
      specialize h_env ⟨k, hk''⟩
      rw [foldlAcc_eq_stateVar i₀ input_var_state input_var_schedule k hk''] at h_env
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_env
      have h2 : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) Specs.SHA256.K[k].toNat)) := normalized_constWord32 _ _
      have h3 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_schedule[k]) := by
        rw [show Vector.map (Expression.eval env.toEnvironment) input_var_schedule[k]
              = eval env.toEnvironment (input_var_schedule[k]'hk'') from
            (CircuitType.eval_var_fields _ _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨k, hk''⟩
      have h_spec := h_env ⟨by
        intro i
        have h := ih hk' i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨_, h_norm⟩ := h_spec
      intro j hj
      rw [stateVar]
      rw [getElem_eval_vector]
      exact h_norm ⟨j, hj⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h := h_inv i.val (le_of_lt i.isLt) j.val j.isLt
    rw [← foldlAcc_eq_stateVar i₀ input_var_state input_var_schedule i.val i.isLt] at h
    rw [getElem_eval_vector] at h
    have heq : (⟨i.val, i.isLt⟩ : Fin 64) = i := Fin.ext rfl
    rw [heq] at h
    exact h
  · exact normalized_constWord32 _ _
  · rw [show Vector.map (Expression.eval env.toEnvironment) input_var_schedule[i.val]
          = eval env.toEnvironment (input_var_schedule[i.val]'i.isLt) from
        (CircuitType.eval_var_fields _ _).symm]
    rw [getElem_eval_vector, h_input_schedule]
    exact h_sched_norm i

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

attribute [local irreducible] main

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hschedule_eq : ∀ {env env' : ProverEnvironment (F p)} (i : Fin 64),
      eval env input = eval env' input →
      ∀ a ∈ input.schedule[i], Expression.eval env.toEnvironment a =
        Expression.eval env'.toEnvironment a := by
    intro env env' i h_input a ha
    simp [circuit_norm] at h_input
    have hword : Vector.map (Expression.eval env.toEnvironment) input.schedule[i] =
        Vector.map (Expression.eval env'.toEnvironment) input.schedule[i] := by
      rw [← CircuitType.eval_var_fields env.toEnvironment (input.schedule[i]),
        ← CircuitType.eval_var_fields env'.toEnvironment (input.schedule[i])]
      have h := congrArg (fun s : SHA256Schedule (F p) => s[i.val]'i.isLt) h_input.2
      simpa [getElem_eval_vector] using h
    simp only [Vector.mem_iff_getElem] at ha
    rcases ha with ⟨j, hj, hget⟩
    rw [← hget]
    simpa [Vector.getElem_map] using Vector.ext_iff.mp hword j hj
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.foldlRange_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  intro i
  have hacc :
      Circuit.FoldlM.foldlAcc offset (Vector.finRange 64)
        (fun s i =>
          subcircuit SHA256Round.circuit
            { state := s, k := constWord32 (Specs.SHA256.K[i].toNat),
              w := input.schedule[i] })
        input.state i =
          stateVar offset input.state i.val := by
    simpa only using foldlAcc_eq_stateVar_main offset input.state input.schedule i
  rw [hacc]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    SHA256Round.circuit input
    ⟨stateVar offset input.state i.val,
      constWord32 (p := p) (Specs.SHA256.K[i].toNat),
      input.schedule[i]⟩
    (offset + i.val * (SHA256Round.circuit (p := p)).localLength
      ⟨stateVar offset input.state i.val,
        constWord32 (p := p) (Specs.SHA256.K[i].toNat),
        input.schedule[i]⟩)
    (by
      intro k env env' hle h_agree h_input
      have hround : env.AgreesBelow (offset + i.val * 455) env' :=
        ProverEnvironment.agreesBelow_of_le h_agree (by
          simp [SHA256Round.circuit, circuit_norm] at hle
          simpa [SHA256Round.circuit, circuit_norm] using hle)
      simp [circuit_norm] at h_input ⊢
      refine ⟨?_, ?_, ?_⟩
      · apply Vector.ext
        intro j hj
        rw [← getElem_eval_vector env.toEnvironment (stateVar offset input.state i.val) j hj,
          ← getElem_eval_vector env'.toEnvironment (stateVar offset input.state i.val) j hj]
        apply Vector.ext
        intro b hb
        rw [← ProvableType.getElem_eval_fields env.toEnvironment
            ((stateVar offset input.state i.val)[j]'hj) b hb,
          ← ProvableType.getElem_eval_fields env'.toEnvironment
            ((stateVar offset input.state i.val)[j]'hj) b hb]
        exact eval_mem_stateVar_of_agreesBelow (offset := offset) (k := i.val)
          (by omega) hround h_input.1 j hj
          (((stateVar offset input.state i.val)[j]'hj)[b]'hb)
          (Vector.getElem_mem _)
      · intro a ha
        simp only [Vector.mem_iff_getElem] at ha
        rcases ha with ⟨j, hj, hget⟩
        rw [← hget]
        simp [constWord32, Expression.eval]
      · exact hschedule_eq i (by
          simp [circuit_norm]
          exact ⟨h_input.1, h_input.2⟩))
    SHA256Round.computableWitnesses env env'

end SHA256Rounds
end Solution.SHA256
end
