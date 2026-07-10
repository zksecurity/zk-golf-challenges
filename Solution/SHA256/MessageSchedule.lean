import Solution.SHA256.ScheduleStep
import Solution.SHA256.MessageScheduleTheorems
import Challenge.Specs.SHA256
import Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^33)]

namespace Solution.SHA256

/-!
# SHA-256 Message Schedule

Expands a 16-word block into a 64-word message schedule.

For i in 16..63:
  w[i] = σ₁(w[i−2]) + w[i−7] + σ₀(w[i−15]) + w[i−16]  (mod 2^32)

`main` inlines a 48-step `Circuit.foldlRange` over the `ScheduleStep` gadget: each
step reads four schedule words, runs `ScheduleStep.circuit` (227 witnesses /
output word at relative offset 194) and `set`s the new word into the accumulator.
The accumulator descriptions (`varSchedule` / `valSchedule`) and the bridging
lemmas live in `MessageScheduleTheorems`.
-/

namespace MessageSchedule

/-- Explicit `ConstantLength` for the inlined fold body (227 witnesses per step).
    Naming it lets `Cost.lean` pass the same instance `main` folds with (the body is
    still inlined into `main`, so `circuit_proof_start` is unaffected). -/
def constantLength :
    Circuit.ConstantLength (fun (x : SHA256Schedule (Expression (F p)) × Fin 48) => do
      let wj ← ScheduleStep.circuit
        ⟨x.1.get ⟨x.2.val + 16 - 2, by omega⟩, x.1.get ⟨x.2.val + 16 - 7, by omega⟩,
         x.1.get ⟨x.2.val + 16 - 15, by omega⟩, x.1.get ⟨x.2.val + 16 - 16, by omega⟩⟩
      return x.1.set (x.2.val + 16) wj (by omega)) where
  localLength := 227
  localLength_eq _ _ := by
    simp [circuit_norm, ScheduleStep.circuit, ScheduleStep.elaborated]

def main (block : SHA256Block (Expression (F p))) : Circuit (F p) (SHA256Schedule (Expression (F p))) := do
  let zero32 : Var (fields 32) (F p) := Vector.replicate 32 (0 : Expression (F p))
  let init : SHA256Schedule (Expression (F p)) := block.append (Vector.replicate 48 zero32)
  Circuit.foldlRange 48 init (fun w i => do
    let wj ← ScheduleStep.circuit
      ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
       w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩
    return w.set (i.val + 16) wj (by omega)) constantLength

def Assumptions (block : SHA256Block (F p)) : Prop :=
  ∀ i : Fin 16, Normalized block[i]

def Spec (block : SHA256Block (F p)) (sched : SHA256Schedule (F p)) : Prop :=
  let block_val : Vector ℕ 16 := block.map valueBits
  let expected := Specs.SHA256.messageSchedule block_val
  ∀ i : Fin 64, valueBits sched[i] = expected[i] ∧ Normalized sched[i]

instance elaborated : ElaboratedCircuit (F p) SHA256Block SHA256Schedule main := by
  elaborate_circuit_with {
    output input i₀ := varSchedule i₀ input 48
  } using by
    simp only [circuit_norm]
    intros
    exact finFoldl_eq_varSchedule_48 _ _

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main]
  -- Inductive invariant: at every step `k`, the variable-level schedule matches the
  -- value-level schedule and is normalized.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 48),
      (∀ (j : ℕ) (hj : j < 64),
        valueBits (eval env ((varSchedule i₀ input_var k)[j]'hj)) =
          (valSchedule (input.map valueBits) k)[j]'hj) ∧
      (∀ (j : ℕ) (hj : j < 64),
        Normalized (eval env ((varSchedule i₀ input_var k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro j hj
        simp only [varSchedule, valSchedule]
        by_cases hj16 : j < 16
        · change valueBits (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j]) = _
          rw [Vector.getElem_append_left hj16]
          simp only [Vector.getElem_mapFinRange, hj16, dif_pos]
          rw [show (Vector.map valueBits input).get ⟨j, hj16⟩ =
                (Vector.map valueBits input)[j]'hj16 from rfl]
          rw [Vector.getElem_map]
          congr 1
          rw [getElem_eval_vector, h_input]
        · change valueBits (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j]) = _
          have hj' : j < 16 + 48 := by omega
          rw [show (input_var ++ Vector.replicate 48
                (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
              (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
              from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
          rw [Vector.getElem_replicate]
          simp only [Vector.getElem_mapFinRange, hj16, dif_neg, not_false_eq_true]
          have h_eval_repl :
              eval env (Vector.replicate 32 (0 : Expression (F p))) =
                Vector.replicate 32 (0 : F p) := by
            rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
          unfold valueBits
          rw [h_eval_repl]
          simp [Vector.getElem_replicate]
      · intro j hj
        simp only [varSchedule]
        by_cases hj16 : j < 16
        · change Normalized (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
          rw [Vector.getElem_append_left hj16]
          have h_ev : eval env (input_var[j]'hj16) = input[j]'hj16 := by
            rw [getElem_eval_vector, h_input]
          rw [h_ev]
          exact h_assumptions ⟨j, hj16⟩
        · change Normalized (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
          have hj' : j < 16 + 48 := by omega
          rw [show (input_var ++ Vector.replicate 48
                (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
              (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
              from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
          rw [Vector.getElem_replicate]
          have h_eval_repl :
              eval env (Vector.replicate 32 (0 : Expression (F p))) =
                Vector.replicate 32 (0 : F p) := by
            rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
          rw [h_eval_repl]
          intro i; left; simp [Vector.getElem_replicate]
    | succ k ih =>
      have hk' : k ≤ 48 := by omega
      have hk'' : k < 48 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      have h_step := h_holds ⟨k, hk''⟩
      rw [foldlAcc_eq_varSchedule i₀ input_var k hk''] at h_step
      simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
        ScheduleStep.Spec, circuit_norm] at h_step
      have h_norm_m2 := ih_norm (k + 16 - 2) (by omega)
      have h_norm_m7 := ih_norm (k + 16 - 7) (by omega)
      have h_norm_m15 := ih_norm (k + 16 - 15) (by omega)
      have h_norm_m16 := ih_norm (k + 16 - 16) (by omega)
      rw [CircuitType.eval_var_fields] at h_norm_m2 h_norm_m7 h_norm_m15 h_norm_m16
      obtain ⟨v_wj, n_wj⟩ := h_step ⟨h_norm_m2, h_norm_m7, h_norm_m15, h_norm_m16⟩
      have ih_val' : ∀ (j : ℕ) (hj : j < 64),
          valueBits (Vector.map (Expression.eval env)
            (Vector.get (varSchedule i₀ input_var k) ⟨j, hj⟩)) =
            (valSchedule (input.map valueBits) k)[j]'hj := by
        intro j hj
        rw [show Vector.get (varSchedule i₀ input_var k) ⟨j, hj⟩ =
              (varSchedule i₀ input_var k)[j]'hj from rfl, ← CircuitType.eval_var_fields]
        exact ih_val j hj
      refine ⟨?_, ?_⟩
      · intro j hj
        simp only [varSchedule, valSchedule, dif_pos hk'']
        by_cases hjk : j = k + 16
        · subst hjk
          rw [Vector.getElem_set_self, Vector.getElem_set_self]
          rw [show (varFromOffset (fields 32) (i₀ + k * 227 + 194) : Vector (Expression (F p)) 32) =
                Vector.mapRange 32 (fun i => (var { index := i₀ + k * 227 + 194 + i } : Expression (F p)))
              from by simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
          rw [CircuitType.eval_var_fields, v_wj,
            ih_val' (k + 16 - 2) (by omega), ih_val' (k + 16 - 7) (by omega),
            ih_val' (k + 16 - 15) (by omega), ih_val' (k + 16 - 16) (by omega)]
        · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          exact ih_val j hj
      · intro j hj
        simp only [varSchedule, dif_pos hk'']
        by_cases hjk : j = k + 16
        · subst hjk
          rw [Vector.getElem_set_self]
          rw [show (i₀ + k * 227 + 194 : ℕ) = i₀ + k * 227 + 64 + 64 + 33 + 33 from by ring]
          rw [show (varFromOffset (fields 32) (i₀ + k * 227 + 64 + 64 + 33 + 33) :
                Vector (Expression (F p)) 32) =
                Vector.mapRange 32 (fun i =>
                  (var { index := i₀ + k * 227 + 64 + 64 + 33 + 33 + i } : Expression (F p)))
              from by simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
          rw [CircuitType.eval_var_fields]
          exact n_wj
        · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          exact ih_norm j hj
  obtain ⟨h_val_48, h_norm_48⟩ := h_inv 48 (le_refl 48)
  refine ⟨?_, ?_⟩
  · intro i
    have h_bridge :
        (eval env (varSchedule i₀ input_var 48))[i.val] =
          eval env ((varSchedule i₀ input_var 48)[i.val]'i.isLt) :=
      (getElem_eval_vector (α := fields 32) (n := 64) env (varSchedule i₀ input_var 48) i.val i.isLt).symm
    refine ⟨?_, ?_⟩
    · rw [h_bridge, messageSchedule_eq_valSchedule]
      exact h_val_48 i.val i.isLt
    · rw [h_bridge]
      exact h_norm_48 i.val i.isLt
  · intro i
    simp [ScheduleStep.circuit, circuit_norm]

theorem completeness : Completeness (F p) (Input := SHA256Block) (Output := SHA256Schedule) main Assumptions := by
  circuit_proof_start [main]
  -- Inductive invariant: at every step k, every slot of `varSchedule i₀ input_var k`
  -- is Normalized.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 48),
      ∀ (j : ℕ) (hj : j < 64),
        Normalized (eval env.toEnvironment ((varSchedule i₀ input_var k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [varSchedule]
      by_cases hj16 : j < 16
      · change Normalized (eval env.toEnvironment (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        rw [Vector.getElem_append_left hj16]
        have h_ev : eval env.toEnvironment (input_var[j]'hj16) = input[j]'hj16 := by
          rw [getElem_eval_vector, h_input]
        rw [h_ev]
        exact h_assumptions ⟨j, hj16⟩
      · change Normalized (eval env.toEnvironment (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        have hj' : j < 16 + 48 := by omega
        rw [show (input_var ++ Vector.replicate 48
              (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
            (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
            from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
        rw [Vector.getElem_replicate]
        have h_eval_repl :
            eval env.toEnvironment (Vector.replicate 32 (0 : Expression (F p))) =
              Vector.replicate 32 (0 : F p) := by
          rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
        rw [h_eval_repl]
        intro i; left; simp [Vector.getElem_replicate]
    | succ k ih =>
      have hk' : k ≤ 48 := by omega
      have hk'' : k < 48 := by omega
      specialize ih hk'
      have h_step := h_env ⟨k, hk''⟩
      rw [foldlAcc_eq_varSchedule i₀ input_var k hk''] at h_step
      simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
        ScheduleStep.Spec, circuit_norm] at h_step
      have h_norm_m2 := ih (k + 16 - 2) (by omega)
      have h_norm_m7 := ih (k + 16 - 7) (by omega)
      have h_norm_m15 := ih (k + 16 - 15) (by omega)
      have h_norm_m16 := ih (k + 16 - 16) (by omega)
      rw [CircuitType.eval_var_fields] at h_norm_m2 h_norm_m7 h_norm_m15 h_norm_m16
      obtain ⟨_, n_wj⟩ := h_step ⟨h_norm_m2, h_norm_m7, h_norm_m15, h_norm_m16⟩
      intro j hj
      simp only [varSchedule, dif_pos hk'']
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self, CircuitType.eval_var_fields]
        exact n_wj
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        exact ih j hj
  -- Discharge the per-step assumptions chain.
  intro i
  have hk : i.val < 48 := i.isLt
  have ih := h_inv i.val (le_of_lt hk)
  rw [foldlAcc_eq_varSchedule i₀ input_var i.val hk]
  simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
    circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ih (i.val + 16 - 2) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 7) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 15) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 16) (by omega); rw [CircuitType.eval_var_fields] at h; exact h

def circuit : FormalCircuit (F p) SHA256Block SHA256Schedule where
  main; elaborated; Assumptions; Spec; soundness;
  completeness := by simp only [completeness]

attribute [local irreducible] main

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.foldlRange_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  intro i
  rw [foldlAcc_eq_varSchedule_main offset input i.val i.isLt]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    ScheduleStep.circuit input
    ⟨(varSchedule offset input i.val).get ⟨i.val + 16 - 2, by omega⟩,
      (varSchedule offset input i.val).get ⟨i.val + 16 - 7, by omega⟩,
      (varSchedule offset input i.val).get ⟨i.val + 16 - 15, by omega⟩,
      (varSchedule offset input i.val).get ⟨i.val + 16 - 16, by omega⟩⟩
    (offset + i.val * (ScheduleStep.circuit (p := p)).localLength
      ⟨(varSchedule offset input i.val).get ⟨i.val + 16 - 2, by omega⟩,
        (varSchedule offset input i.val).get ⟨i.val + 16 - 7, by omega⟩,
        (varSchedule offset input i.val).get ⟨i.val + 16 - 15, by omega⟩,
        (varSchedule offset input i.val).get ⟨i.val + 16 - 16, by omega⟩⟩)
    (by
      intro k env env' hle h_agree h_input
      have hstep : env.AgreesBelow (offset + i.val * 227) env' :=
        ProverEnvironment.agreesBelow_of_le h_agree (by
          simp [ScheduleStep.circuit, circuit_norm] at hle
          simpa [ScheduleStep.circuit, circuit_norm] using hle)
      simp [circuit_norm]
      constructor
      · exact eval_mem_varSchedule_of_agreesBelow (offset := offset) (k := i.val)
          (by omega) hstep h_input (i.val + 16 - 2) (by omega) (by omega)
      · constructor
        · exact eval_mem_varSchedule_of_agreesBelow (offset := offset) (k := i.val)
            (by omega) hstep h_input (i.val + 16 - 7) (by omega) (by omega)
        · constructor
          · exact eval_mem_varSchedule_of_agreesBelow (offset := offset) (k := i.val)
              (by omega) hstep h_input (i.val + 16 - 15) (by omega) (by omega)
          · exact eval_mem_varSchedule_of_agreesBelow (offset := offset) (k := i.val)
              (by omega) hstep h_input (i.val + 16 - 16) (by omega) (by omega))
    ScheduleStep.computableWitnesses env env'

end MessageSchedule
end Solution.SHA256
end
