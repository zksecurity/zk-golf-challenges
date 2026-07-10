import Solution.SHA256.SHA256Rounds
import Solution.SHA256.MessageSchedule
import Solution.SHA256.Add32
import Challenge.Specs.SHA256
import Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^33)]

namespace Solution.SHA256

/-!
# SHA-256 Full Block Compression

Composes the message schedule, the 64 compression rounds, and the final add of
the original state to produce the block output (the Davies–Meyer construction).

This file builds the `FormalCircuit`:
  * `CompressBlock.circuit`    — message schedule + 64 rounds + Davies-Meyer
-/

/-!
## FormalCircuit for full block compression (messageSchedule + 64 rounds + Davies-Meyer)
-/

namespace CompressBlock

structure Inputs (F : Type) where
  state : SHA256State F
  block : SHA256Block F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let w ← MessageSchedule.circuit input.block
  let state' ← SHA256Rounds.circuit ⟨input.state, w⟩
  Circuit.mapFinRange 8 fun (i : Fin 8) =>
    Add32.circuit ⟨input.state[i], state'[i]⟩

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 16, Normalized input.block[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.compressBlock (input.state.map valueBits) (input.block.map valueBits)
  ∧ ∀ i : Fin 8, Normalized out[i]

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [MessageSchedule.circuit, MessageSchedule.Spec, MessageSchedule.Assumptions,
    SHA256Rounds.circuit, SHA256Rounds.Spec, SHA256Rounds.Assumptions,
    Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨h_state_norm, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched, h_rounds, h_add⟩ := h_holds
  have h_sched_full := h_sched h_block_norm
  have h_sched_val := fun i => (h_sched_full i).1
  have h_sched_norm := fun i => (h_sched_full i).2
  have h_rounds_full := h_rounds ⟨h_state_norm, h_sched_norm⟩
  have h_rounds_val := h_rounds_full.1
  have h_rounds_norm := h_rounds_full.2
  -- Per-position antecedents for h_add (lifted via getElem_eval_vector / eval_var_fields)
  have h_state_a : ∀ i : Fin 8,
      Normalized (Vector.map (Expression.eval env) input_var_state[i.val]) := by
    intro i
    rw [← CircuitType.eval_var_fields, getElem_eval_vector, h_input_state]
    exact h_state_norm i
  have h_state_b : ∀ i : Fin 8,
      Normalized (Vector.map (Expression.eval env)
        (SHA256Rounds.stateVar (i₀ + 48 * 227) input_var_state 64)[i.val]) := by
    intro i
    have := h_rounds_norm i
    rw [← getElem_eval_vector, CircuitType.eval_var_fields] at this
    exact this
  -- Bridge: Vector.map valueBits of evaluated message schedule = Specs.SHA256.messageSchedule
  have h_sched_map :
      Vector.map valueBits (eval env (MessageSchedule.varSchedule i₀ input_var_block 48))
        = Specs.SHA256.messageSchedule (Vector.map valueBits input_block) := by
    ext j hj
    simp only [Vector.getElem_map]
    exact h_sched_val ⟨j, hj⟩
  -- Per-position value equation: bridging valueBits of var-output to value-level state.
  have h_val_eq : ∀ i : Fin 8,
      valueBits (Vector.map (Expression.eval env) input_var_state[i.val])
        = valueBits input_state[i.val] := by
    intro i
    rw [← CircuitType.eval_var_fields, getElem_eval_vector, h_input_state]
  have h_rounds_eq : ∀ i : Fin 8,
      valueBits (Vector.map (Expression.eval env)
        (SHA256Rounds.stateVar (i₀ + 48 * 227) input_var_state 64)[i.val])
        = (Specs.SHA256.sha256Compress (input_state.map valueBits)
            (Specs.SHA256.messageSchedule (input_block.map valueBits)))[i.val]'i.isLt := by
    intro i
    rw [← CircuitType.eval_var_fields, getElem_eval_vector]
    have := congrArg (fun v => v[i.val]'i.isLt) h_rounds_val
    simp only [Vector.getElem_map] at this
    rw [this, h_sched_map]
  -- Helper to convert `eval env <mapFinRange>[i]` to the per-position var form.
  have h_index : ∀ (i : ℕ) (hi : i < 8),
      (eval env ((Vector.mapFinRange 8 fun (j : Fin 8) ↦
              Vector.mapRange 32 fun i_1 ↦
                var { index := i₀ + 48 * 227 + 64 * 455 + j.val * 33 + i_1 }) :
            Var SHA256State (F p)))[i]'hi
          = Vector.map (Expression.eval env)
              (Vector.mapRange 32 fun i_1 ↦
                var (F := F p) { index := i₀ + 48 * 227 + 64 * 455 + i * 33 + i_1 }) := by
    intro i hi
    rw [← getElem_eval_vector, CircuitType.eval_var_fields, Vector.getElem_mapFinRange]
  simp_all only [implies_true, and_self, forall_const, and_true]
  -- Value equality
  simp only [Specs.SHA256.compressBlock]
  ext i hi
  have ⟨h_val, _⟩ := h_add ⟨i, hi⟩
  simp only at h_val
  rw [Vector.getElem_map, h_index i hi, h_val,
      Vector.getElem_mapFinRange]
  simp only [_root_.add32, circuit_norm]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [MessageSchedule.circuit, MessageSchedule.Spec, MessageSchedule.Assumptions,
    SHA256Rounds.circuit, SHA256Rounds.Spec, SHA256Rounds.Assumptions,
    Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨h_state_norm, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched_impl, h_rounds_impl, _⟩ := h_env
  -- Extract directly from h_sched_impl/h_rounds_impl applied to assumptions.
  have h_sched_full := h_sched_impl h_block_norm
  have h_sched_norm := fun i => (h_sched_full i).2
  have h_rounds_full := h_rounds_impl ⟨h_state_norm, h_sched_norm⟩
  have h_rounds_norm := h_rounds_full.2
  refine ⟨h_block_norm, ⟨h_state_norm, h_sched_norm⟩, ?_⟩
  intro i
  refine ⟨?_, ?_⟩
  · -- Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[i.val])
    rw [← CircuitType.eval_var_fields, getElem_eval_vector, h_input_state]
    exact h_state_norm i
  · -- Normalized (Vector.map (Expression.eval env.toEnvironment) (stateVar ...)[i.val])
    have := h_rounds_norm i
    rw [← getElem_eval_vector, CircuitType.eval_var_fields] at this
    exact this

def circuit : FormalCircuit (F p) Inputs SHA256State where
  main; elaborated; Assumptions; Spec; soundness; completeness

attribute [local irreducible] main MessageSchedule.circuit SHA256Rounds.circuit Add32.circuit

private theorem messageScheduleComputableWitnesses :
    (MessageSchedule.circuit (p := p)).ComputableWitnesses :=
  MessageSchedule.computableWitnesses

private theorem sha256RoundsComputableWitnesses :
    (SHA256Rounds.circuit (p := p)).ComputableWitnesses :=
  SHA256Rounds.computableWitnesses

private theorem add32ComputableWitnesses :
    (Add32.circuit (p := p)).ComputableWitnesses :=
  Add32.computableWitnesses

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  have hstruct :
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        input env env' offset ((main input).operations offset) := by
    unfold main
    let scheduleCircuit : Circuit (F p) (Var SHA256Schedule (F p)) :=
      MessageSchedule.circuit input.block
    let schedule := scheduleCircuit.output offset
    let roundsOffset := offset + scheduleCircuit.localLength offset
    let roundsCircuit : Circuit (F p) (Var SHA256State (F p)) :=
      SHA256Rounds.circuit ⟨input.state, schedule⟩
    let state' := roundsCircuit.output roundsOffset
    let addOffset := roundsOffset + roundsCircuit.localLength roundsOffset
    let addBody : Fin 8 → Circuit (F p) (Var (fields 32) (F p)) :=
      fun i => Add32.circuit ⟨input.state[i], state'[i]⟩
    have h_messageSchedule := messageScheduleComputableWitnesses (p := p)
    have h_sha256Rounds := sha256RoundsComputableWitnesses (p := p)
    have h_add32 := add32ComputableWitnesses (p := p)
    have h_schedule_len : scheduleCircuit.localLength offset = 48 * 227 := by
      simp [scheduleCircuit, MessageSchedule.circuit, circuit_norm]
    have h_rounds_len : roundsCircuit.localLength roundsOffset = 64 * 455 := by
      simp [roundsCircuit, SHA256Rounds.circuit, circuit_norm]
    simp only [
      Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.mapFinRange_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
    and_intros
    · exact @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
        (F p) _ Inputs SHA256Block SHA256Schedule _ _ _
        MessageSchedule.circuit input input.block offset
        (by
          intro env env' h_input
          simp [circuit_norm] at h_input ⊢
          exact h_input.2)
        h_messageSchedule env env'
    · exact @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (F p) _ Inputs SHA256Rounds.Inputs SHA256State _ _ _
        SHA256Rounds.circuit input ⟨input.state, schedule⟩ roundsOffset
        (by
          intro k env env' hle h_agree h_input
          have h_parent_input := h_input
          simp [circuit_norm] at h_input ⊢
          constructor
          · exact h_input.1
          · have h_sched_agree : env.AgreesBelow (offset + 48 * 227) env' :=
              ProverEnvironment.agreesBelow_of_le h_agree (by
                simpa [roundsOffset, h_schedule_len] using hle)
            have h_block_eval : eval env input.block = eval env' input.block := by
              simpa [circuit_norm] using
                congrArg (fun x : Inputs (F p) => x.block) h_parent_input
            have h_schedule_output :
                schedule = MessageSchedule.varSchedule offset input.block 48 := by
              simp [schedule, scheduleCircuit, MessageSchedule.circuit, circuit_norm]
            rw [h_schedule_output]
            apply Vector.ext
            intro j hj
            rw [← getElem_eval_vector env.toEnvironment
                (MessageSchedule.varSchedule offset input.block 48) j hj,
              ← getElem_eval_vector env'.toEnvironment
                (MessageSchedule.varSchedule offset input.block 48) j hj]
            apply Vector.ext
            intro b hb
            rw [← ProvableType.getElem_eval_fields env.toEnvironment
                ((MessageSchedule.varSchedule offset input.block 48)[j]'hj) b hb,
              ← ProvableType.getElem_eval_fields env'.toEnvironment
                ((MessageSchedule.varSchedule offset input.block 48)[j]'hj) b hb]
            exact MessageSchedule.eval_mem_varSchedule_of_agreesBelow
              (offset := offset) (k := 48) (by omega) h_sched_agree h_block_eval
              j hj (by omega) _ (Vector.getElem_mem hb))
        h_sha256Rounds env env'
    · intro i
      exact @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (F p) _ Inputs Add32.Inputs (fields 32) _ _ _
        Add32.circuit input ⟨input.state[i], state'[i]⟩
        (addOffset + i.val * (addBody 0).localLength)
        (by
          intro k env env' hle h_agree h_input
          simp [circuit_norm] at h_input ⊢
          constructor
          · intro a ha
            have hword :
                Vector.map (Expression.eval env.toEnvironment) input.state[i] =
                  Vector.map (Expression.eval env'.toEnvironment) input.state[i] := by
              rw [← CircuitType.eval_var_fields env.toEnvironment (input.state[i]),
                ← CircuitType.eval_var_fields env'.toEnvironment (input.state[i])]
              simpa [getElem_eval_vector] using
                congrArg (fun state : SHA256State (F p) => state[i.val]'i.isLt) h_input.1
            simp only [Vector.mem_iff_getElem] at ha
            rcases ha with ⟨b, hb, hget⟩
            rw [← hget]
            simpa [Vector.getElem_map] using Vector.ext_iff.mp hword b hb
          · have h_rounds_agree : env.AgreesBelow (roundsOffset + 64 * 455) env' :=
              ProverEnvironment.agreesBelow_of_le h_agree (by
                simp [addOffset, h_rounds_len] at hle ⊢
                omega)
            have h_state_output :
                state' = SHA256Rounds.stateVar roundsOffset input.state 64 := by
              simp [state', roundsCircuit, SHA256Rounds.circuit, circuit_norm]
            rw [h_state_output]
            exact SHA256Rounds.eval_mem_stateVar_of_agreesBelow
              (offset := roundsOffset) (k := 64) (by omega) h_rounds_agree h_input.1 i.val i.isLt)
        h_add32 env env'
  exact
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
      input env env' hstruct

lemma eval_mem_output_of_agreesBelow {offset : ℕ}
    {env env' : ProverEnvironment (F p)}
    (input : Var Inputs (F p))
    (h_agree : env.AgreesBelow (offset + 48 * 227 + 64 * 455 + 8 * 33) env') :
    ∀ (j : ℕ) (hj : j < 8),
      ∀ a ∈ ((main input).output offset)[j]'hj,
        Expression.eval env.toEnvironment a =
          Expression.eval env'.toEnvironment a := by
  intro j hj a ha
  simp only [main, Circuit.mapFinRange.output_eq,
    circuit_norm] at ha
  simp [Add32.circuit, MessageSchedule.circuit, SHA256Rounds.circuit, circuit_norm] at ha
  exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
    (offset := offset + 48 * 227 + 64 * 455 + j * 33) (m := 32) h_agree (by omega) a ha

lemma eval_output_of_agreesBelow {offset : ℕ}
    {env env' : ProverEnvironment (F p)}
    (input : Var Inputs (F p))
    (h_agree : env.AgreesBelow (offset + 48 * 227 + 64 * 455 + 8 * 33) env') :
    eval env.toEnvironment ((main input).output offset) =
      eval env'.toEnvironment ((main input).output offset) := by
  apply Vector.ext
  intro j hj
  rw [← getElem_eval_vector env.toEnvironment ((main input).output offset) j hj,
    ← getElem_eval_vector env'.toEnvironment ((main input).output offset) j hj]
  apply Vector.ext
  intro b hb
  rw [← ProvableType.getElem_eval_fields env.toEnvironment (((main input).output offset)[j]'hj) b hb,
    ← ProvableType.getElem_eval_fields env'.toEnvironment (((main input).output offset)[j]'hj) b hb]
  exact eval_mem_output_of_agreesBelow input h_agree j hj _ (Vector.getElem_mem hb)

lemma eval_circuit_output_of_agreesBelow {offset : ℕ}
    {env env' : ProverEnvironment (F p)}
    (input : Var Inputs (F p))
    (h_agree : env.AgreesBelow (offset + 48 * 227 + 64 * 455 + 8 * 33) env') :
    eval env.toEnvironment ((circuit (p := p)).output input offset) =
      eval env'.toEnvironment ((circuit (p := p)).output input offset) := by
  change eval env.toEnvironment (ElaboratedCircuit.output main input offset) =
    eval env'.toEnvironment (ElaboratedCircuit.output main input offset)
  rw [← elaborated.output_eq input offset]
  exact eval_output_of_agreesBelow input h_agree

end CompressBlock
end Solution.SHA256
end
