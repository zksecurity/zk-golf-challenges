import Solution.SHA256.SHA256Rounds
import Solution.SHA256.MessageSchedule
import Solution.SHA256.Add32
import Challenge.Specs.SHA256

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

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end CompressBlock
end Solution.SHA256
end
