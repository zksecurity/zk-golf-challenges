import Solution.SHA256CompressGF2.ScheduleStepTheorems

/-!
# `ScheduleStep`: one message-schedule step

The message schedule step
`W[t] = add32 (add32 (σ₁ W[t-2]) W[t-7]) (add32 (σ₀ W[t-15]) W[t-16])`.
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace ScheduleStep

/-- Input `v = W[t-16] ‖ W[t-15] ‖ W[t-7] ‖ W[t-2]`; output the materialized
`W[t] = add32 (add32 (σ₁ W[t-2]) W[t-7]) (add32 (σ₀ W[t-15]) W[t-16])`. -/
def main (v : Var (fields 128) (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let a1 ← Add32.circuit ⟨lowerSigma1E (w128 v 3), w128 v 2⟩
  let a2 ← Add32.circuit ⟨lowerSigma0E (w128 v 1), w128 v 0⟩
  let a3 ← Add32.circuit ⟨a1, a2⟩
  let W ← Pin32.circuit a3
  return W

instance elaborated : ElaboratedCircuit (F p2) (fields 128) (fields 32) main := by
  elaborate_circuit

def Assumptions (_ : fields 128 (F p2)) : Prop := True

/-- Word-level schedule step on the packed windows. -/
def Spec (v : fields 128 (F p2)) (out : fields 32 (F p2)) : Prop :=
  toNat out
    = add32 (add32 (Specs.SHA256.lowerSigma1 (wordAt 32 v 3)) (wordAt 32 v 2))
        (add32 (Specs.SHA256.lowerSigma0 (wordAt 32 v 1)) (wordAt 32 v 0))

theorem soundness : Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Add32.circuit, Pin32.circuit,
    Add32.Assumptions, Pin32.Assumptions, Add32.Spec, Pin32.Spec]
  obtain ⟨h1, h2, h3, h4⟩ := h_holds
  have hv : ∀ (m : ℕ) (hm : m < 128),
      Expression.eval env (input_var[m]'hm) = input[m]'hm := by
    intro m hm
    have h := Vector.ext_iff.mp h_input m hm
    rwa [Vector.getElem_map] at h
  have hw : ∀ k : ℕ, 32 * k + 32 ≤ 128 →
      toNat (Vector.map (Expression.eval env) (w128 input_var k)) = wordAt 32 input k := by
    intro k hk
    refine toNat_map_eval_window _ input k hk ?_
    intro j hj
    unfold w128 a128
    rw [Vector.getElem_ofFn]
    have hlt : 32 * k + j < 128 := by omega
    simp only [Nat.mod_eq_of_lt hlt]
    exact hv _ hlt
  rw [h4, h3, h1, h2, toNat_eval_lowerSigma1E, toNat_eval_lowerSigma0E,
    hw 3 (by norm_num), hw 2 (by norm_num), hw 1 (by norm_num), hw 0 (by norm_num)]
  rfl

theorem completeness : Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Add32.circuit, Add32.Assumptions, Pin32.circuit, Pin32.Assumptions, and_self]

def circuit : FormalCircuit (F p2) (fields 128) (fields 32) :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

/-- The first adder's input, as a function of the step input. -/
theorem eval_in1_congr {v : Var (fields 128) (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) :
    eval env (⟨lowerSigma1E (w128 v 3), w128 v 2⟩ : Var Add32.Inputs (F p2))
      = eval env' (⟨lowerSigma1E (w128 v 3), w128 v 2⟩ : Var Add32.Inputs (F p2)) :=
  Add32.eval_mk_congr (eval_lowerSigma1E_congr (eval_w128_congr h 3)) (eval_w128_congr h 2)

/-- The second adder's input, as a function of the step input. -/
theorem eval_in2_congr {v : Var (fields 128) (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) :
    eval env (⟨lowerSigma0E (w128 v 1), w128 v 0⟩ : Var Add32.Inputs (F p2))
      = eval env' (⟨lowerSigma0E (w128 v 1), w128 v 0⟩ : Var Add32.Inputs (F p2)) :=
  Add32.eval_mk_congr (eval_lowerSigma0E_congr (eval_w128_congr h 1)) (eval_w128_congr h 0)

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    Add32.subcircuit_localLength, Pin32.subcircuit_localLength,
    and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Add32.circuit input _ offset (fun _ _ h => eval_in1_congr h)
      Add32.computableWitnesses env env'
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Add32.circuit input _ _ (fun _ _ h => eval_in2_congr h)
      Add32.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32.circuit input _ _ ?_ Add32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32.eval_mk_congr
      (Add32.eval_subOut_of_agreesBelow _ offset (by omega) h_agree (eval_in1_congr h_input))
      (Add32.eval_subOut_of_agreesBelow _ (offset + 31) (by omega) h_agree
        (eval_in2_congr h_input))
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Pin32.circuit input _ _ ?_ Pin32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32.eval_subOut_of_agreesBelow _ (offset + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr
        (Add32.eval_subOut_of_agreesBelow _ offset (by omega) h_agree (eval_in1_congr h_input))
        (Add32.eval_subOut_of_agreesBelow _ (offset + 31) (by omega) h_agree
          (eval_in2_congr h_input)))

theorem subcircuit_localLength (v : Var (fields 128) (F p2)) (m : ℕ) :
    (subcircuit circuit v).localLength m = 125 := rfl

/-- The step's output is the trailing `Pin32` witness block at relative offset 93. -/
theorem eval_subOut_of_agreesBelow (v : Var (fields 128) (F p2)) (n : ℕ) {k : ℕ}
    (hk : n + 125 ≤ k)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit v).output n)
      = eval env' ((subcircuit circuit v).output n) := by
  have hout : (subcircuit circuit v).output n = varFromOffset (fields 32) (n + 93) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

end ComputableWitness

end ScheduleStep

end Solution.SHA256CompressGF2
