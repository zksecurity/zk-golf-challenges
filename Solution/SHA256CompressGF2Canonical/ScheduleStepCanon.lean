import Solution.SHA256CompressGF2.ScheduleStep
import Solution.SHA256CompressGF2.ScheduleStepTheorems
import Solution.SHA256CompressGF2.Theorems
import Solution.SHA256CompressGF2.Cost
import Solution.SHA256CompressGF2Canonical.Add32Canon
import Solution.SHA256CompressGF2Canonical.Ch32Canon
import Solution.SHA256CompressGF2Canonical.Maj32Canon
import Solution.SHA256CompressGF2Canonical.PinCanon

/-!
# `ScheduleStep` in canonical (C = identity) form

Identical to `Solution.SHA256CompressGF2.ScheduleStep`, but the three adders use
`Add32Canon` (the pinned canonical adder). `Add32Canon` reuses `Add32.Spec` /
`Add32.Assumptions`, so soundness/completeness port verbatim; only the cost
changes (3 × 62 + 32 = 218) and the certificate becomes `IsCidCirc`.
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace ScheduleStepCanon

def main (v : Var (fields 128) (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let a1 ← Add32Canon.circuit ⟨lowerSigma1E (w128 v 3), w128 v 2⟩
  let a2 ← Add32Canon.circuit ⟨lowerSigma0E (w128 v 1), w128 v 0⟩
  let a3 ← Add32Canon.circuit ⟨a1, a2⟩
  let W ← Pin32Canon.circuit a3
  return W

instance elaborated : ElaboratedCircuit (F p2) (fields 128) (fields 32) main := by
  elaborate_circuit

def Assumptions (_ : fields 128 (F p2)) : Prop := True

def Spec (v : fields 128 (F p2)) (out : fields 32 (F p2)) : Prop :=
  toNat out
    = add32 (add32 (Specs.SHA256.lowerSigma1 (wordAt 32 v 3)) (wordAt 32 v 2))
        (add32 (Specs.SHA256.lowerSigma0 (wordAt 32 v 1)) (wordAt 32 v 0))

theorem soundness : Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Add32Canon.circuit, Pin32Canon.circuit,
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
  simp only [Add32Canon.circuit, Add32.Assumptions, Pin32Canon.circuit, Pin32.Assumptions, and_self]

def circuit : FormalCircuit (F p2) (fields 128) (fields 32) :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

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
    Add32Canon.subcircuit_localLength, Pin32Canon.subcircuit_localLength,
    and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Add32Canon.circuit input _ offset (fun _ _ h => ScheduleStep.eval_in1_congr h)
      Add32Canon.computableWitnesses env env'
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Add32Canon.circuit input _ _ (fun _ _ h => ScheduleStep.eval_in2_congr h)
      Add32Canon.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32.eval_mk_congr
      (Add32Canon.eval_subOut_of_agreesBelow _ offset (by omega) h_agree
        (ScheduleStep.eval_in1_congr h_input))
      (Add32Canon.eval_subOut_of_agreesBelow _ (offset + 62) (by omega) h_agree
        (ScheduleStep.eval_in2_congr h_input))
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Pin32Canon.circuit input _ _ ?_ Pin32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32Canon.eval_subOut_of_agreesBelow _ (offset + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr
        (Add32Canon.eval_subOut_of_agreesBelow _ offset (by omega) h_agree
          (ScheduleStep.eval_in1_congr h_input))
        (Add32Canon.eval_subOut_of_agreesBelow _ (offset + 62) (by omega) h_agree
          (ScheduleStep.eval_in2_congr h_input)))

theorem subcircuit_localLength (v : Var (fields 128) (F p2)) (m : ℕ) :
    (subcircuit circuit v).localLength m = 218 := rfl

/-- The canonical step's output is the trailing `Pin32Canon` block at relative
offset 186. -/
theorem eval_subOut_of_agreesBelow (v : Var (fields 128) (F p2)) (n : ℕ) {k : ℕ}
    (hk : n + 218 ≤ k)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit v).output n)
      = eval env' ((subcircuit circuit v).output n) := by
  have hout : (subcircuit circuit v).output n = varFromOffset (fields 32) (n + 186) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

end ComputableWitness

end ScheduleStepCanon

end Solution.SHA256CompressGF2
