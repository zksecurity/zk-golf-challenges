import Solution.SHA256CompressGF2Canonical.Sched16CanonTheorems
import Solution.SHA256CompressGF2Canonical.ScheduleStepCanon
import Solution.SHA256CompressGF2Canonical.Theorems
import Solution.SHA256CompressGF2.Sched16Theorems
import Solution.SHA256CompressGF2.PureSchedule
import Solution.SHA256CompressGF2.Cost
import Challenge.Utils.CostR1CSCanonical
import Mathlib.Tactic.IntervalCases

/-!
# `Sched16Canon` gadget
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Sched16Canon

def main (v : Var (fields 512) (F p2)) : Circuit (F p2) (Var (fields 512) (F p2)) := do
  let w ← Circuit.foldlRange 16
    ((Vector.ofFn fun j : Fin 16 => q512 v j.val) ++
      Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))
    (fun w i => do
      let ui ← ScheduleStepCanon.circuit (c128 (w[i.val]'(by omega)) (w[i.val + 1]'(by omega))
        (w[i.val + 9]'(by omega)) (w[i.val + 14]'(by omega)))
      return w.set (16 + i.val) ui (by omega))
    constantLength
  return c512x (w[16]'(by norm_num)) (w[17]'(by norm_num)) (w[18]'(by norm_num)) (w[19]'(by norm_num))
    (w[20]'(by norm_num)) (w[21]'(by norm_num)) (w[22]'(by norm_num)) (w[23]'(by norm_num))
    (w[24]'(by norm_num)) (w[25]'(by norm_num)) (w[26]'(by norm_num)) (w[27]'(by norm_num))
    (w[28]'(by norm_num)) (w[29]'(by norm_num)) (w[30]'(by norm_num)) (w[31]'(by norm_num))

instance elaborated : ElaboratedCircuit (F p2) (fields 512) (fields 512) main := by
  elaborate_circuit_with {
    output _ i₀ := c512x (stepWord i₀ 0) (stepWord i₀ 1) (stepWord i₀ 2) (stepWord i₀ 3)
      (stepWord i₀ 4) (stepWord i₀ 5) (stepWord i₀ 6) (stepWord i₀ 7)
      (stepWord i₀ 8) (stepWord i₀ 9) (stepWord i₀ 10) (stepWord i₀ 11)
      (stepWord i₀ 12) (stepWord i₀ 13) (stepWord i₀ 14) (stepWord i₀ 15)
  } using by
    refine ⟨fun a => rfl, fun a n => ?_, ?_, ?_⟩
    · have hfold : (Fin.foldl 16
          (fun (acc : Vector (fields 32 (Expression (F p2))) 32) (i : Fin 16) =>
            acc.set (16 + i.val)
              (Vector.mapRange 32 fun i_1 => var { index := n + i.val * 218 + 62 + 62 + 62 + i_1 })
              (by omega))
          ((Vector.ofFn fun j : Fin 16 => q512 a j.val) ++
            Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2)))))
          = varBuf n a 16 := finFoldl_eq_varBuf n a
      simp only [circuit_norm, hfold]
      rw [varBuf_out n a 0 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 1 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 2 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 3 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 4 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 5 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 6 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 7 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 8 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 9 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 10 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 11 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 12 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 13 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 14 (by norm_num) 16 (by norm_num) (by norm_num),
        varBuf_out n a 15 (by norm_num) 16 (by norm_num) (by norm_num)]
    · simp only [circuit_norm]
    · simp only [circuit_norm]

def Assumptions (_ : fields 512 (F p2)) : Prop := True

/-- The 16 output words are the schedule extended by one window. -/
def Spec (v out : fields 512 (F p2)) : Prop :=
  toWords 32 16 out = PureSchedule.extend16 (toWords 32 16 v)

theorem soundness : Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, ScheduleStepCanon.Assumptions, ScheduleStepCanon.Spec]
  set x := toWords 32 16 input with hx
  have hq : ∀ m (hm : m < 16),
      toNat (Vector.map (Expression.eval env) (q512 input_var m)) = x[m]'hm := by
    intro m hm
    rw [toNat_eval_q512 env input_var m (by omega), h_input]
    simp only [hx, toWords, Vector.getElem_ofFn]
  have Q : ∀ k, k ≤ 16 → ∀ j (hj : j < 32),
      toNat (Vector.map (Expression.eval env) ((varBuf i₀ input_var k)[j]'hj))
        = (PureSchedule.ext32 x k)[j]'hj := by
    intro k
    induction k with
    | zero =>
      intro _ j hj
      by_cases hj16 : j < 16
      · rw [show (varBuf i₀ input_var 0)[j]'hj = q512 input_var j from by
              show ((Vector.ofFn fun jj : Fin 16 => q512 input_var jj.val) ++ _)[j]'hj = _
              rw [Vector.getElem_append_left hj16, Vector.getElem_ofFn]]
        rw [hq j hj16]
        rw [show (PureSchedule.ext32 x 0)[j]'hj = x[j]'hj16 from by
              rw [PureSchedule.ext32]
              show (x ++ Vector.replicate 16 0)[j]'hj = _
              rw [Vector.getElem_append_left hj16]]
      · rw [show (varBuf i₀ input_var 0)[j]'hj
                = Vector.replicate 32 (0 : Expression (F p2)) from by
              show ((Vector.ofFn fun jj : Fin 16 => q512 input_var jj.val) ++
                Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))[j]'hj = _
              rw [Vector.getElem_append_right hj (by omega), Vector.getElem_replicate]]
        rw [Sched16.toNat_replicate0]
        rw [show (PureSchedule.ext32 x 0)[j]'hj = 0 from by
              rw [PureSchedule.ext32]
              show (x ++ Vector.replicate 16 (0 : ℕ))[j]'hj = _
              rw [Vector.getElem_append_right hj (by omega), Vector.getElem_replicate]]
    | succ k ih =>
      intro hk j hj
      have hk16 : k < 16 := by omega
      have hvb : varBuf i₀ input_var (k + 1)
          = (varBuf i₀ input_var k).set (16 + k) (stepWord i₀ k) (by omega) := by
        conv_lhs => rw [varBuf]
        rw [dif_pos hk16]
      have hstep := h_holds ⟨k, hk16⟩
      rw [foldlAcc_eq_varBuf i₀ input_var k hk16] at hstep
      replace hstep := hstep (by simp only [ScheduleStepCanon.circuit, ScheduleStepCanon.Assumptions])
      rw [show ScheduleStepCanon.circuit.Spec = ScheduleStepCanon.Spec from rfl] at hstep
      simp only [ScheduleStepCanon.Spec, wordAt_eval_c128_0, wordAt_eval_c128_1, wordAt_eval_c128_2,
        wordAt_eval_c128_3, scheduleStep_output, scheduleStep_localLength] at hstep
      rw [ih (by omega) (k + 14) (by omega), ih (by omega) (k + 9) (by omega),
        ih (by omega) (k + 1) (by omega), ih (by omega) k (by omega)] at hstep
      by_cases hjk : j = 16 + k
      · subst hjk
        rw [hvb, Vector.getElem_set_self, stepWord, hstep]
        rw [PureSchedule.ext32, dif_pos hk16, Vector.getElem_set, if_pos (by omega : k + 16 = 16 + k)]
      · rw [hvb, Vector.getElem_set_ne (by omega) hj (by omega),
          PureSchedule.ext32_succ_ne x k j hj (by omega)]
        exact ih (by omega) j hj
  have hcell : ∀ j (hj : j < 16),
      toNat (Vector.map (Expression.eval env) (stepWord i₀ j))
        = (PureSchedule.ext32 x 16)[16 + j]'(by omega) := by
    intro j hj
    rw [← varBuf_out i₀ input_var j hj 16 (by omega) (le_refl 16)]
    exact Q 16 (le_refl 16) (16 + j) (by omega)
  refine ⟨?_, ?_⟩
  · refine Vector.ext fun k hk => ?_
    simp only [toWords, Vector.getElem_ofFn, PureSchedule.extend16]
    rw [wordAt_eval_c512x_sel env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k hk]
    interval_cases k <;> (simp only [c512sel]; exact hcell _ (by norm_num))
  · intro i
    exact Or.inl rfl

theorem completeness : Completeness (F p2) main Assumptions := by
  circuit_proof_start
  intro i
  simp only [ScheduleStepCanon.circuit, ScheduleStepCanon.Assumptions]

def circuit : FormalCircuit (F p2) (fields 512) (fields 512) :=
  { main, elaborated, Assumptions, Spec, soundness, completeness := by simp only [completeness] }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

theorem subcircuit_localLength (v : Var (fields 512) (F p2)) (m : ℕ) :
    (subcircuit circuit v).localLength m = 3488 := rfl

/-- The chunk's output is the 16 witnessed canonical step words. -/
theorem eval_subOut_of_agreesBelow (v : Var (fields 512) (F p2)) (n : ℕ) {kk : ℕ}
    (hk : n + 3488 ≤ kk) {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow kk env') :
    eval env ((subcircuit circuit v).output n)
      = eval env' ((subcircuit circuit v).output n) := by
  have hstep : ∀ t : ℕ, t < 16 → eval env (stepWord n t) = eval env' (stepWord n t) :=
    fun t ht => eval_stepWord_of_agreesBelow n t (by omega) h_agree
  refine eval_c512x_congr fun t ht => ?_
  interval_cases t <;> (simp only [c512sel]; exact hstep _ (by norm_num))

-- Keep the unifier from expanding the 218-witness step body while peeling the
-- loop; the offsets and outputs are supplied by the `rfl` lemmas instead.
attribute [local irreducible] main

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.foldlRange_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    ScheduleStepCanon.subcircuit_localLength, and_true]
  intro i
  obtain ⟨iv, hiv⟩ := i
  rw [foldlAcc_eq_varBuf_do offset input iv hiv]
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    ScheduleStepCanon.circuit input _ _ ?_ ScheduleStepCanon.computableWitnesses env env'
  intro kk e e' hle h_agree h_input
  -- the loop offset is `offset + iv * 218` (`stepBody_localLength`, definitionally)
  have hle' : offset + iv * 218 ≤ kk := hle
  exact eval_c128_congr
    (eval_varBuf_getElem_of_agreesBelow offset input h_agree h_input iv (by omega) iv (by omega))
    (eval_varBuf_getElem_of_agreesBelow offset input h_agree h_input iv (by omega)
      (iv + 1) (by omega))
    (eval_varBuf_getElem_of_agreesBelow offset input h_agree h_input iv (by omega)
      (iv + 9) (by omega))
    (eval_varBuf_getElem_of_agreesBelow offset input h_agree h_input iv (by omega)
      (iv + 14) (by omega))

end ComputableWitness

end Sched16Canon

end Solution.SHA256CompressGF2
