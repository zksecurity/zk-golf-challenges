import Solution.SHA256CompressGF2Canonical.Rounds16CanonTheorems
import Solution.SHA256CompressGF2Canonical.RoundCanon
import Solution.SHA256CompressGF2.Rounds16Theorems
import Solution.SHA256CompressGF2.PureRounds
import Solution.SHA256CompressGF2.Cost
import Challenge.Utils.CostR1CSCanonical
import Solution.SHA256CompressGF2Canonical.PinCanon

/-!
# `Rounds16Canon` gadget
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Rounds16Canon

def main (r0 : ℕ) (v : Var (fields 768) (F p2)) : Circuit (F p2) (Var (fields 256) (F p2)) := do
  let s16 ← Circuit.foldlRange 16 (st768 v) (fun s i =>
    RoundCanon.circuit (kAt (r0 + i.val)) (c288s s (q768 v (8 + i.val)))) (constantLength r0 v)
  Pin256Canon.circuit s16

instance elaborated (r0 : ℕ) :
    ElaboratedCircuit (F p2) (fields 768) (fields 256) (main r0) := by
  elaborate_circuit_with {
    localLength _ := 9248
    output _ i₀ := varFromOffset (fields 256) (i₀ + 8992)
  } using by
    refine ⟨fun a => ?_, fun a n => ?_, ?_, ?_⟩
    · simp only [circuit_norm]
    · simp only [circuit_norm]
    · simp only [circuit_norm]
    · simp only [circuit_norm]

def Assumptions (_ : fields 768 (F p2)) : Prop := True

/-- The output state is `applyRounds16` of the input state and schedule window. -/
def Spec (r0 : ℕ) (v : fields 768 (F p2)) (out : fields 256 (F p2)) : Prop :=
  toWords 32 8 out = PureRounds.applyRounds16 r0
    (Vector.ofFn fun i : Fin 16 => wordAt 32 v (8 + i.val))
    (Vector.ofFn fun i : Fin 8 => wordAt 32 v i.val)

set_option maxRecDepth 100000 in
theorem soundness (r0 : ℕ) : Soundness (F p2) (main r0) Assumptions (Spec r0) := by
  circuit_proof_start [main, Spec, RoundCanon.Assumptions, RoundCanon.Spec,
    Pin256.Assumptions, Pin256.Spec]
  set schedOf := (Vector.ofFn fun i : Fin 16 => wordAt 32 input (8 + i.val)) with hsc
  set stateOf := (Vector.ofFn fun i : Fin 8 => wordAt 32 input i.val) with hst
  have hLL : ∀ (k : ℕ) (x : Var (fields 288) (F p2)),
      (RoundCanon.circuit k).localLength x = 562 := by
    intro k x; simp [circuit_norm, RoundCanon.circuit, RoundCanon.elaborated]
  obtain ⟨h_fold, hpin⟩ := h_holds
  simp only [hLL] at hpin
  have hsched : ∀ j (hj : j < 16), PureRounds.at16 schedOf j = wordAt 32 input (8 + j) := by
    intro j hj
    rw [PureRounds.at16_lt schedOf j hj, hsc, Vector.getElem_ofFn]
  have Q : ∀ k, k ≤ 16 →
      (Vector.ofFn fun i : Fin 8 =>
          wordAt 32 (Vector.map (Expression.eval env) (stateVar256 r0 i₀ input_var k)) i.val)
        = PureRounds.applyN r0 schedOf k stateOf := by
    intro k
    induction k with
    | zero =>
      intro _
      show (Vector.ofFn fun i : Fin 8 =>
          wordAt 32 (Vector.map (Expression.eval env) (st768 input_var)) i.val) = stateOf
      rw [hst]
      refine Vector.ext fun i hi => ?_
      rw [Vector.getElem_ofFn, Vector.getElem_ofFn, wordAt_eval_st768 env input_var i hi, h_input]
    | succ k ih =>
      intro hk
      have hk16 : k < 16 := by omega
      have hstep := h_fold ⟨k, hk16⟩
      rw [foldlAcc_eq_stateVar256 r0 i₀ input_var k hk16] at hstep
      replace hstep := hstep (by simp only [RoundCanon.circuit, RoundCanon.Assumptions])
      rw [show (RoundCanon.circuit (kAt (r0 + k))).Spec = RoundCanon.Spec (kAt (r0 + k)) from rfl] at hstep
      simp only [RoundCanon.Spec] at hstep
      rw [ofFn_wordAt_c288s, wordAt_eval_c288s_msg,
        toNat_eval_q768 env input_var (8 + k) (by omega), h_input, ih (by omega)] at hstep
      rw [← hsched k hk16] at hstep
      rw [← show PureRounds.applyN r0 schedOf (k + 1) stateOf
          = Specs.SHA256.sha256Round (PureRounds.applyN r0 schedOf k stateOf) (kAt (r0 + k))
              (PureRounds.at16 schedOf k) from rfl] at hstep
      rw [stateVar256]
      exact hstep
  simp only [Pin256Canon.circuit, Pin256.elaborated, Pin256.Assumptions, Pin256.Spec, true_implies] at hpin
  rw [fin_foldl_eq_stateVar256 r0 i₀ input_var 16] at hpin
  rw [PureRounds.applyRounds16_eq_applyN, ← Q 16 (le_refl 16)]
  simp only [toWords]
  refine ⟨?_, fun i => Or.inl rfl, Or.inl rfl⟩
  rw [show (Vector.map (Expression.eval env) (Vector.mapRange 256 fun i => var { index := i₀ + 8992 + i }))
        = Vector.map (Expression.eval env) (stateVar256 r0 i₀ input_var 16) from hpin]

theorem completeness (r0 : ℕ) : Completeness (F p2) (main r0) Assumptions := by
  circuit_proof_start
  simp [RoundCanon.circuit, RoundCanon.Assumptions, Pin256Canon.circuit, Pin256.Assumptions]

def circuit (r0 : ℕ) : FormalCircuit (F p2) (fields 768) (fields 256) :=
  { main := main r0, elaborated := elaborated r0, Assumptions, Spec := Spec r0,
    soundness := soundness r0, completeness := by simp only [completeness] }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

theorem subcircuit_localLength (r0 : ℕ) (v : Var (fields 768) (F p2)) (m : ℕ) :
    (subcircuit (circuit r0) v).localLength m = 9248 := rfl

/-- The chunk's output is the trailing `Pin256Canon` witness block at relative
offset 8992. -/
theorem eval_subOut_of_agreesBelow (r0 : ℕ) (v : Var (fields 768) (F p2)) (n : ℕ) {kk : ℕ}
    (hk : n + 9248 ≤ kk) {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow kk env') :
    eval env ((subcircuit (circuit r0) v).output n)
      = eval env' ((subcircuit (circuit r0) v).output n) := by
  have hout : (subcircuit (circuit r0) v).output n = varFromOffset (fields 256) (n + 8992) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

-- Keep the unifier from expanding the 562-witness round body while peeling the
-- loop; the offsets and outputs are supplied by the `rfl` lemmas instead.
attribute [local irreducible] RoundCanon.circuit Pin256Canon.circuit main

theorem computableWitnesses (r0 : ℕ) : (circuit r0).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main r0 input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.foldlRange_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    RoundCanon.subcircuit_localLength, Circuit.foldlRange.localLength_eq,
    Circuit.foldlRange.output_eq, Nat.reduceMul, gt_iff_lt, Nat.ofNat_pos,
    ↓reduceDIte]
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨iv, hiv⟩ := i
    rw [foldlAcc_eq_stateVar256_var r0 offset input iv hiv]
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (RoundCanon.circuit (kAt (r0 + iv))) input _ _ ?_
      (RoundCanon.computableWitnesses _) env env'
    intro kk e e' hle h_agree h_input
    exact eval_c288s_congr
      (eval_stateVar256_of_agreesBelow r0 offset input h_agree h_input iv (by omega))
      (eval_q768_congr h_input (8 + iv))
  · rw [fin_foldl_subcircuit_eq_stateVar256 r0 offset input 16]
    refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Pin256Canon.circuit input _ _ ?_ Pin256Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact eval_stateVar256_of_agreesBelow r0 offset input h_agree h_input 16 (by omega)

end ComputableWitness

end Rounds16Canon

end Solution.SHA256CompressGF2
