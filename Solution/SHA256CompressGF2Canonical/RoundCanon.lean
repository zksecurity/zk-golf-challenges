import Solution.SHA256CompressGF2.Round
import Solution.SHA256CompressGF2.Theorems
import Solution.SHA256CompressGF2.Cost
import Solution.SHA256CompressGF2Canonical.ScheduleStepCanon
import Solution.SHA256CompressGF2Canonical.PinCanon

/-!
# `Round` in canonical (C = identity) form

Swaps `Ch32`/`Maj32`/`Add32` for their canonical variants (`Pin32` is already
identity-C and is reused). All subcircuit `Spec`s are unchanged, so the
soundness/completeness proofs port with name swaps; cost becomes
`32 + 32 + 7·62 + 2·32 = 562`.
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace RoundCanon

def main (k : ℕ) (v : Var (fields 288) (F p2)) :
    Circuit (F p2) (Var (fields 256) (F p2)) := do
  let ch ← Ch32Canon.circuit (c96 (w288 v 4) (w288 v 5) (w288 v 6))
  let maj ← Maj32Canon.circuit (c96 (w288 v 0) (w288 v 1) (w288 v 2))
  let t1a ← Add32Canon.circuit ⟨w288 v 7, upperSigma1E (w288 v 4)⟩
  let t1b ← Add32Canon.circuit ⟨t1a, ch⟩
  let t1c ← Add32Canon.circuit ⟨t1b, constW k⟩
  let t1 ← Add32Canon.circuit ⟨t1c, w288 v 8⟩
  let t2 ← Add32Canon.circuit ⟨upperSigma0E (w288 v 0), maj⟩
  let en ← Add32Canon.circuit ⟨w288 v 3, t1⟩
  let an ← Add32Canon.circuit ⟨t1, t2⟩
  let A ← Pin32Canon.circuit an
  let E ← Pin32Canon.circuit en
  return outState A E v

instance elaborated (k : ℕ) :
    ElaboratedCircuit (F p2) (fields 288) (fields 256) (main k) := by
  elaborate_circuit

def Assumptions (_ : fields 288 (F p2)) : Prop := True

def Spec (k : ℕ) (v : fields 288 (F p2)) (out : fields 256 (F p2)) : Prop :=
  Vector.ofFn (fun i : Fin 8 => wordAt 32 out i.val)
    = Specs.SHA256.sha256Round (Vector.ofFn fun i : Fin 8 => wordAt 32 v i.val)
        k (wordAt 32 v 8)

theorem soundness (k : ℕ) : Soundness (F p2) (main k) Assumptions (Spec k) := by
  circuit_proof_start [main, Spec, Add32Canon.circuit, Pin32Canon.circuit,
    Ch32Canon.circuit, Maj32Canon.circuit,
    Add32.Assumptions, Pin32.Assumptions, Ch32Canon.Assumptions, Maj32Canon.Assumptions,
    Add32.Spec, Pin32.Spec, Ch32Canon.Spec, Maj32Canon.Spec]
  obtain ⟨hch, hmaj, ht1a, ht1b, ht1c, ht1, ht2, hen, han, hA, hE⟩ := h_holds
  have hv : ∀ (m : ℕ) (hm : m < 288),
      Expression.eval env (input_var[m]'hm) = input[m]'hm := by
    intro m hm
    have h := Vector.ext_iff.mp h_input m hm
    rwa [Vector.getElem_map] at h
  have hw : ∀ l : ℕ, 32 * l + 32 ≤ 288 →
      toNat (Vector.map (Expression.eval env) (w288 input_var l)) = wordAt 32 input l := by
    intro l hl
    refine toNat_map_eval_window _ input l hl ?_
    intro j hj
    unfold w288 a288
    rw [Vector.getElem_ofFn]
    have hlt : 32 * l + j < 288 := by omega
    simp only [Nat.mod_eq_of_lt hlt]
    exact hv _ hlt
  rw [wordAt_eval_c96_0, wordAt_eval_c96_1, wordAt_eval_c96_2,
    hw 4 (by norm_num), hw 5 (by norm_num), hw 6 (by norm_num)] at hch
  rw [wordAt_eval_c96_0, wordAt_eval_c96_1, wordAt_eval_c96_2,
    hw 0 (by norm_num), hw 1 (by norm_num), hw 2 (by norm_num)] at hmaj
  rw [toNat_eval_upperSigma1E, hw 4 (by norm_num), hw 7 (by norm_num)] at ht1a
  rw [ht1a, hch] at ht1b
  rw [ht1b, toNat_eval_constW, Nat.add_mod_mod] at ht1c
  rw [ht1c, hw 8 (by norm_num)] at ht1
  rw [toNat_eval_upperSigma0E, hw 0 (by norm_num), hmaj] at ht2
  rw [ht1, hw 3 (by norm_num)] at hen
  rw [ht1, ht2] at han
  rw [sha256Round_eq]
  simp only [Vector.getElem_ofFn]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_ofFn]
  interval_cases i
  · rw [vec8_0, wordAt_eval_outState_0, hA, han]
    simp only [show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [vec8_1, wordAt_eval_outState_pass env _ _ _ input hv 1 (by omega) (by omega) (by omega)]
  · rw [vec8_2, wordAt_eval_outState_pass env _ _ _ input hv 2 (by omega) (by omega) (by omega)]
  · rw [vec8_3, wordAt_eval_outState_pass env _ _ _ input hv 3 (by omega) (by omega) (by omega)]
  · rw [vec8_4, wordAt_eval_outState_4, hE, hen]
    simp only [show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [vec8_5, wordAt_eval_outState_pass env _ _ _ input hv 5 (by omega) (by omega) (by omega)]
  · rw [vec8_6, wordAt_eval_outState_pass env _ _ _ input hv 6 (by omega) (by omega) (by omega)]
  · rw [vec8_7, wordAt_eval_outState_pass env _ _ _ input hv 7 (by omega) (by omega) (by omega)]

theorem completeness (k : ℕ) : Completeness (F p2) (main k) Assumptions := by
  circuit_proof_start
  simp only [Add32Canon.circuit, Add32.Assumptions, Pin32Canon.circuit, Pin32.Assumptions,
    Ch32Canon.circuit, Ch32Canon.Assumptions, Maj32Canon.circuit, Maj32Canon.Assumptions, and_self]

def circuit (k : ℕ) : FormalCircuit (F p2) (fields 288) (fields 256) :=
  { main := main k, elaborated := elaborated k, Assumptions, Spec := Spec k,
    soundness := soundness k, completeness := completeness k }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

theorem computableWitnesses (k : ℕ) : (circuit k).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main k input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    Ch32Canon.subcircuit_localLength, Maj32Canon.subcircuit_localLength,
    Add32Canon.subcircuit_localLength, Pin32Canon.subcircuit_localLength,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Ch32Canon.circuit input _ (offset)
      (fun _ _ h => eval_c96_congr (eval_w288_congr h 4) (eval_w288_congr h 5)
        (eval_w288_congr h 6))
      Ch32Canon.computableWitnesses env env'
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Maj32Canon.circuit input _ (offset + 32)
      (fun _ _ h => eval_c96_congr (eval_w288_congr h 0) (eval_w288_congr h 1)
        (eval_w288_congr h 2))
      Maj32Canon.computableWitnesses env env'
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Add32Canon.circuit input _ (offset + 32 + 32)
      (fun _ _ h => Add32.eval_mk_congr (eval_w288_congr h 7)
        (eval_upperSigma1E_congr (eval_w288_congr h 4)))
      Add32Canon.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 4) (eval_w288_congr h_input 5)
        (eval_w288_congr h_input 6))
    have ht1a := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    exact Add32.eval_mk_congr ht1a hch
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 4) (eval_w288_congr h_input 5)
        (eval_w288_congr h_input 6))
    have ht1a := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    exact Add32.eval_mk_congr ht1b (eval_constW_congr k)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 4) (eval_w288_congr h_input 5)
        (eval_w288_congr h_input 6))
    have ht1a := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    exact Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hmaj := Maj32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 0) (w288 input 1) (w288 input 2)) (offset + 32) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 0) (eval_w288_congr h_input 1)
        (eval_w288_congr h_input 2))
    exact Add32.eval_mk_congr (eval_upperSigma0E_congr (eval_w288_congr h_input 0)) hmaj
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 4) (eval_w288_congr h_input 5)
        (eval_w288_congr h_input 6))
    have ht1a := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    have ht1 := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8))
    exact Add32.eval_mk_congr (eval_w288_congr h_input 3) ht1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 4) (eval_w288_congr h_input 5)
        (eval_w288_congr h_input 6))
    have hmaj := Maj32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 0) (w288 input 1) (w288 input 2)) (offset + 32) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 0) (eval_w288_congr h_input 1)
        (eval_w288_congr h_input 2))
    have ht1a := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    have ht1 := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8))
    have ht2 := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr (eval_upperSigma0E_congr (eval_w288_congr h_input 0)) hmaj)
    exact Add32.eval_mk_congr ht1 ht2
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Pin32Canon.circuit input _ _ ?_ Pin32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 4) (eval_w288_congr h_input 5)
        (eval_w288_congr h_input 6))
    have hmaj := Maj32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 0) (w288 input 1) (w288 input 2)) (offset + 32) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 0) (eval_w288_congr h_input 1)
        (eval_w288_congr h_input 2))
    have ht1a := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    have ht1 := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8))
    have ht2 := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr (eval_upperSigma0E_congr (eval_w288_congr h_input 0)) hmaj)
    have han := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62 + 62 + 62 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1 ht2)
    exact han
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Pin32Canon.circuit input _ _ ?_ Pin32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32Canon.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
      (eval_c96_congr (eval_w288_congr h_input 4) (eval_w288_congr h_input 5)
        (eval_w288_congr h_input 6))
    have ht1a := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    have ht1 := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8))
    have hen := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 62 + 62 + 62 + 62 + 62) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 3) ht1)
    exact hen

theorem subcircuit_localLength (k : ℕ) (v : Var (fields 288) (F p2)) (m : ℕ) :
    (subcircuit (circuit k) v).localLength m = 562 := rfl

/-- The canonical round's output mixes the two pinned words (fresh witnesses at
relative offsets 498 and 530) with pass-through words of the input state. -/
theorem eval_subOut_of_agreesBelow (k : ℕ) (v : Var (fields 288) (F p2)) (n : ℕ) {kk : ℕ}
    (hk : n + 562 ≤ kk) {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow kk env') (h_input : eval env v = eval env' v) :
    eval env ((subcircuit (circuit k) v).output n)
      = eval env' ((subcircuit (circuit k) v).output n) := by
  have hout : (subcircuit (circuit k) v).output n
      = outState (varFromOffset (fields 32) (n + 498))
          (varFromOffset (fields 32) (n + 530)) v := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  rw [hout]
  exact eval_outState_congr
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    h_input

end ComputableWitness

end RoundCanon

end Solution.SHA256CompressGF2
