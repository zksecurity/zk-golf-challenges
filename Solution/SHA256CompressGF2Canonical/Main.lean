import Solution.SHA256CompressGF2Canonical.Cost
import Solution.SHA256CompressGF2Canonical.MainTheorems

/-!
# Canonical (C = identity) reference solution for `gf2-sha256-compress-canonical`

Built from the shared SHA-256 gadget layer, with every constraint row's C-side
being a single fresh witness variable (identity C). 3 `Sched16Canon` (3,488) +
4 `Rounds16Canon` (9,248) + 8 feed-forward `Add32Canon` (62) = **47,952**.
Soundness/completeness/cost are machine-checked as before; `isR1CS_Cidentity`
certifies the identity-C shape.
-/

namespace Solution.SHA256CompressGF2Canonical

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS
open Solution.SHA256CompressGF2

@[reducible] def allocations : Nat := 47952

@[reducible] def constraints : Nat := 47952

def main (input : Var Input (F p2)) : Circuit (F p2) (Var Output (F p2)) := do
  let wb1 ← Sched16Canon.circuit input.m
  let wb2 ← Sched16Canon.circuit wb1
  let wb3 ← Sched16Canon.circuit wb2
  let s1 ← Rounds16Canon.circuit 0 (c768 input.h input.m)
  let s2 ← Rounds16Canon.circuit 16 (c768 s1 wb1)
  let s3 ← Rounds16Canon.circuit 32 (c768 s2 wb2)
  let s4 ← Rounds16Canon.circuit 48 (c768 s3 wb3)
  let outs ← Circuit.mapFinRange 8 (fun i : Fin 8 => Add32Canon.circuit ⟨w256 input.h i.val, w256 s4 i.val⟩)
    (feedConstantLength input s4)
  return { h := out256 outs[0] outs[1] outs[2] outs[3] outs[4] outs[5] outs[6] outs[7] }

instance elaborated : ElaboratedCircuit (F p2) Input Output main := by
  elaborate_circuit

theorem soundness : GeneralFormalCircuit.Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Sched16Canon.circuit, Sched16Canon.Assumptions, Sched16Canon.Spec,
    Rounds16Canon.circuit, Rounds16Canon.Assumptions, Rounds16Canon.Spec, Add32Canon.circuit, Add32.Assumptions, Add32.Spec]
  obtain ⟨hhIn, hmIn⟩ := h_input
  obtain ⟨hsc1, hsc2, hsc3, hrd1, hrd2, hrd3, hrd4, hadd⟩ := h_holds
  set block := toWords 32 16 input_m with hblock
  set hIn8 := toWords 32 8 input_h with hhIn8
  have hw1 : PureSchedule.extend16 block = PureSchedule.window block 1 := by
    have h := PureSchedule.extend16_window block 0 (by omega)
    rwa [PureSchedule.window_zero] at h
  have hw2 : PureSchedule.extend16 (PureSchedule.window block 1) = PureSchedule.window block 2 :=
    PureSchedule.extend16_window block 1 (by omega)
  have hw3 : PureSchedule.extend16 (PureSchedule.window block 2) = PureSchedule.window block 3 :=
    PureSchedule.extend16_window block 2 (by omega)
  rw [hw1] at hsc1
  rw [hsc1, hw2] at hsc2
  rw [hsc2, hw3] at hsc3
  rw [ofFn_wordAt_c768_sched env input_var_h input_var_m,
      ofFn_wordAt_c768_state env input_var_h input_var_m, hmIn, hhIn] at hrd1
  rw [ofFn_wordAt_c768_sched env _ _, ofFn_wordAt_c768_state env _ _, hsc1, hrd1] at hrd2
  rw [ofFn_wordAt_c768_sched env _ _, ofFn_wordAt_c768_state env _ _, hsc2, hrd2] at hrd3
  rw [ofFn_wordAt_c768_sched env _ _, ofFn_wordAt_c768_state env _ _, hsc3, hrd3] at hrd4
  have hwin : ∀ k, PureRounds.win64 (PureSchedule.valSchedule block 48) k = PureSchedule.window block k :=
    fun k => rfl
  have hS4' : Specs.SHA256.sha256Compress hIn8 (Specs.SHA256.messageSchedule block)
      = PureRounds.applyRounds16 48 (PureSchedule.window block 3)
          (PureRounds.applyRounds16 32 (PureSchedule.window block 2)
            (PureRounds.applyRounds16 16 (PureSchedule.window block 1)
              (PureRounds.applyRounds16 0 block hIn8))) := by
    rw [PureRounds.sha256Compress_split, PureSchedule.messageSchedule_eq,
      hwin 0, hwin 1, hwin 2, hwin 3, PureSchedule.window_zero]
  have hS4 := hrd4.trans hS4'.symm
  rw [Specs.SHA256.compressBlock, ← hS4]
  refine Vector.ext fun k hk => ?_
  rw [Vector.getElem_mapFinRange, hhIn8]
  simp only [toWords_getElem]
  interval_cases k
  · rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 0 (by norm_num)]
    simp only [o8sel]
    have hk := hadd 0
    rw [show ((0 : Fin 8) : ℕ) = 0 from rfl] at hk
    rw [hk, toNat_eval_w256 env input_var_h 0 (by norm_num),
      toNat_eval_w256 env _ 0 (by norm_num), hhIn]
    simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 1 (by norm_num)]
    simp only [o8sel]
    have hk := hadd 1
    rw [show ((1 : Fin 8) : ℕ) = 1 from rfl] at hk
    rw [hk, toNat_eval_w256 env input_var_h 1 (by norm_num),
      toNat_eval_w256 env _ 1 (by norm_num), hhIn]
    simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 2 (by norm_num)]
    simp only [o8sel]
    have hk := hadd 2
    rw [show ((2 : Fin 8) : ℕ) = 2 from rfl] at hk
    rw [hk, toNat_eval_w256 env input_var_h 2 (by norm_num),
      toNat_eval_w256 env _ 2 (by norm_num), hhIn]
    simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 3 (by norm_num)]
    simp only [o8sel]
    have hk := hadd 3
    rw [show ((3 : Fin 8) : ℕ) = 3 from rfl] at hk
    rw [hk, toNat_eval_w256 env input_var_h 3 (by norm_num),
      toNat_eval_w256 env _ 3 (by norm_num), hhIn]
    simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 4 (by norm_num)]
    simp only [o8sel]
    have hk := hadd 4
    rw [show ((4 : Fin 8) : ℕ) = 4 from rfl] at hk
    rw [hk, toNat_eval_w256 env input_var_h 4 (by norm_num),
      toNat_eval_w256 env _ 4 (by norm_num), hhIn]
    simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 5 (by norm_num)]
    simp only [o8sel]
    have hk := hadd 5
    rw [show ((5 : Fin 8) : ℕ) = 5 from rfl] at hk
    rw [hk, toNat_eval_w256 env input_var_h 5 (by norm_num),
      toNat_eval_w256 env _ 5 (by norm_num), hhIn]
    simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 6 (by norm_num)]
    simp only [o8sel]
    have hk := hadd 6
    rw [show ((6 : Fin 8) : ℕ) = 6 from rfl] at hk
    rw [hk, toNat_eval_w256 env input_var_h 6 (by norm_num),
      toNat_eval_w256 env _ 6 (by norm_num), hhIn]
    simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 7 (by norm_num)]
    simp only [o8sel]
    have hk := hadd 7
    rw [show ((7 : Fin 8) : ℕ) = 7 from rfl] at hk
    rw [hk, toNat_eval_w256 env input_var_h 7 (by norm_num),
      toNat_eval_w256 env _ 7 (by norm_num), hhIn]
    simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]

theorem completeness : GeneralFormalCircuit.Completeness (F p2) main ProverAssumptions ProverSpec := by
  circuit_proof_start
  simp [Sched16Canon.circuit, Sched16Canon.Assumptions, Rounds16Canon.circuit, Rounds16Canon.Assumptions,
    Add32Canon.circuit, Add32.Assumptions]

theorem mainCost :
    Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := by
  intro input
  exact
    (CostIs.bind (Sched16Canon.costIs_sub _) fun _ =>
      CostIs.bind (Sched16Canon.costIs_sub _) fun _ =>
      CostIs.bind (Sched16Canon.costIs_sub _) fun _ =>
      CostIs.bind (Rounds16Canon.costIs_sub _ _) fun _ =>
      CostIs.bind (Rounds16Canon.costIs_sub _ _) fun _ =>
      CostIs.bind (Rounds16Canon.costIs_sub _ _) fun _ =>
      CostIs.bind (Rounds16Canon.costIs_sub _ _) fun _ =>
      CostIs.bind (CostIs.mapFinRange fun _ _ => Add32Canon.costIs_sub _ _) fun _ =>
      CostIs.pure _
        : CostIs (main input) ⟨allocations, constraints⟩)

-- `maxRecDepth` controls elaboration stack depth only (not the trusted kernel base
-- nor the heartbeat budget); the deep feed-forward `do`-block output needs more
-- than the default when certifying affinity of every offset.
set_option maxRecDepth 8000 in
theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main :=
  isR1CS_Cidentity_of_IsCidCirc
  (fun input hinput => by
    have hh : AffineW input.h := affineW_input_h hinput
    have hm : AffineW input.m := affineW_input_m hinput
    unfold main
    refine IsCidCirc.bind_out (Sched16Canon.isCidentity_sub _ hm)
      (Sched16Canon.balanced_sub _) fun m1 => ?_
    refine IsCidCirc.bind_out (Sched16Canon.isCidentity_sub _ (Sched16Canon.affineW_subOut _ m1))
      (Sched16Canon.balanced_sub _) fun m2 => ?_
    refine IsCidCirc.bind_out (Sched16Canon.isCidentity_sub _ (Sched16Canon.affineW_subOut _ m2))
      (Sched16Canon.balanced_sub _) fun m3 => ?_
    refine IsCidCirc.bind_out (Rounds16Canon.isCidentity_sub 0 _ (c768_affine hh hm))
      (Rounds16Canon.balanced_sub _ _) fun p1 => ?_
    refine IsCidCirc.bind_out (Rounds16Canon.isCidentity_sub 16 _ (c768_affine (Rounds16Canon.affineW_subOut 0 _ p1) (Sched16Canon.affineW_subOut _ m1)))
      (Rounds16Canon.balanced_sub _ _) fun p2 => ?_
    refine IsCidCirc.bind_out (Rounds16Canon.isCidentity_sub 32 _ (c768_affine (Rounds16Canon.affineW_subOut 16 _ p2) (Sched16Canon.affineW_subOut _ m2)))
      (Rounds16Canon.balanced_sub _ _) fun p3 => ?_
    refine IsCidCirc.bind_out (Rounds16Canon.isCidentity_sub 48 _ (c768_affine (Rounds16Canon.affineW_subOut 32 _ p3) (Sched16Canon.affineW_subOut _ m3)))
      (Rounds16Canon.balanced_sub _ _) fun p4 => ?_
    refine IsCidCirc.bind (IsCidCirc.mapFinRange (L := 62)
      (by simp [circuit_norm, Add32Canon.circuit, Add32Canon.elaborated])
      (fun i n => (Add32Canon.costIs_sub _).constraints n)
      (fun i => add32canon_cid _ _ (w256_affine hh i.val)
        (w256_affine (Rounds16Canon.affineW_subOut 48 _ p4) i.val)))
      ?_ fun _ => ?_
    · exact Balanced.of_costIs
        (CostIs.mapFinRange fun i n => Add32Canon.costIs_sub _ n)
        (fun n => by simp [circuit_norm, Add32Canon.circuit, Add32Canon.elaborated])
    · exact IsCidCirc.pure _)
  (fun input hinput n => by
    have hh : AffineW input.h := affineW_input_h hinput
    intro i hi
    have hi256 : i < 256 := by have hsz : size Output = 256 := rfl; omega
    simp only [main, Circuit.bind_output_eq, Circuit.pure_output_eq,
      Circuit.mapFinRange.output_eq, Vector.getElem_mapFinRange]
    exact out256_add32canon_affine hh (Rounds16Canon.affineW_subOut 48 _ _) _ _ _ _ _ _ _ _ i hi256)

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

-- Keep the unifier from expanding the 47,952-witness circuit while peeling the
-- top-level `do` block; offsets and outputs come from the `rfl` lemmas instead.
attribute [local irreducible] Sched16Canon.circuit Rounds16Canon.circuit
  Add32Canon.circuit main

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p2) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  intro n input hinput env env'
  change (main input).operations n |>.forAllFlat n
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  have hstruct : FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' n ((main input).operations n) := by
    unfold main
    simp only [
      Circuit.bind_structuralComputableWitnesses_iff,
      Circuit.mapFinRange_structuralComputableWitnesses_iff,
      FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
      Circuit.pure_structuralComputableWitnesses_iff,
      Sched16Canon.subcircuit_localLength, Rounds16Canon.subcircuit_localLength,
      Add32Canon.subcircuit_localLength,
      and_true]
    set wb1 := (subcircuit Sched16Canon.circuit input.m).output n with hwb1def
    set wb2 := (subcircuit Sched16Canon.circuit wb1).output (n + 3488) with hwb2def
    set wb3 := (subcircuit Sched16Canon.circuit wb2).output (n + 3488 + 3488) with hwb3def
    set s1 := (subcircuit (Rounds16Canon.circuit 0) (c768 input.h input.m)).output
      (n + 3488 + 3488 + 3488) with hs1def
    set s2 := (subcircuit (Rounds16Canon.circuit 16) (c768 s1 wb1)).output
      (n + 3488 + 3488 + 3488 + 9248) with hs2def
    set s3 := (subcircuit (Rounds16Canon.circuit 32) (c768 s2 wb2)).output
      (n + 3488 + 3488 + 3488 + 9248 + 9248) with hs3def
    set s4 := (subcircuit (Rounds16Canon.circuit 48) (c768 s3 wb3)).output
      (n + 3488 + 3488 + 3488 + 9248 + 9248 + 9248) with hs4def
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
        Sched16Canon.circuit input _ n (fun _ _ h => eval_input_m_congr h)
        Sched16Canon.computableWitnesses env env'
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        Sched16Canon.circuit input _ _ ?_ Sched16Canon.computableWitnesses env env'
      intro kk e e' hle h_agree h_input
      exact Sched16Canon.eval_subOut_of_agreesBelow input.m n (by omega) h_agree
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        Sched16Canon.circuit input _ _ ?_ Sched16Canon.computableWitnesses env env'
      intro kk e e' hle h_agree h_input
      exact Sched16Canon.eval_subOut_of_agreesBelow wb1 (n + 3488) (by omega) h_agree
    · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
        (Rounds16Canon.circuit 0) input _ _
        (fun _ _ h => eval_c768_congr (eval_input_h_congr h) (eval_input_m_congr h))
        (Rounds16Canon.computableWitnesses 0) env env'
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Rounds16Canon.circuit 16) input _ _ ?_ (Rounds16Canon.computableWitnesses 16) env env'
      intro kk e e' hle h_agree h_input
      exact eval_c768_congr
        (Rounds16Canon.eval_subOut_of_agreesBelow 0 (c768 input.h input.m) (n + 3488 + 3488 + 3488)
          (by omega) h_agree)
        (Sched16Canon.eval_subOut_of_agreesBelow input.m n (by omega) h_agree)
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Rounds16Canon.circuit 32) input _ _ ?_ (Rounds16Canon.computableWitnesses 32) env env'
      intro kk e e' hle h_agree h_input
      exact eval_c768_congr
        (Rounds16Canon.eval_subOut_of_agreesBelow 16 (c768 s1 wb1) (n + 3488 + 3488 + 3488 + 9248) (by omega) h_agree)
        (Sched16Canon.eval_subOut_of_agreesBelow wb1 (n + 3488) (by omega) h_agree)
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Rounds16Canon.circuit 48) input _ _ ?_ (Rounds16Canon.computableWitnesses 48) env env'
      intro kk e e' hle h_agree h_input
      exact eval_c768_congr
        (Rounds16Canon.eval_subOut_of_agreesBelow 32 (c768 s2 wb2) (n + 3488 + 3488 + 3488 + 9248 + 9248) (by omega) h_agree)
        (Sched16Canon.eval_subOut_of_agreesBelow wb2 (n + 3488 + 3488) (by omega) h_agree)
    · intro i
      refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
      intro kk e e' hle h_agree h_input
      exact Add32.eval_mk_congr (eval_w256_congr (eval_input_h_congr h_input) i.val)
        (eval_w256_congr
          (Rounds16Canon.eval_subOut_of_agreesBelow 48 (c768 s3 wb3) (n + 3488 + 3488 + 3488 + 9248 + 9248 + 9248)
            (by omega) h_agree) i.val)
  have hflat := FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
    input env env' hstruct
  unfold FormalCircuitBase.computableWitnessCondition at hflat
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  let targetCondition : Condition (F p2) :=
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  apply FlatOperation.forAll_implies (F := F p2) n ?_ hflat
  have himplies : ∀ (ops : List (FlatOperation (F p2))) (off : ℕ),
      n ≤ off →
      FlatOperation.forAll off
        (Condition.implies
          (FormalCircuitBase.computableWitnessCondition input env env')
          targetCondition).ignoreSubcircuit
        ops := by
    intro ops off hoff
    induction ops generalizing off with
    | nil => simp [FlatOperation.forAll]
    | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          constructor
          · intro hparent hagree
            exact hparent hagree
              (hinput env env' (ProverEnvironment.agreesBelow_of_le hagree hoff))
          · exact ih (m + off) (by omega)
      | assert e =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | lookup l =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | interact i =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
  exact himplies ((main input).operations n).toFlat n (le_refl n)

end ComputableWitness

end Solution.SHA256CompressGF2Canonical
