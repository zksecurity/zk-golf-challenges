import Solution.KangarooTwelveGF2.Round
import Solution.KangarooTwelveGF2.MainTheorems
import Solution.KangarooTwelveGF2.Cost

namespace Solution.KangarooTwelveGF2

open Challenge.Instances.KangarooTwelveGF2.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

@[reducible] def allocations : Nat := 19200

@[reducible] def constraints : Nat := 19200

def main (input : Var Input (F p2)) : Circuit (F p2) (Var Output (F p2)) := do
  let s0 ← Round.circuit (0 : Fin Specs.KangarooTwelve.rounds) input.state
  let s1 ← Round.circuit (1 : Fin Specs.KangarooTwelve.rounds) s0
  let s2 ← Round.circuit (2 : Fin Specs.KangarooTwelve.rounds) s1
  let s3 ← Round.circuit (3 : Fin Specs.KangarooTwelve.rounds) s2
  let s4 ← Round.circuit (4 : Fin Specs.KangarooTwelve.rounds) s3
  let s5 ← Round.circuit (5 : Fin Specs.KangarooTwelve.rounds) s4
  let s6 ← Round.circuit (6 : Fin Specs.KangarooTwelve.rounds) s5
  let s7 ← Round.circuit (7 : Fin Specs.KangarooTwelve.rounds) s6
  let s8 ← Round.circuit (8 : Fin Specs.KangarooTwelve.rounds) s7
  let s9 ← Round.circuit (9 : Fin Specs.KangarooTwelve.rounds) s8
  let s10 ← Round.circuit (10 : Fin Specs.KangarooTwelve.rounds) s9
  let s11 ← Round.circuit (11 : Fin Specs.KangarooTwelve.rounds) s10
  return { state := s11 }

instance elaborated : ElaboratedCircuit (F p2) Input Output main := by
  elaborate_circuit

theorem soundness : GeneralFormalCircuit.Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Round.circuit, Round.Assumptions, Round.Spec]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h_holds
  simp only [Specs.KangarooTwelve.keccakP1600_12]
  rw [h0] at h1
  rw [h1] at h2
  rw [h2] at h3
  rw [h3] at h4
  rw [h4] at h5
  rw [h5] at h6
  rw [h6] at h7
  rw [h7] at h8
  rw [h8] at h9
  rw [h9] at h10
  rw [h10] at h11
  exact h11

theorem completeness :
    GeneralFormalCircuit.Completeness (F p2) main ProverAssumptions ProverSpec := by
  circuit_proof_start
  simp only [Round.circuit, Round.Assumptions, and_self]

theorem mainCost :
    Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := by
  intro input
  exact
    (CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.bind (Cost.costIs_sub _ _) fun _ =>
      CostIs.pure _
        : CostIs (main input) (⟨1600, 1600⟩ + (⟨1600, 1600⟩ + (⟨1600, 1600⟩
            + (⟨1600, 1600⟩ + (⟨1600, 1600⟩ + (⟨1600, 1600⟩ + (⟨1600, 1600⟩
            + (⟨1600, 1600⟩ + (⟨1600, 1600⟩ + (⟨1600, 1600⟩ + (⟨1600, 1600⟩
            + (⟨1600, 1600⟩ + ⟨0, 0⟩)))))))))))))

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

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
      FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
      Circuit.pure_structuralComputableWitnesses_iff,
      Round.subcircuit_localLength,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
        (Round.circuit 0) input input.state n
        (fun e e' h => eval_input_state h)
        (Round.computableWitnesses 0) env env'
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 1) input _ _ ?_ (Round.computableWitnesses 1) env env'
      intro kk e e' hle h_agree h_input
      exact Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 2) input _ _ ?_ (Round.computableWitnesses 2) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      exact Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 3) input _ _ ?_ (Round.computableWitnesses 3) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      exact Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 4) input _ _ ?_ (Round.computableWitnesses 4) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      have h3 := Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
      exact Round.eval_subOut_of_agreesBelow 3 _ (n + 1600 + 1600 + 1600) (by omega) h_agree h3
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 5) input _ _ ?_ (Round.computableWitnesses 5) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      have h3 := Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
      have h4 := Round.eval_subOut_of_agreesBelow 3 _ (n + 1600 + 1600 + 1600) (by omega) h_agree h3
      exact Round.eval_subOut_of_agreesBelow 4 _ (n + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h4
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 6) input _ _ ?_ (Round.computableWitnesses 6) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      have h3 := Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
      have h4 := Round.eval_subOut_of_agreesBelow 3 _ (n + 1600 + 1600 + 1600) (by omega) h_agree h3
      have h5 := Round.eval_subOut_of_agreesBelow 4 _ (n + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h4
      exact Round.eval_subOut_of_agreesBelow 5 _ (n + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h5
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 7) input _ _ ?_ (Round.computableWitnesses 7) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      have h3 := Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
      have h4 := Round.eval_subOut_of_agreesBelow 3 _ (n + 1600 + 1600 + 1600) (by omega) h_agree h3
      have h5 := Round.eval_subOut_of_agreesBelow 4 _ (n + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h4
      have h6 := Round.eval_subOut_of_agreesBelow 5 _ (n + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h5
      exact Round.eval_subOut_of_agreesBelow 6 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h6
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 8) input _ _ ?_ (Round.computableWitnesses 8) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      have h3 := Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
      have h4 := Round.eval_subOut_of_agreesBelow 3 _ (n + 1600 + 1600 + 1600) (by omega) h_agree h3
      have h5 := Round.eval_subOut_of_agreesBelow 4 _ (n + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h4
      have h6 := Round.eval_subOut_of_agreesBelow 5 _ (n + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h5
      have h7 := Round.eval_subOut_of_agreesBelow 6 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h6
      exact Round.eval_subOut_of_agreesBelow 7 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h7
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 9) input _ _ ?_ (Round.computableWitnesses 9) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      have h3 := Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
      have h4 := Round.eval_subOut_of_agreesBelow 3 _ (n + 1600 + 1600 + 1600) (by omega) h_agree h3
      have h5 := Round.eval_subOut_of_agreesBelow 4 _ (n + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h4
      have h6 := Round.eval_subOut_of_agreesBelow 5 _ (n + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h5
      have h7 := Round.eval_subOut_of_agreesBelow 6 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h6
      have h8 := Round.eval_subOut_of_agreesBelow 7 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h7
      exact Round.eval_subOut_of_agreesBelow 8 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h8
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 10) input _ _ ?_ (Round.computableWitnesses 10) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      have h3 := Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
      have h4 := Round.eval_subOut_of_agreesBelow 3 _ (n + 1600 + 1600 + 1600) (by omega) h_agree h3
      have h5 := Round.eval_subOut_of_agreesBelow 4 _ (n + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h4
      have h6 := Round.eval_subOut_of_agreesBelow 5 _ (n + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h5
      have h7 := Round.eval_subOut_of_agreesBelow 6 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h6
      have h8 := Round.eval_subOut_of_agreesBelow 7 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h7
      have h9 := Round.eval_subOut_of_agreesBelow 8 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h8
      exact Round.eval_subOut_of_agreesBelow 9 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h9
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (Round.circuit 11) input _ _ ?_ (Round.computableWitnesses 11) env env'
      intro kk e e' hle h_agree h_input
      have h1 := Round.eval_subOut_of_agreesBelow 0 input.state n (by omega) h_agree
        (eval_input_state h_input)
      have h2 := Round.eval_subOut_of_agreesBelow 1 _ (n + 1600) (by omega) h_agree h1
      have h3 := Round.eval_subOut_of_agreesBelow 2 _ (n + 1600 + 1600) (by omega) h_agree h2
      have h4 := Round.eval_subOut_of_agreesBelow 3 _ (n + 1600 + 1600 + 1600) (by omega) h_agree h3
      have h5 := Round.eval_subOut_of_agreesBelow 4 _ (n + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h4
      have h6 := Round.eval_subOut_of_agreesBelow 5 _ (n + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h5
      have h7 := Round.eval_subOut_of_agreesBelow 6 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h6
      have h8 := Round.eval_subOut_of_agreesBelow 7 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h7
      have h9 := Round.eval_subOut_of_agreesBelow 8 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h8
      have h10 := Round.eval_subOut_of_agreesBelow 9 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h9
      exact Round.eval_subOut_of_agreesBelow 10 _ (n + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600 + 1600) (by omega) h_agree h10
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

set_option maxRecDepth 8000 in
theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main :=
  isR1CS_Cidentity_of_IsCidCirc
  (fun input hinput => by
    have hs0 : AffineW input.state := Cost.affineW_input_state hinput
    unfold main
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs0) (Cost.balanced_sub _ _) fun n0 => ?_
    have hs1 := Cost.affineW_subOut (0 : Fin Specs.KangarooTwelve.rounds) _ hs0 n0
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs1) (Cost.balanced_sub _ _) fun n1 => ?_
    have hs2 := Cost.affineW_subOut (1 : Fin Specs.KangarooTwelve.rounds) _ hs1 n1
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs2) (Cost.balanced_sub _ _) fun n2 => ?_
    have hs3 := Cost.affineW_subOut (2 : Fin Specs.KangarooTwelve.rounds) _ hs2 n2
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs3) (Cost.balanced_sub _ _) fun n3 => ?_
    have hs4 := Cost.affineW_subOut (3 : Fin Specs.KangarooTwelve.rounds) _ hs3 n3
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs4) (Cost.balanced_sub _ _) fun n4 => ?_
    have hs5 := Cost.affineW_subOut (4 : Fin Specs.KangarooTwelve.rounds) _ hs4 n4
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs5) (Cost.balanced_sub _ _) fun n5 => ?_
    have hs6 := Cost.affineW_subOut (5 : Fin Specs.KangarooTwelve.rounds) _ hs5 n5
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs6) (Cost.balanced_sub _ _) fun n6 => ?_
    have hs7 := Cost.affineW_subOut (6 : Fin Specs.KangarooTwelve.rounds) _ hs6 n6
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs7) (Cost.balanced_sub _ _) fun n7 => ?_
    have hs8 := Cost.affineW_subOut (7 : Fin Specs.KangarooTwelve.rounds) _ hs7 n7
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs8) (Cost.balanced_sub _ _) fun n8 => ?_
    have hs9 := Cost.affineW_subOut (8 : Fin Specs.KangarooTwelve.rounds) _ hs8 n8
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs9) (Cost.balanced_sub _ _) fun n9 => ?_
    have hs10 := Cost.affineW_subOut (9 : Fin Specs.KangarooTwelve.rounds) _ hs9 n9
    refine IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hs10) (Cost.balanced_sub _ _) fun n10 => ?_
    have hs11 := Cost.affineW_subOut (10 : Fin Specs.KangarooTwelve.rounds) _ hs10 n10
    refine IsCidCirc.bind (Cost.isCidentity_sub _ _ hs11) (Cost.balanced_sub _ _) fun _ => ?_
    exact IsCidCirc.pure _)
  (fun input hinput n => by
    intro i hi
    have houtput : AffineW ((main input).output n).state := by
      have hs0 : AffineW input.state := Cost.affineW_input_state hinput
      simp only [main, Circuit.bind_output_eq, Circuit.pure_output_eq]
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      apply Cost.affineW_subOut
      exact hs0
    have hiState : i < permutationBits := by
      have hsz : size Output = permutationBits := rfl
      omega
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using
      houtput i hiState)

end Solution.KangarooTwelveGF2
