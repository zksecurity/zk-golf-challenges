import Challenge.Instances.AssertBytes.Interface
import Solution.AssertBytes.Num2Bits
import Solution.AssertBytes.Cost
import Challenge.Utils.CostR1CS

/-!
# Baseline `AssertBytes` solution

The top-level circuit byte-checks every element of a 16-element buffer by applying
the `Num2Bits 8` gadget (an inlined, lookup-free, R1CS bit-decomposition range
check, defined from circuit primitives in `Num2Bits.lean`) to each element. There
are no soundness assumptions: the circuit itself constrains each element to be a
byte. Completeness needs the honest prover to actually hold bytes
(`ProverAssumptions`), so the witnessed bit decomposition exists.
-/

namespace Solution.AssertBytes

open Challenge.Instances.AssertBytes.Interface
open Challenge.CostR1CS

section

def main (input : Var Input (F circomPrime)) : Circuit (F circomPrime) (Var Output (F circomPrime)) :=
  Circuit.forEach input.buffer (fun x => Num2Bits.circuit 8 x)

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := by
  elaborate_circuit

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Num2Bits.circuit, Num2Bits.Spec, Num2Bits.Assumptions]
  intro i
  rw [← h_input, Vector.getElem_map]
  exact h_holds i

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := by
  circuit_proof_start [main, ProverAssumptions, ProverSpec, Num2Bits.circuit, Num2Bits.Spec,
    Num2Bits.Assumptions]
  intro i
  have := h_assumptions i
  rwa [← h_input, Vector.getElem_map] at this

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := by
  intro n input hinput env env'
  change (main input).operations n |>.forAllFlat n
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  have hstruct :
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        input env env' n ((main input).operations n) := by
    unfold main
    simp only [
      Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff]
    intro i
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_of_condition
      (Num2Bits.circuit 8) input (input.buffer[i.val]) _
      (by
        intro k e1 e2 _ _ h_input
        have h_buffer : (eval e1 input).buffer[i.val] = (eval e2 input).buffer[i.val] := by
          rw [h_input]
        simpa [circuit_norm] using h_buffer)
      (Num2Bits.computableWitnesses 8) env env'
  -- bridge the structural condition to the target `forAllFlat`, using `hinput`
  have hflat :=
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
      input env env' hstruct
  unfold Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition at hflat
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  let targetCondition : Condition (F circomPrime) :=
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  apply FlatOperation.forAll_implies (F := F circomPrime) n ?_ hflat
  have himplies : ∀ (ops : List (FlatOperation (F circomPrime))) (off : ℕ),
      n ≤ off →
      FlatOperation.forAll off
        (Condition.implies
          (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
            input env env')
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

end

section
open Solution.AssertBytes.Cost

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

@[reducible] def allocations : Nat := 128
@[reducible] def constraints : Nat := 144

theorem affineW_input_buffer (input : Var Input (F circomPrime)) (hinput : AffineProvable input) :
    AffineW input.buffer := by
  intro i hi
  simpa [AffineProvable] using hinput i hi

theorem mainCost :
    circuitCost main ⟨allocations, constraints⟩ :=
  fun input =>
    show CostIs (main input) ⟨allocations, constraints⟩ from
      CostIs.forEach (fun a n => costIs_assertion_num2Bits 8 a n)

theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
  (fun input hinput =>
    (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
      fun i n => isR1CS_assertion_num2Bits 8 _ (affineW_input_buffer input hinput i.val i.isLt) n))
  (fun _ _ => affineOutput_unit _)

end

end Solution.AssertBytes
