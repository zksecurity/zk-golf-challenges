import Challenge.Specs.Bls12381G1
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS
import Challenge.Utils.WitgenIR
import Challenge.Instances.Bls12381G1ScalarMulFixedBase.Interface
import Challenge.Instances.Bls12381G1ScalarMulFixedBase.Cost

/-!
Trusted statement template for the BLS12-381 G1 fixed-base
scalar-multiplication instance.

This file is the trusted boundary: it states, with `sorry` placeholders, the
declarations a solution must export. The comparator checks that the
submitted solution proves exactly these statements.
-/

namespace Solution.Bls12381G1ScalarMulFixedBase

open Challenge.Instances.Bls12381G1ScalarMulFixedBase.Interface

def main : Var Input (F circomPrime) → Circuit (F circomPrime) (Var Output (F circomPrime)) := sorry

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := sorry

theorem soundness : GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := sorry
theorem completeness : GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := sorry

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry
theorem isR1CS : Challenge.CostR1CS.isR1CS main := sorry
theorem witgenIsIR : Challenge.WitgenIR.witgenIsIR main := sorry

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry

theorem requirementsChannelsLawful : ∀ input offset,
  ((main input).operations offset).RequirementsChannelsLawful
    elaborated.channelsWithGuarantees [] := sorry

def formalCircuit : GeneralFormalCircuit (F circomPrime) Input Output :=
  {
    main := main
    requirementsChannelsLawful := requirementsChannelsLawful
    Assumptions := Assumptions
    Spec := Spec
    ProverAssumptions := ProverAssumptions
    ProverSpec := ProverSpec
    soundness := soundness
    completeness := completeness
  }

end Solution.Bls12381G1ScalarMulFixedBase
