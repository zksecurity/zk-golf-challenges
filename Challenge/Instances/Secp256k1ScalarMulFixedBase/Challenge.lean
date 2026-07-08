import Challenge.Specs.Secp256k1
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS
import Challenge.Instances.Secp256k1ScalarMulFixedBase.Interface
import Challenge.Instances.Secp256k1ScalarMulFixedBase.Cost

/-!
Trusted statement template for the secp256k1 fixed-base scalar-multiplication
instance.

This file is the trusted boundary: it states, with `sorry` placeholders, the
declarations a solution must export. The comparator checks that the
submitted solution proves exactly these statements.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

open Challenge.Instances.Secp256k1ScalarMulFixedBase.Interface

def main : Var Input (F circomPrime) → Circuit (F circomPrime) (Var Output (F circomPrime)) := sorry

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := sorry

theorem soundness : GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := sorry
theorem completeness : GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := sorry

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry
theorem isR1CS : Challenge.CostR1CS.isR1CS main := sorry

def formalCircuit : GeneralFormalCircuit (F circomPrime) Input Output :=
  {
    main := main
    Assumptions := Assumptions
    Spec := Spec
    ProverAssumptions := ProverAssumptions
    ProverSpec := ProverSpec
    soundness := soundness
    completeness := completeness
  }

end Solution.Secp256k1ScalarMulFixedBase
