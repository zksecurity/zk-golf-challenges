import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS
import Challenge.Instances.AssertBytes.Interface
import Challenge.Instances.AssertBytes.Cost


/-!
Trusted statements for the `AssertBytes` instance.

This file pins the exact types the implementation must prove. The implementation
lives under `Solution.AssertBytes`; its exported declarations must match these
signatures. The `Cost` import supplies `allocations`/`constraints`, which the
checker overwrites with the solver's claimed cost.
-/

namespace Solution.AssertBytes

open Challenge.Instances.AssertBytes.Interface

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

end Solution.AssertBytes
