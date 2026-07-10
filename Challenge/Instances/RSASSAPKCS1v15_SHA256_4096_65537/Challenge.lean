import Challenge.Specs.RSASSAPKCS1v15
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS
import Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
import Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Cost


/-!
Trusted challenge statements for the RSASSA-PKCS1-v1_5/SHA256/4096/e=65537 instance.

This file is the trusted boundary: it owns the input/output type and the
statements the implementation must prove. The implementation may be arbitrary,
but its exported proofs must have exactly these types.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface

def main : Var Input (F circomPrime) → Circuit (F circomPrime) (Var Output (F circomPrime)) := sorry

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := sorry

theorem soundness : GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := sorry
theorem completeness : GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := sorry

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry
theorem isR1CS : Challenge.CostR1CS.isR1CS main := sorry

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry

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

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
