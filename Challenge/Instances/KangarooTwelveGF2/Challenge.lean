import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CSCanonicalSpec
import Challenge.Instances.KangarooTwelveGF2.Interface
import Challenge.Instances.KangarooTwelveGF2.Cost

namespace Solution.KangarooTwelveGF2

open Challenge.Instances.KangarooTwelveGF2.Interface
open Challenge.F2Bits

def main : Var Input (F p2) → Circuit (F p2) (Var Output (F p2)) := sorry

instance elaborated : ElaboratedCircuit (F p2) Input Output main := sorry

theorem soundness : GeneralFormalCircuit.Soundness (F p2) main Assumptions Spec := sorry
theorem completeness :
    GeneralFormalCircuit.Completeness (F p2) main ProverAssumptions ProverSpec := sorry

theorem mainCost :
    Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry
theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main := sorry

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F p2) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry

end Solution.KangarooTwelveGF2
