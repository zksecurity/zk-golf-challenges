import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CSCanonicalSpec
import Challenge.Instances.SHA256CompressGF2Canonical.Interface
import Challenge.Instances.SHA256CompressGF2Canonical.Cost

/-!
Contract file for the `gf2-sha256-compress-canonical` challenge. In addition to
the shared SHA-256 compression specification, the R1CS obligation is the strict
`isR1CS_Cidentity`: constraint row `t` must use exactly `var (n₀ + t)` as its
`C`-side. Bodies are `sorry`; the solution in
`Solution/SHA256CompressGF2Canonical/` proves these with no extra axioms.
-/

namespace Solution.SHA256CompressGF2Canonical

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits

def main : Var Input (F p2) → Circuit (F p2) (Var Output (F p2)) := sorry

instance elaborated : ElaboratedCircuit (F p2) Input Output main := sorry

theorem soundness : GeneralFormalCircuit.Soundness (F p2) main Assumptions Spec := sorry
theorem completeness : GeneralFormalCircuit.Completeness (F p2) main ProverAssumptions ProverSpec := sorry

theorem mainCost :
    Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry
theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main := sorry

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F p2) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry

end Solution.SHA256CompressGF2Canonical
