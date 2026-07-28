import Solution.Blake3CompressGF2Canonical.Witness

/-!
# BLAKE3 canonical reference entrypoint

This deeply composed reference groups its internal certificates by aspect:
`Circuit.lean`, `Cost.lean`, `Canonical.lean`, and `Witness.lean` contain the
supporting proofs, while this file is the small public checker entrypoint.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.F2Bits

@[reducible] def allocations : Nat := 86880

@[reducible] def constraints : Nat := 86880

theorem mainCost :
    Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := by
  simpa [allocations, constraints] using mainCostInternal

theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main :=
  isR1CS_CidentityInternal

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p2) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  computableWitnessInternal

end Solution.Blake3CompressGF2Canonical
