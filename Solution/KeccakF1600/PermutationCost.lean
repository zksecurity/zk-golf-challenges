import Solution.KeccakF1600.Permutation
import Solution.KeccakF1600.Cost

namespace Solution.KeccakF1600.Permutation

open Challenge.Instances.KeccakF1600.Interface
open Challenge.CostR1CS Solution.KeccakF1600.Cost

set_option maxHeartbeats 4000000

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- The permutation costs 24 rounds × 6400 = 153600 witnesses / constraints. -/
theorem costIs (state : Var KeccakBitState (F circomPrime)) :
    CostIs (main state) ⟨153600, 153600⟩ := by
  have h : CostIs (main state) ⟨24 * 6400, 24 * 6400⟩ :=
    CostIs.foldlRange (constant := foldConstant)
      (fun s i n => costIs_sub_round (rc i) (rc_lt i) s n)
  exact h

/-- Every assert in the permutation is a single R1CS row for affine input. -/
theorem r1cs (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (main state) :=
  IsR1CSCirc.foldlRange_inv (constant := foldConstant) StateAffine hs
    (fun s i hsa => r1cs_sub_round (rc i) (rc_lt i) s hsa)
    (fun s i n _ => stateAffine_subOut_round (rc i) (rc_lt i) s n)

end Solution.KeccakF1600.Permutation
