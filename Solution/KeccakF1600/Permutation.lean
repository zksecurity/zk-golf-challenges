import Solution.KeccakF1600.PermutationDefs
import Solution.KeccakF1600.PermutationSound
import Solution.KeccakF1600.PermutationComplete

namespace Solution.KeccakF1600.Permutation

open Challenge.Instances.KeccakF1600.Interface

set_option maxHeartbeats 1000000

/-- The Keccak-f[1600] permutation on the lane state as a `FormalCircuit`. -/
def circuit : FormalCircuit (F circomPrime) KeccakBitState KeccakBitState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  -- `soundness := soundness` / `completeness := completeness` trigger a `whnf`
  -- timeout while checking the term against the structure's `base.main`
  -- projection (the same quirk noted in clean's own Keccak Permutation); routing
  -- through `simp only` matches the goal syntactically and sidesteps it.
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]

end Solution.KeccakF1600.Permutation
