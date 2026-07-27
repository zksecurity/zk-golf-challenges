import Solution.SHA256CompressGF2Canonical.Add32Canon
import Solution.SHA256CompressGF2.MainTheorems

/-!
# Top-level helper for the canonical `main`
-/

namespace Solution.SHA256CompressGF2Canonical

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS
open Solution.SHA256CompressGF2

/-- Explicit `ConstantLength` for the 8-add canonical feed-forward `mapFinRange`
    body (Add32Canon localLength is 62). -/
def feedConstantLength (input : Var Input (F p2)) (s4 : Var (fields 256) (F p2)) :
    Circuit.ConstantLength (fun i : Fin 8 => Add32Canon.circuit ⟨w256 input.h i.val, w256 s4 i.val⟩) where
  localLength := 62
  localLength_eq _ _ := by simp [circuit_norm, Add32Canon.circuit, Add32Canon.elaborated]

end Solution.SHA256CompressGF2Canonical
