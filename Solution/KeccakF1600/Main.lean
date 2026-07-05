import Challenge.Instances.KeccakF1600.Interface
import Solution.KeccakF1600.KeccakRound
import Solution.KeccakF1600.MainTheorems
import Solution.KeccakF1600.Cost
import Solution.KeccakF1600.Permutation
import Solution.KeccakF1600.PermutationCost
import Challenge.Utils.CostR1CS

namespace Solution.KeccakF1600

open Challenge.Instances.KeccakF1600.Interface


section

def main (input : Var Input (F circomPrime)) : Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  let state ← Permutation.circuit (toLanes input.state)
  return { state := fromLanes state }

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := by
  elaborate_circuit

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Permutation.circuit, Permutation.Assumptions, Permutation.Spec]
  have h_bits : ∀ i : Fin 1600, (input_state[i.val] : F circomPrime).val < 2 := by
    intro i
    have := h_assumptions i
    simpa [fieldElemsToNat, Vector.getElem_map] using this
  have init_norm :
      StateNormalized (Vector.map (Vector.map (Expression.eval env)) (toLanes input_var_state)) := by
    rw [eval_toLanes_vec, h_input]
    exact StateNormalized_toLanes input_state fun i => h_bits i
  have init_val :
      stateValue (Vector.map (Vector.map (Expression.eval env)) (toLanes input_var_state)) =
        Specs.Keccak.bitsToState (fieldElemsToNat input_state) := by
    rw [eval_toLanes_vec, h_input, stateValue_toLanes]
    rfl
  rw [eval_keccakState, eval_keccakState] at h_holds
  obtain ⟨out_norm, out_val⟩ := h_holds init_norm
  rw [init_val] at out_val
  show fieldElemsToNat _ = Specs.Keccak.keccakF1600 (fieldElemsToNat input_state)
  unfold Specs.Keccak.keccakF1600
  show Vector.map ZMod.val (Vector.map (Expression.eval env) (fromLanes _)) = _
  rw [eval_fromLanes_vec, fieldElems_fromLanes _ out_norm, out_val]

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := by
  circuit_proof_start [Permutation.circuit, Permutation.Assumptions, Permutation.Spec]
  have h_bits : ∀ i : Fin 1600, (input_state[i.val] : F circomPrime).val < 2 := by
    intro i
    have := h_assumptions i
    simpa [fieldElemsToNat, Vector.getElem_map] using this
  have init_norm :
      StateNormalized (Vector.map (Vector.map (Expression.eval env.toEnvironment))
        (toLanes input_var_state)) := by
    rw [eval_toLanes_vec, h_input]
    exact StateNormalized_toLanes input_state fun i => h_bits i
  rw [eval_keccakState]
  exact init_norm

end

section
open Challenge.CostR1CS
open Solution.KeccakF1600.Cost

-- `maxRecDepth` controls elaboration stack depth only (not the trusted base and
-- not the heartbeat budget); the deep `do`-block here needs more than the default.
set_option maxRecDepth 8000

-- Keep the trusted R1CS predicates opaque while *applying* the per-gadget
-- certificates (see `Cost.lean`).
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

@[reducible] def allocations : Nat := 153600
@[reducible] def constraints : Nat := 153600

theorem costIs_sub_permutation (b : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit Permutation.circuit b) ⟨153600, 153600⟩ :=
  CostIs.subcircuit (fun n => Permutation.costIs b n)

theorem mainCost :
    circuitCost main ⟨allocations, constraints⟩ :=
  fun input =>
  (CostIs.bind (costIs_sub_permutation _) fun _ => CostIs.pure _
    : CostIs (main input) ⟨allocations, constraints⟩)

theorem r1cs_sub_permutation (b : Var KeccakBitState (F circomPrime)) (hb : StateAffine b) :
    IsR1CSCirc (subcircuit Permutation.circuit b) :=
  IsR1CSCirc.subcircuit (Permutation.r1cs b hb)

/-- The permutation subcircuit output (ι of the last χ-output witness) is affine. -/
theorem stateAffine_subOut_permutation (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    StateAffine ((subcircuit Permutation.circuit b).output n) := by
  rw [show (subcircuit Permutation.circuit b).output n = Permutation.stateVar n 23 from rfl,
    Permutation.stateVar]
  apply stateAffine_iotaWire
  intro j hj i hi
  rw [Vector.getElem_mapFinRange, Vector.getElem_mapRange]
  exact Affine.var _

theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
  (fun input hinput => by
    have hbits : ∀ i (hi : i < 1600), Affine (input.state[i]'hi) := by
      intro i hi
      have hsz : size Input = 1600 := rfl
      simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using
        hinput i (by omega)
    have h0 : StateAffine (toLanes input.state) := stateAffine_toLanes hbits
    exact IsR1CSCirc.bind_out (r1cs_sub_permutation _ h0) fun _ => IsR1CSCirc.pure _)
  (fun input hinput => by
    intro n i hi
    have hi1600 : i < 1600 := by
      have hsz : size Output = 1600 := rfl
      omega
    change Affine (((main input).output n).state[i]'hi1600)
    exact affine_fromLanes (stateAffine_subOut_permutation _ _) i hi1600)

end

end Solution.KeccakF1600
