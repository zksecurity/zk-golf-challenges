import Challenge.Instances.AssertBytes.Interface
import Solution.AssertBytes.Num2Bits
import Solution.AssertBytes.Cost
import Challenge.Utils.CostR1CS

/-!
# Baseline `AssertBytes` solution

The top-level circuit byte-checks every element of a 16-element buffer by applying
the `Num2Bits 8` gadget (an inlined, lookup-free, R1CS bit-decomposition range
check, defined from circuit primitives in `Num2Bits.lean`) to each element. There
are no soundness assumptions: the circuit itself constrains each element to be a
byte. Completeness needs the honest prover to actually hold bytes
(`ProverAssumptions`), so the witnessed bit decomposition exists.
-/

namespace Solution.AssertBytes

open Challenge.Instances.AssertBytes.Interface
open Challenge.CostR1CS

section

def main (input : Var Input (F circomPrime)) : Circuit (F circomPrime) (Var Output (F circomPrime)) :=
  Circuit.forEach input.buffer (fun x => Num2Bits.circuit 8 x)

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := by
  elaborate_circuit

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Num2Bits.circuit, Num2Bits.Spec, Num2Bits.Assumptions]
  intro i
  rw [← h_input, Vector.getElem_map]
  exact h_holds i

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := by
  circuit_proof_start [main, ProverAssumptions, ProverSpec, Num2Bits.circuit, Num2Bits.Spec,
    Num2Bits.Assumptions]
  intro i
  have := h_assumptions i
  rwa [← h_input, Vector.getElem_map] at this

end

section
open Solution.AssertBytes.Cost

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

@[reducible] def allocations : Nat := 128
@[reducible] def constraints : Nat := 144

theorem affineW_input_buffer :
    AffineW ((varFromOffset Input 0 : Var Input (F circomPrime)).buffer) := by
  have heq : (varFromOffset Input 0 : Var Input (F circomPrime)).buffer
      = varFromOffset (fields bufferLen) 0 := by simp only [circuit_norm]
  rw [heq]; exact affineW_varFromOffset _ _

theorem mainCost :
    circuitCount (main default) = ⟨allocations, constraints⟩ :=
  circuitCount_eq_of_CostIs
    (show CostIs (main default) ⟨allocations, constraints⟩ from
      CostIs.forEach (fun a n => costIs_assertion_num2Bits 8 a n))

theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
    (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
      fun i n => isR1CS_assertion_num2Bits 8 _ (affineW_input_buffer i.val i.isLt) n)

end

end Solution.AssertBytes
