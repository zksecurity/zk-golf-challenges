import Solution.Blake3CompressGF2Canonical.PureEval

/-!
# Simple canonical BLAKE3 compression reference

The reference pins both the 512-bit state and the 512-bit permuted message at
every round boundary. This is intentionally not cost-optimized; it keeps all
correctness and witness-computability arguments local and compositional.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.Instances.Blake3CompressGF2Canonical.Interface.Blake3Bits
open Challenge.F2Bits

namespace Prepare

def main (input : Var Input (F p2)) :
    Circuit (F p2) (Var Config (F p2)) := do
  let words := splitWords 28 input.bits
  let state ← PinStateCanon.circuit (initialState words)
  let block ← PinStateCanon.circuit (initialBlock words)
  return ⟨state, block⟩

instance elaborated :
    ElaboratedCircuit (F p2) Input Config main := by
  elaborate_circuit

def Assumptions (_ : Input (F p2)) : Prop := True

def Spec (input : Input (F p2)) (output : Config (F p2)) : Prop :=
  let words := splitWords 28 input.bits
  output = ⟨initialState words, initialBlock words⟩

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, PinStateCanon.circuit,
    PinStateCanon.Assumptions, PinStateCanon.Spec,
    eval_splitWords, eval_initialState, eval_initialBlock]
  obtain ⟨hstate, hblock⟩ := h_holds
  rw [hstate, hblock]

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [PinStateCanon.circuit, PinStateCanon.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Input Config :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Prepare

namespace Step

def main (input : Var Config (F p2)) :
    Circuit (F p2) (Var Config (F p2)) := do
  let state ← Round.circuit ⟨input.state, input.block⟩
  let block ← PinStateCanon.circuit (permuteState input.block)
  return ⟨state, block⟩

instance elaborated :
    ElaboratedCircuit (F p2) Config Config main := by
  elaborate_circuit

def Assumptions (_ : Config (F p2)) : Prop := True

def Spec (input output : Config (F p2)) : Prop :=
  output = stepConfig input

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Round.circuit, Round.Assumptions, Round.Spec,
    PinStateCanon.circuit, PinStateCanon.Assumptions, PinStateCanon.Spec,
    eval_permuteState]
  obtain ⟨hstate, hblock⟩ := h_holds
  rw [hstate, hblock]
  rfl

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Round.circuit, Round.Assumptions,
    PinStateCanon.circuit, PinStateCanon.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Config Config :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Step

namespace Steps2

def main (input : Var Config (F p2)) :
    Circuit (F p2) (Var Config (F p2)) := do
  let x1 ← Step.circuit input
  Step.circuit x1

instance elaborated :
    ElaboratedCircuit (F p2) Config Config main := by
  elaborate_circuit

def Assumptions (_ : Config (F p2)) : Prop := True

def Spec (input output : Config (F p2)) : Prop :=
  output = Blake3Bits.steps2 input

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Step.circuit, Step.Assumptions, Step.Spec]
  obtain ⟨h1, h2⟩ := h_holds
  simpa only [Blake3Bits.steps2, h1] using h2

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Step.circuit, Step.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Config Config :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Steps2

namespace Steps4

def main (input : Var Config (F p2)) :
    Circuit (F p2) (Var Config (F p2)) := do
  let x2 ← Steps2.circuit input
  Steps2.circuit x2

instance elaborated :
    ElaboratedCircuit (F p2) Config Config main := by
  elaborate_circuit

def Assumptions (_ : Config (F p2)) : Prop := True

def Spec (input output : Config (F p2)) : Prop :=
  output = Blake3Bits.steps4 input

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Steps2.circuit, Steps2.Assumptions, Steps2.Spec]
  obtain ⟨h2, h4⟩ := h_holds
  simpa only [Blake3Bits.steps4, h2] using h4

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Steps2.circuit, Steps2.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Config Config :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Steps4

namespace Steps7

def main (input : Var Config (F p2)) :
    Circuit (F p2) (Var Config (F p2)) := do
  let x4 ← Steps4.circuit input
  let x6 ← Steps2.circuit x4
  Step.circuit x6

instance elaborated :
    ElaboratedCircuit (F p2) Config Config main := by
  elaborate_circuit

def Assumptions (_ : Config (F p2)) : Prop := True

def Spec (input output : Config (F p2)) : Prop :=
  output = Blake3Bits.steps7 input

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Steps4.circuit, Steps4.Assumptions, Steps4.Spec,
    Steps2.circuit, Steps2.Assumptions, Steps2.Spec,
    Step.circuit, Step.Assumptions, Step.Spec]
  obtain ⟨h4, h6, h7⟩ := h_holds
  rw [h4] at h6
  rw [h6] at h7
  exact h7

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Steps4.circuit, Steps4.Assumptions,
    Steps2.circuit, Steps2.Assumptions,
    Step.circuit, Step.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Config Config :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Steps7

namespace Finalize

structure Inputs (F : Type) where
  state : State F
  initial : State F
deriving ProvableStruct

def main (input : Var Inputs (F p2)) :
    Circuit (F p2) (Var State (F p2)) :=
  PinStateCanon.circuit (finalizeState input.state input.initial)

instance elaborated :
    ElaboratedCircuit (F p2) Inputs State main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F p2)) : Prop := True

def Spec (input : Inputs (F p2)) (output : State (F p2)) : Prop :=
  output = finalizeState input.state input.initial

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, PinStateCanon.circuit,
    PinStateCanon.Assumptions, PinStateCanon.Spec, eval_finalizeState]
  exact h_holds

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [PinStateCanon.circuit, PinStateCanon.Assumptions]

def circuit : FormalCircuit (F p2) Inputs State :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Finalize

def main (input : Var Input (F p2)) :
    Circuit (F p2) (Var Output (F p2)) := do
  let prepared ← Prepare.circuit input
  let result ← Steps7.circuit prepared
  let output ← Finalize.circuit ⟨result.state, prepared.state⟩
  return ⟨output⟩

instance elaborated :
    ElaboratedCircuit (F p2) Input Output main := by
  elaborate_circuit

theorem soundness :
    GeneralFormalCircuit.Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Prepare.circuit, Prepare.Assumptions, Prepare.Spec,
    Steps7.circuit, Steps7.Assumptions, Steps7.Spec,
    Finalize.circuit, Finalize.Assumptions, Finalize.Spec]
  obtain ⟨hprepare, hsteps, hfinal⟩ := h_holds
  rw [hprepare] at hsteps
  have hresult := congrArg Config.state hsteps
  have hinitial := congrArg Config.state hprepare
  dsimp only at hresult hinitial
  rw [hresult, hinitial] at hfinal
  simpa only [Blake3Bits.compress, Blake3Bits.compressState] using hfinal

theorem completeness :
    GeneralFormalCircuit.Completeness (F p2) main ProverAssumptions ProverSpec := by
  circuit_proof_start
  simp only [Prepare.circuit, Prepare.Assumptions,
    Steps7.circuit, Steps7.Assumptions,
    Finalize.circuit, Finalize.Assumptions, true_and]

end Solution.Blake3CompressGF2Canonical
