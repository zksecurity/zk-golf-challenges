import Solution.Blake3CompressGF2Canonical.G

/-!
# BLAKE3 round

Each `ApplyG` call has an exact state-level specification. A round is therefore
just the eight assignments in the BLAKE3 definition.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.Instances.Blake3CompressGF2Canonical.Interface.Blake3Bits
open Challenge.F2Bits

namespace ApplyG

structure Inputs (F : Type) where
  state : State F
  mx : Word F
  my : Word F
deriving ProvableStruct

def main (a b c d : Fin 16) (input : Var Inputs (F p2)) :
    Circuit (F p2) (Var State (F p2)) := do
  let q ← G.circuit
    ⟨stateWord input.state a, stateWord input.state b,
      stateWord input.state c, stateWord input.state d, input.mx, input.my⟩
  PinStateCanon.circuit (writeQuad input.state a b c d q)

instance elaborated (a b c d : Fin 16) :
    ElaboratedCircuit (F p2) Inputs State (main a b c d) := by
  elaborate_circuit

def Assumptions (_ : Inputs (F p2)) : Prop := True

def Spec (a b c d : Fin 16) (input : Inputs (F p2)) (output : State (F p2)) : Prop :=
  output = g input.state a b c d input.mx input.my

theorem soundness (a b c d : Fin 16) :
    Soundness (F p2) (main a b c d) Assumptions (Spec a b c d) := by
  circuit_proof_start [main, Spec, G.circuit, G.Assumptions, G.Spec,
    PinStateCanon.circuit, PinStateCanon.Assumptions, PinStateCanon.Spec,
    eval_stateWord, eval_writeQuad]
  obtain ⟨hg, hpin⟩ := h_holds
  rw [hpin, hg]
  rfl

theorem completeness (a b c d : Fin 16) :
    Completeness (F p2) (main a b c d) Assumptions := by
  circuit_proof_start
  simp only [G.circuit, G.Assumptions,
    PinStateCanon.circuit, PinStateCanon.Assumptions, and_self]

def circuit (a b c d : Fin 16) : FormalCircuit (F p2) Inputs State :=
  { main := main a b c d
    elaborated := elaborated a b c d
    Assumptions
    Spec := Spec a b c d
    soundness := soundness a b c d
    completeness := completeness a b c d }

end ApplyG

namespace Round

structure Inputs (F : Type) where
  state : State F
  block : State F
deriving ProvableStruct

namespace Pair

def main
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (input : Var Round.Inputs (F p2)) :
    Circuit (F p2) (Var State (F p2)) := do
  let s0 ← ApplyG.circuit a0 b0 c0 d0
    ⟨input.state, stateWord input.block mx0, stateWord input.block my0⟩
  ApplyG.circuit a1 b1 c1 d1
    ⟨s0, stateWord input.block mx1, stateWord input.block my1⟩

instance elaborated
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16) :
    ElaboratedCircuit (F p2) Round.Inputs State
      (main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) := by
  elaborate_circuit

def Assumptions (_ : Round.Inputs (F p2)) : Prop := True

def Spec
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (input : Round.Inputs (F p2)) (output : State (F p2)) : Prop :=
  output = gPairState input.state input.block
    a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1

theorem soundness
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16) :
    Soundness (F p2) (main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1)
      Assumptions (Spec a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) := by
  circuit_proof_start [main, Spec, ApplyG.circuit, ApplyG.Assumptions,
    ApplyG.Spec, eval_stateWord]
  obtain ⟨h0, h1⟩ := h_holds
  rw [h0] at h1
  simpa only [gPairState] using h1

theorem completeness
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16) :
    Completeness (F p2) (main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1)
      Assumptions := by
  circuit_proof_start
  simp only [ApplyG.circuit, ApplyG.Assumptions, and_self]

def circuit
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16) :
    FormalCircuit (F p2) Round.Inputs State :=
  { main := main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1
    elaborated := elaborated a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1
    Assumptions
    Spec := Spec a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1
    soundness := soundness a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1
    completeness := completeness a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 }

end Pair

namespace Columns

def main (input : Var Round.Inputs (F p2)) :
    Circuit (F p2) (Var State (F p2)) := do
  let s01 ← Pair.circuit 0 4 8 12 0 1 1 5 9 13 2 3 input
  Pair.circuit 2 6 10 14 4 5 3 7 11 15 6 7 ⟨s01, input.block⟩

instance elaborated :
    ElaboratedCircuit (F p2) Round.Inputs State main := by
  elaborate_circuit

def Assumptions (_ : Round.Inputs (F p2)) : Prop := True

def Spec (input : Round.Inputs (F p2)) (output : State (F p2)) : Prop :=
  output =
    gPairState
      (gPairState input.state input.block 0 4 8 12 0 1 1 5 9 13 2 3)
      input.block 2 6 10 14 4 5 3 7 11 15 6 7

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, ApplyG.circuit, ApplyG.Assumptions,
    ApplyG.Spec, Pair.circuit, Pair.Assumptions, Pair.Spec, eval_stateWord]
  obtain ⟨h01, h23⟩ := h_holds
  simpa only [h01] using h23

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Pair.circuit, Pair.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Round.Inputs State :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Columns

namespace Diagonals

def main (input : Var Round.Inputs (F p2)) :
    Circuit (F p2) (Var State (F p2)) := do
  let s45 ← Pair.circuit 0 5 10 15 8 9 1 6 11 12 10 11 input
  Pair.circuit 2 7 8 13 12 13 3 4 9 14 14 15 ⟨s45, input.block⟩

instance elaborated :
    ElaboratedCircuit (F p2) Round.Inputs State main := by
  elaborate_circuit

def Assumptions (_ : Round.Inputs (F p2)) : Prop := True

def Spec (input : Round.Inputs (F p2)) (output : State (F p2)) : Prop :=
  output =
    gPairState
      (gPairState input.state input.block 0 5 10 15 8 9 1 6 11 12 10 11)
      input.block 2 7 8 13 12 13 3 4 9 14 14 15

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Pair.circuit, Pair.Assumptions, Pair.Spec,
    eval_stateWord]
  obtain ⟨h45, h67⟩ := h_holds
  simpa only [h45] using h67

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Pair.circuit, Pair.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Round.Inputs State :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Diagonals

def main (input : Var Inputs (F p2)) :
    Circuit (F p2) (Var State (F p2)) := do
  let columns ← Columns.circuit input
  Diagonals.circuit ⟨columns, input.block⟩

instance elaborated :
    ElaboratedCircuit (F p2) Inputs State main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F p2)) : Prop := True

def Spec (input : Inputs (F p2)) (output : State (F p2)) : Prop :=
  output = roundState input.state input.block

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Columns.circuit, Columns.Assumptions, Columns.Spec,
    Diagonals.circuit, Diagonals.Assumptions, Diagonals.Spec]
  obtain ⟨hcolumns, hdiagonals⟩ := h_holds
  simpa only [roundState, hcolumns] using hdiagonals

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Columns.circuit, Columns.Assumptions,
    Diagonals.circuit, Diagonals.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Inputs State :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Round
end Solution.Blake3CompressGF2Canonical
