import Solution.Blake3CompressGF2Canonical.Theorems
import Solution.Blake3CompressGF2Canonical.PinCanon

/-!
# BLAKE3 `G` mixing function

This reference deliberately materializes every intermediate word. The extra
rows make every enclosing proof a short composition of exact word equalities.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.Instances.Blake3CompressGF2Canonical.Interface.Blake3Bits
open Challenge.F2Bits

structure GInputs (F : Type) where
  a : Word F
  b : Word F
  c : Word F
  d : Word F
  mx : Word F
  my : Word F
deriving ProvableStruct

def GInputs.quad {α : Type} (input : GInputs α) : Quad α :=
  ⟨input.a, input.b, input.c, input.d⟩

namespace AddExact

def main (input : Var Add32.Inputs (F p2)) :
    Circuit (F p2) (Var (fields 32) (F p2)) := do
  let sum ← Add32Canon.circuit input
  Pin32Canon.circuit sum

instance elaborated :
    ElaboratedCircuit (F p2) Add32.Inputs (fields 32) main := by
  elaborate_circuit

def Assumptions (_ : Add32.Inputs (F p2)) : Prop := True

def Spec (input : Add32.Inputs (F p2)) (output : Word (F p2)) : Prop :=
  output = addWord input.x input.y

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Add32Canon.circuit, Pin32Canon.circuit,
    Add32.Assumptions, Add32.Spec, Pin32Canon.Assumptions, Pin32Canon.Spec]
  obtain ⟨hx, hy⟩ := h_input
  obtain ⟨hadd, hpin⟩ := h_holds
  rw [hpin]
  apply toNat_injective
  rw [hadd, toNat_addWord]

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Add32Canon.circuit, Add32.Assumptions,
    Pin32Canon.circuit, Pin32Canon.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Add32.Inputs (fields 32) :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end AddExact

namespace XorRotateExact

structure Inputs (F : Type) where
  x : Word F
  y : Word F
deriving ProvableStruct

def main (n : ℕ) (input : Var Inputs (F p2)) :
    Circuit (F p2) (Var (fields 32) (F p2)) :=
  Pin32Canon.circuit (rotRight (xorWord input.x input.y) n)

instance elaborated (n : ℕ) :
    ElaboratedCircuit (F p2) Inputs (fields 32) (main n) := by
  elaborate_circuit

def Assumptions (_ : Inputs (F p2)) : Prop := True

def Spec (n : ℕ) (input : Inputs (F p2)) (output : Word (F p2)) : Prop :=
  output = rotRight (xorWord input.x input.y) n

theorem soundness (n : ℕ) :
    Soundness (F p2) (main n) Assumptions (Spec n) := by
  circuit_proof_start [main, Spec, Pin32Canon.circuit,
    Pin32Canon.Assumptions, Pin32Canon.Spec]
  obtain ⟨hx, hy⟩ := h_input
  rw [h_holds, eval_rotRight, eval_xorWord, hx, hy]

theorem completeness (n : ℕ) :
    Completeness (F p2) (main n) Assumptions := by
  circuit_proof_start
  simp only [Pin32Canon.circuit, Pin32Canon.Assumptions]

def circuit (n : ℕ) : FormalCircuit (F p2) Inputs (fields 32) :=
  { main := main n
    elaborated := elaborated n
    Assumptions
    Spec := Spec n
    soundness := soundness n
    completeness := completeness n }

end XorRotateExact

namespace PinQuadExact

def main (input : Var Quad (F p2)) :
    Circuit (F p2) (Var Quad (F p2)) := do
  let a ← Pin32Canon.circuit input.a
  let b ← Pin32Canon.circuit input.b
  let c ← Pin32Canon.circuit input.c
  let d ← Pin32Canon.circuit input.d
  return ⟨a, b, c, d⟩

instance elaborated :
    ElaboratedCircuit (F p2) Quad Quad main := by
  elaborate_circuit

def Assumptions (_ : Quad (F p2)) : Prop := True

def Spec (input output : Quad (F p2)) : Prop :=
  output = input

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, Pin32Canon.circuit,
    Pin32Canon.Assumptions, Pin32Canon.Spec]
  obtain ⟨ha, hb, hc, hd⟩ := h_holds
  rw [ha, hb, hc, hd]

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [Pin32Canon.circuit, Pin32Canon.Assumptions, and_self]

def circuit : FormalCircuit (F p2) Quad Quad :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end PinQuadExact

namespace GFirst

def main (input : Var GInputs (F p2)) :
    Circuit (F p2) (Var Quad (F p2)) := do
  let a0 ← AddExact.circuit ⟨input.a, input.b⟩
  let av ← AddExact.circuit ⟨a0, input.mx⟩
  let dv ← XorRotateExact.circuit 16 ⟨input.d, av⟩
  let cv ← AddExact.circuit ⟨input.c, dv⟩
  let bv ← XorRotateExact.circuit 12 ⟨input.b, cv⟩
  PinQuadExact.circuit ⟨av, bv, cv, dv⟩

instance elaborated :
    ElaboratedCircuit (F p2) GInputs Quad main := by
  elaborate_circuit

def Assumptions (_ : GInputs (F p2)) : Prop := True

def Spec (input : GInputs (F p2)) (output : Quad (F p2)) : Prop :=
  output = gFirstValues input.quad input.mx

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, AddExact.circuit, XorRotateExact.circuit,
    AddExact.Assumptions, AddExact.Spec,
    XorRotateExact.Assumptions, XorRotateExact.Spec,
    PinQuadExact.circuit, PinQuadExact.Assumptions, PinQuadExact.Spec]
  obtain ⟨ha0, hav, hdv, hcv, hbv, hpin⟩ := h_holds
  rw [ha0] at hav
  rw [hav] at hdv
  rw [hdv] at hcv
  rw [hcv] at hbv
  rw [hpin, hav, hbv, hcv, hdv]
  rfl

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [AddExact.circuit, AddExact.Assumptions,
    XorRotateExact.circuit, XorRotateExact.Assumptions,
    PinQuadExact.circuit, PinQuadExact.Assumptions, and_self]

def circuit : FormalCircuit (F p2) GInputs Quad :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end GFirst

namespace GSecond

def main (input : Var GInputs (F p2)) :
    Circuit (F p2) (Var Quad (F p2)) := do
  let a0 ← AddExact.circuit ⟨input.a, input.b⟩
  let av ← AddExact.circuit ⟨a0, input.my⟩
  let dv ← XorRotateExact.circuit 8 ⟨input.d, av⟩
  let cv ← AddExact.circuit ⟨input.c, dv⟩
  let bv ← XorRotateExact.circuit 7 ⟨input.b, cv⟩
  PinQuadExact.circuit ⟨av, bv, cv, dv⟩

instance elaborated :
    ElaboratedCircuit (F p2) GInputs Quad main := by
  elaborate_circuit

def Assumptions (_ : GInputs (F p2)) : Prop := True

def Spec (input : GInputs (F p2)) (output : Quad (F p2)) : Prop :=
  output = gSecondValues input.quad input.my

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, AddExact.circuit, XorRotateExact.circuit,
    AddExact.Assumptions, AddExact.Spec,
    XorRotateExact.Assumptions, XorRotateExact.Spec,
    PinQuadExact.circuit, PinQuadExact.Assumptions, PinQuadExact.Spec]
  obtain ⟨ha0, hav, hdv, hcv, hbv, hpin⟩ := h_holds
  rw [ha0] at hav
  rw [hav] at hdv
  rw [hdv] at hcv
  rw [hcv] at hbv
  rw [hpin, hav, hbv, hcv, hdv]
  rfl

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [AddExact.circuit, AddExact.Assumptions,
    XorRotateExact.circuit, XorRotateExact.Assumptions,
    PinQuadExact.circuit, PinQuadExact.Assumptions, and_self]

def circuit : FormalCircuit (F p2) GInputs Quad :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end GSecond

namespace G

def main (input : Var GInputs (F p2)) :
    Circuit (F p2) (Var Quad (F p2)) := do
  let first ← GFirst.circuit input
  GSecond.circuit
    ⟨first.a, first.b, first.c, first.d, input.mx, input.my⟩

instance elaborated :
    ElaboratedCircuit (F p2) GInputs Quad main := by
  elaborate_circuit

def Assumptions (_ : GInputs (F p2)) : Prop := True

def Spec (input : GInputs (F p2)) (output : Quad (F p2)) : Prop :=
  output = gValues input.quad input.mx input.my

theorem soundness :
    Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, GFirst.circuit, GSecond.circuit,
    GFirst.Assumptions, GFirst.Spec, GSecond.Assumptions, GSecond.Spec]
  obtain ⟨hfirst, hsecond⟩ := h_holds
  simpa only [gValues, GInputs.quad, hfirst] using hsecond

theorem completeness :
    Completeness (F p2) main Assumptions := by
  circuit_proof_start
  simp only [GFirst.circuit, GFirst.Assumptions, GSecond.circuit,
    GSecond.Assumptions, and_self]

def circuit : FormalCircuit (F p2) GInputs Quad :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end G
end Solution.Blake3CompressGF2Canonical
