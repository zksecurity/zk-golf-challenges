import Solution.Secp256k1ScalarMulFixedBase.CompleteAdd

/-!
# One double-and-add step — `Step`

`FormalCircuit` for a single left-to-right double-and-add step, the loop body
of `ScalarMul`: double the accumulator (a self-add), add the base point, and
select by the scalar bit. Its specification is exactly the trusted spec's
`Specs.ShortWeierstrass.step` on decoded values.

Extracting the body as its own gadget keeps the `Circuit.foldl` loop body a
single `subcircuit` call, so the fold's `ConstantLength`/`ConstantOutput`
synthesis stays trivial (inlining the three subcircuits blows the heartbeat
budget).

-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Step

/-- Inputs of `Step`: the accumulator, the base-point coordinates, and the
current scalar bit. -/
structure Inputs (F : Type) where
  acc : FlaggedPoint F
  px : Emu F
  py : Emu F
  bit : F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime)) := do
  let { acc, px, py, bit } := input
  let base : Var FlaggedPoint (F circomPrime) :=
    { x := px, y := py,
      isInf := ((0 : F circomPrime) : Expression (F circomPrime)) }
  let doubled ← subcircuit CompleteAdd.circuit { P := acc, Q := acc }
  let added ← subcircuit CompleteAdd.circuit { P := doubled, Q := base }
  subcircuit (Mux.circuit (M := FlaggedPoint))
    { selector := bit, ifTrue := added, ifFalse := doubled }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs FlaggedPoint main := by
  elaborate_circuit

/-- Preconditions: the accumulator is a well-formed flagged point, the bit is
boolean, and the base point has canonical coordinates and lies on the curve. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.acc.Valid ∧ IsBool input.bit ∧
  Fe.Valid input.px ∧ Fe.Valid input.py ∧
  Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
    { x := decodeFe input.px, y := decodeFe input.py }

/-- Postcondition: the output is well-formed and decodes to the trusted
spec's `step` on the decoded inputs. -/
def Spec (input : Inputs (F circomPrime)) (out : FlaggedPoint (F circomPrime)) : Prop :=
  out.Valid ∧
    decodePoint out =
      Specs.ShortWeierstrass.step Specs.Secp256k1.curve
        { x := decodeFe input.px, y := decodeFe input.py }
        (decodePoint input.acc) (input.bit.val)

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hacc, hbit, hpx, hpy, honcurve⟩ := h_assumptions
  obtain ⟨hdbl, hadd, hmux⟩ := h_holds
  obtain ⟨hdblv, hdble⟩ := hdbl hacc
  have hbase : FlaggedPoint.Valid
      { x := input_px, y := input_py, isInf := (0 : F circomPrime) } :=
    ⟨Or.inl rfl, hpx, hpy, fun _ => honcurve⟩
  obtain ⟨haddv, hadde⟩ := hadd ⟨hdblv, hbase⟩
  have hmux' := hmux hbit
  rw [hmux']
  have hbased : decodePoint
      { x := input_px, y := input_py, isInf := (0 : F circomPrime) } =
      .affine { x := decodeFe input_px, y := decodeFe input_py } := by
    simp only [decodePoint, if_neg (zero_ne_one (α := F circomPrime))]
  rcases hbit with h0 | h1
  · rw [h0, if_neg (zero_ne_one (α := F circomPrime)), ZMod.val_zero]
    simp only [Specs.ShortWeierstrass.step, if_neg (zero_ne_one (α := ℕ))]
    exact ⟨hdblv, hdble⟩
  · rw [h1, if_pos rfl, ZMod.val_one]
    simp only [Specs.ShortWeierstrass.step, if_true]
    exact ⟨haddv, by rw [hadde, hdble, hbased]⟩

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [CompleteAdd.circuit, CompleteAdd.Assumptions, CompleteAdd.Spec,
    Mux.circuit, Mux.Assumptions, Mux.Spec]
  obtain ⟨hacc, hbit, hpx, hpy, honcurve⟩ := h_assumptions
  obtain ⟨hdbl, -⟩ := h_env
  obtain ⟨hdblv, -⟩ := hdbl hacc
  exact ⟨hacc, ⟨hdblv, ⟨Or.inl rfl, hpx, hpy, fun _ => honcurve⟩⟩, hbit⟩

/-- The `Step` formal circuit: one double-and-add iteration. -/
def circuit : FormalCircuit (F circomPrime) Inputs FlaggedPoint where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Step
end Solution.Secp256k1ScalarMulFixedBase
