import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS


/-!
Public interface for the `AssertBytes` "hello world" assertion instance.

This file is the trusted boundary: it owns the input type and the statements the
implementation must prove. The implementation may be arbitrary, but its exported
proofs must have exactly these types.

The instance is intentionally minimal: given a fixed-length buffer of field
elements and *no* preconditions, the circuit must assert that every element is a
byte (its canonical representative is `< 256`).
-/

namespace Challenge.Instances.AssertBytes

namespace Interface

/-- Number of buffer elements that must be byte-checked. -/
@[reducible] def bufferLen : ℕ := 16

/-- Inputs: a flat buffer of `bufferLen` field elements. -/
structure Input (F : Type) where
  buffer : Vector F bufferLen
deriving ProvableStruct

/-- The circuit produces no output; it is an assertion. -/
@[reducible] def Output : TypeMap := unit

section

-- we are working over the circom prime
def circomPrime : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

axiom hCircomPrime : circomPrime.Prime
instance : Fact circomPrime.Prime := ⟨hCircomPrime⟩

/--
No assumptions: the circuit must byte-check arbitrary inputs, so soundness holds
unconditionally.
-/
def Assumptions (_input : Input (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop := True

/-- Spec: every buffer element is a byte (its `ZMod.val` is `< 256`). -/
def Spec (input : Input (F circomPrime)) (_output : Output (F circomPrime))
    (_data : ProverData (F circomPrime)) : Prop :=
  ∀ i : Fin bufferLen, (input.buffer[i.val]'i.isLt).val < 256

/--
For completeness the honest prover must already hold genuine bytes: the circuit
constrains byteness, so the witnessed bit decomposition only exists when each
element is `< 256`.
-/
def ProverAssumptions
    (input : Input (F circomPrime)) (_data : ProverData (F circomPrime))
    (_hint : ProverHint (F circomPrime)) : Prop :=
  ∀ i : Fin bufferLen, (input.buffer[i.val]'i.isLt).val < 256

def ProverSpec
    (_input : Input (F circomPrime)) (_output : Output (F circomPrime))
    (_hint : ProverHint (F circomPrime)) : Prop :=
  True

end

end Interface
end Challenge.Instances.AssertBytes
