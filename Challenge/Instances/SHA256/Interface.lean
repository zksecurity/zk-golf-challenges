import Challenge.Specs.SHA256
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS


/-!
Public interface for a SHA-256 assertion instance.

This file is the trusted boundary: it owns the input/output type and the
statements the implementation must prove. The implementation may be arbitrary,
but its exported proofs must have exactly these types.
-/

namespace Challenge.Instances.SHA256

namespace Interface

/-- Number of input octets for this SHA-256 instance template. -/
@[reducible] def inputBufferLen : ℕ := 256

/-- Number of 32-bit words in a SHA-256 digest. -/
@[reducible] def digestWordsLen : ℕ := 8

/--
Inputs to SHA-256 verification.

The message is a byte string encoded as field elements. The digest is encoded as
eight 32-bit words.
-/
structure Input (F : Type) where
  /-- Message bytes. -/
  message : Vector F inputBufferLen

  /--
    Message length.
    The message gets truncated to this length and then hashed
  -/
  messageLen : F
deriving ProvableStruct

structure Output (F : Type) where
  digest : Vector F 8
deriving ProvableStruct

section

-- we are working over the circom prime
def circomPrime : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

axiom hCircomPrime : circomPrime.Prime
instance : Fact circomPrime.Prime := ⟨hCircomPrime⟩

/--
  Interpret a field-element vector as the corresponding natural values.
-/
def fieldElemsToNat {n : ℕ} (xs : Vector (F circomPrime) n) : Vector ℕ n :=
  xs.map ZMod.val

def Assumptions (input : Input (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop :=
  Specs.SHA256.Assumptions (fieldElemsToNat input.message) input.messageLen.val

def Spec (input : Input (F circomPrime)) (output : Output (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop :=
  Specs.SHA256.Spec
    (fieldElemsToNat input.message)
    input.messageLen.val
    (fieldElemsToNat output.digest)

def ProverAssumptions
    (input : Input (F circomPrime)) (data : ProverData (F circomPrime)) (_hint : ProverHint (F circomPrime)) : Prop :=
  -- the honest inputs satisfy the assumptions
  Assumptions input data ∧
  -- the honest prover pads the data with zeros
  ∀ (i : Fin inputBufferLen), i >= input.messageLen.val → input.message[i]'(i.isLt) = 0

def ProverSpec
    (_input : Input (F circomPrime)) (_output : Output (F circomPrime)) (_hint : ProverHint (F circomPrime)) : Prop :=
  True

end

end Interface
end Challenge.Instances.SHA256
