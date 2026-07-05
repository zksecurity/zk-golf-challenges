import Challenge.Specs.Keccak
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS

namespace Challenge.Instances.KeccakF1600

namespace Interface

/-- Number of state bits of Keccak-f[1600]. -/
@[reducible] def stateBitsLen : ℕ := 1600

/--
Inputs to the Keccak-f[1600] permutation.

The state is a 1600-bit string encoded as field elements, one bit per element,
in the bit order of the spec (`Specs.Keccak`): bit `64·(x + 5y) + z` is bit `z`
of the lane at coordinates `(x, y)`.
-/
structure Input (F : Type) where
  /-- State bits. -/
  state : Vector F stateBitsLen
deriving ProvableStruct

/-- The permuted state, encoded like the input. -/
structure Output (F : Type) where
  state : Vector F stateBitsLen
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
  Specs.Keccak.Assumptions (fieldElemsToNat input.state)

def Spec (input : Input (F circomPrime)) (output : Output (F circomPrime))
    (_data : ProverData (F circomPrime)) : Prop :=
  Specs.Keccak.Spec (fieldElemsToNat input.state) (fieldElemsToNat output.state)

def ProverAssumptions
    (input : Input (F circomPrime)) (data : ProverData (F circomPrime))
    (_hint : ProverHint (F circomPrime)) : Prop :=
  -- the honest inputs satisfy the assumptions
  Assumptions input data

def ProverSpec
    (_input : Input (F circomPrime)) (_output : Output (F circomPrime))
    (_hint : ProverHint (F circomPrime)) : Prop :=
  True

end

end Interface
end Challenge.Instances.KeccakF1600
