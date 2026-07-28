import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Instances.Blake3CompressGF2Canonical.Spec

/-!
Shared interface for the canonical BLAKE3 compression challenge over `F 2`.

The input uses the raw 896-bit serialization defined in `Spec.lean`: 8
chaining-value words, 16 message words, the low and high counter words, the
block length, and the flags. The output is all 16 compression words (512 bits).
Within every word, bit `32 * i + j` is bit `j`.
-/

namespace Challenge.Instances.Blake3CompressGF2Canonical

namespace Interface

open Challenge.F2Bits

structure Input (F : Type) where
  bits : Vector F inputBits
deriving ProvableStruct

structure Output (F : Type) where
  bits : Vector F outputBits
deriving ProvableStruct

def Assumptions (_input : Input (F p2)) (_data : ProverData (F p2)) : Prop := True

def Spec (input : Input (F p2)) (output : Output (F p2))
    (_data : ProverData (F p2)) : Prop :=
  output.bits = Blake3Bits.compress input.bits

def ProverAssumptions
    (input : Input (F p2)) (data : ProverData (F p2)) (_hint : ProverHint (F p2)) : Prop :=
  Assumptions input data

def ProverSpec
    (_input : Input (F p2)) (_output : Output (F p2)) (_hint : ProverHint (F p2)) : Prop :=
  True

end Interface
end Challenge.Instances.Blake3CompressGF2Canonical
