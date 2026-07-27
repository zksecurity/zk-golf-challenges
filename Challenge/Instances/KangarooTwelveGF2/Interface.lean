import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Specs.KangarooTwelve
import Challenge.Utils.F2Bits

namespace Challenge.Instances.KangarooTwelveGF2

namespace Interface

open Challenge.F2Bits

@[reducible] def permutationBits : ℕ := Specs.KangarooTwelve.stateBits

structure Input (F : Type) where
  state : Vector F permutationBits
deriving ProvableStruct

structure Output (F : Type) where
  state : Vector F permutationBits
deriving ProvableStruct

def Assumptions (_input : Input (F p2)) (_data : ProverData (F p2)) : Prop := True

def Spec (input : Input (F p2)) (output : Output (F p2)) (_data : ProverData (F p2)) :
    Prop :=
  output.state = Specs.KangarooTwelve.keccakP1600_12 input.state

def ProverAssumptions
    (input : Input (F p2)) (data : ProverData (F p2)) (_hint : ProverHint (F p2)) : Prop :=
  Assumptions input data

def ProverSpec
    (_input : Input (F p2)) (_output : Output (F p2)) (_hint : ProverHint (F p2)) : Prop :=
  True

end Interface
end Challenge.Instances.KangarooTwelveGF2
