import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Specs.SHA256
import Challenge.Utils.F2Bits

/-!
Shared interface for the canonical SHA-256 compression instance: a single
compression over the binary field `F 2` (Flock-style R1CS-over-GF(2)).

This file is the trusted boundary: it owns the input/output types and the
statements the implementation must prove. Words are flat GF(2) bit vectors,
packed little-endian (bit `32·i + j` is bit `j` of word `i`). There is no
padding or message-length handling; the circuit applies `compressBlock` to one
block. There are no assumptions because every element of `F 2` is already a
bit.
-/

namespace Challenge.Instances.SHA256CompressGF2Canonical

namespace Interface

open Challenge.F2Bits

/-- 256-bit chaining value = 8 × 32-bit words. -/
@[reducible] def cvBits : ℕ := 256

/-- 512-bit message block = 16 × 32-bit words. -/
@[reducible] def blockBits : ℕ := 512

/-- Inputs: chaining value `h` and message block `m`, as bit vectors. -/
structure Input (F : Type) where
  h : Vector F cvBits
  m : Vector F blockBits
deriving ProvableStruct

/-- Output: the chaining value after compressing the block. -/
structure Output (F : Type) where
  h : Vector F cvBits
deriving ProvableStruct

section

def Assumptions (_input : Input (F p2)) (_data : ProverData (F p2)) : Prop := True

/-- Spec: `h` (output) is the SHA-256 compression of `h` (input) under block `m`. -/
def Spec (input : Input (F p2)) (output : Output (F p2)) (_data : ProverData (F p2)) : Prop :=
  toWords 32 8 output.h
    = Specs.SHA256.compressBlock (toWords 32 8 input.h) (toWords 32 16 input.m)

def ProverAssumptions
    (input : Input (F p2)) (data : ProverData (F p2)) (_hint : ProverHint (F p2)) : Prop :=
  Assumptions input data

def ProverSpec
    (_input : Input (F p2)) (_output : Output (F p2)) (_hint : ProverHint (F p2)) : Prop :=
  True

end

end Interface
end Challenge.Instances.SHA256CompressGF2Canonical
