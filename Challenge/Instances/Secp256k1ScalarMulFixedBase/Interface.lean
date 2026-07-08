import Challenge.Specs.Secp256k1
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS

/-!
Public interface for the secp256k1 fixed-base scalar-multiplication instance.

This file is the trusted boundary: it owns the input/output types and the
statements the implementation must prove. The implementation may be
arbitrary, but its exported proofs must have exactly these types.

The base point is fixed to the standard generator `G` (not part of the input),
so the only input is the scalar as a bit sequence (most significant first).
The output carries a boolean is-infinity flag with zero-masked coordinates,
making the relation total and each group element's encoding unique.
-/

namespace Challenge.Instances.Secp256k1ScalarMulFixedBase

namespace Interface

/-- Number of scalar bits (most significant first). -/
@[reducible] def scalarBits : ℕ := Specs.Secp256k1.scalarBits

/-- Number of bytes of a coordinate (big-endian). -/
@[reducible] def coordBytes : ℕ := 32

/--
Inputs of fixed-base scalar multiplication: the scalar as a bit sequence. The
base point is the fixed generator `G` and is not part of the input.
-/
structure Input (F : Type) where
  /-- Scalar bits, most significant first. -/
  bits : Vector F scalarBits
deriving ProvableStruct

/--
Output of scalar multiplication: the resulting group element, as big-endian
coordinate bytes plus a boolean point-at-infinity flag. The coordinate bytes
carry no meaning — and must be zero — when the flag is set.
-/
structure Output (F : Type) where
  /-- Result x-coordinate, big-endian bytes (zero when `isInf = 1`). -/
  x : Vector F coordBytes
  /-- Result y-coordinate, big-endian bytes (zero when `isInf = 1`). -/
  y : Vector F coordBytes
  /-- Boolean point-at-infinity flag. -/
  isInf : F
deriving ProvableStruct

section

-- we are working over the circom prime
def circomPrime : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

axiom hCircomPrime : circomPrime.Prime
instance : Fact circomPrime.Prime := ⟨hCircomPrime⟩

/--
  Big-endian byte value of a coordinate (the `os2ip` fold).
-/
def coordVal {n : ℕ} (v : Vector (F circomPrime) n) : ℕ :=
  v.toList.foldl (fun acc b => acc * 256 + b.val) 0

/--
  Decode a big-endian byte-encoded coordinate to the secp256k1 base field of
  the trusted spec.
-/
def decodeCoord (v : Vector (F circomPrime) coordBytes) : Specs.Secp256k1.Fp :=
  ((coordVal v : ℕ) : Specs.Secp256k1.Fp)

/--
  Every entry is a byte.
-/
@[reducible] def IsBytes {n : ℕ} (v : Vector (F circomPrime) n) : Prop :=
  ∀ i : Fin n, (v[i]).val < 256

/--
  Every entry is a bit.
-/
@[reducible] def IsBits (v : Vector (F circomPrime) scalarBits) : Prop :=
  ∀ i : Fin scalarBits, (v[i]).val < 2

/--
  Input assumptions (established by the caller, not enforced by the circuit):
  the scalar entries are bits. The base point is the fixed generator `G`,
  which lies on the curve, so no on-curve assumption is needed.
-/
def Assumptions (input : Input (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop :=
  IsBits input.bits

/--
  Well-formed output encoding, which the circuit must **enforce**: entries
  are bytes, the encoded coordinates are canonical (`< p`), the flag is
  boolean, and the coordinate bytes are zero when the flag is set. Together
  with `decodeOutput` this makes the wire encoding of each group element
  unique.
-/
def OutputValid (out : Output (F circomPrime)) : Prop :=
  IsBytes out.x ∧ IsBytes out.y ∧
  IsBool out.isInf ∧
  coordVal out.x < Specs.Secp256k1.p ∧
  coordVal out.y < Specs.Secp256k1.p ∧
  (out.isInf = 1 →
    (∀ i : Fin coordBytes, out.x[i] = 0) ∧ (∀ i : Fin coordBytes, out.y[i] = 0))

/--
  Decode the output to a spec-level group point.
-/
def decodeOutput (out : Output (F circomPrime)) :
    Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp :=
  if out.isInf = 1 then .infinity
  else .affine { x := decodeCoord out.x, y := decodeCoord out.y }

/--
  The circuit must output a well-formed encoding of the true multiple of the
  fixed generator: the decoded output satisfies the trusted total spec
  (`Specs.Secp256k1ScalarMulFixedBase.Spec`, naive double-and-add over
  the bits with base point `G` and the complete group law).
-/
def Spec (input : Input (F circomPrime)) (output : Output (F circomPrime))
    (_data : ProverData (F circomPrime)) : Prop :=
  OutputValid output ∧
  Specs.Secp256k1ScalarMulFixedBase.Spec (input.bits.map ZMod.val)
    (decodeOutput output)

def ProverAssumptions
    (input : Input (F circomPrime)) (data : ProverData (F circomPrime))
    (_hint : ProverHint (F circomPrime)) : Prop :=
  -- the honest inputs satisfy the assumptions; the relation is total, so no
  -- scalar needs to be excluded
  Assumptions input data

def ProverSpec
    (_input : Input (F circomPrime)) (_output : Output (F circomPrime))
    (_hint : ProverHint (F circomPrime)) : Prop :=
  True

end

end Interface
end Challenge.Instances.Secp256k1ScalarMulFixedBase
