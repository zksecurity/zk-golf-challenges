import Solution.Secp256k1ScalarMulFixedBase.MulMod
import Challenge.Specs.Secp256k1
import Challenge.Instances.Secp256k1ScalarMulFixedBase.Interface

/-!
# secp256k1 scalar multiplication — parameters, types, and decoding

Shared definitions for the secp256k1 variable-base scalar-multiplication
reference circuit: the emulated-field limb parameters, the constant limbs of
the secp256k1 prime, the flagged point type, and the decoding functions that
bridge circuit values to the trusted spec (`Challenge.Specs.Secp256k1`).

The secp256k1 base field (256-bit prime `p`) is emulated over the circuit
field (the ~254-bit circom/bn254 scalar prime) as `numLimbs = 4` little-endian
limbs of `limbBits = 64` bits — byte-aligned, so the byte-encoded output
boundary is a per-limb affine recomposition — reusing the big-integer gadget
family adapted
from the RSA solution (`Normalize`, `LessThan`, `Equal`, `EqViaCarries`,
`MulMod`).
-/

namespace Solution.Secp256k1ScalarMulFixedBase

/-- The circuit field: the bn254/circom scalar prime, owned (with its
primality axiom) by the instance Interface. Reducible alias so every gadget
file can keep referring to it unqualified. -/
@[reducible] def circomPrime : ℕ :=
  Challenge.Instances.Secp256k1ScalarMulFixedBase.Interface.circomPrime

instance : Fact (circomPrime > 2) := ⟨by decide⟩

/-- The emulated secp256k1 base-field prime (`2^256 - 2^32 - 977`). -/
@[reducible] def P256 : ℕ := Specs.Secp256k1.p

/-- Number of limbs of an emulated secp256k1 base-field element. -/
@[reducible] def numLimbs : ℕ := 4

/-- Limb bit-width (byte-aligned: one limb is exactly `bytesPerLimb` bytes). -/
@[reducible] def limbBits : ℕ := 64

/-- Bytes per limb (`limbBits / 8`). -/
@[reducible] def bytesPerLimb : ℕ := 8

/-- Number of bytes of a coordinate (`numLimbs * bytesPerLimb`). -/
@[reducible] def coordBytes : ℕ := 32

/-- An emulated secp256k1 base-field element: 4 little-endian 64-bit limbs
(covering exactly 256 bits; canonical values are `< P256 < 2^256`). -/
@[reducible] def Emu : TypeMap := BigInt numLimbs

/-- Big-integer parameters for 256-bit values over the circom prime: 4 limbs
of 64 bits, 69-bit carries. The largest field-size hypothesis (`hWp`) is
`≈ 2^133.1 < 2^253.6`. -/
def secpParams : BigIntParams circomPrime numLimbs where
  B := limbBits
  W := 69
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide

/-! ## Constants as limbs -/

/-- Limb `k` of a natural number, little-endian base `2^limbBits`. -/
def limbOfNat (v k : ℕ) : ℕ := v / 2 ^ (limbBits * k) % 2 ^ limbBits

/-- A natural number `< 2^256` as a value-level `Emu`. -/
def emuOfNat (v : ℕ) : Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs => ((limbOfNat v k.val : ℕ) : F circomPrime)

/-- A natural number `< 2^256` as constant limb expressions. -/
def emuConst (v : ℕ) : Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (((limbOfNat v k.val : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- The secp256k1 prime as constant limb expressions (the `modulus` argument
of every `MulMod`/`EqViaCarries` call). -/
def pConst : Var Emu (F circomPrime) := emuConst P256

/-- Constant `0` as limb expressions. -/
def zeroConst : Var Emu (F circomPrime) := emuConst 0

/-- Constant `1` as limb expressions. -/
def oneConst : Var Emu (F circomPrime) := emuConst 1

/-! ## Witness-side evaluation helpers -/

/-- Natural-number value of an `Emu` variable under a prover environment.
Used only inside witness generators. -/
def evalEmu (env : ProverEnvironment (F circomPrime))
    (x : Var Emu (F circomPrime)) : ℕ :=
  Limbs.fromLimbs limbBits
    ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

/-! ## Decoding to the trusted spec -/

/-- Decode an emulated element to the secp256k1 base field of the trusted
spec. -/
def decodeFe (x : Emu (F circomPrime)) : Specs.Secp256k1.Fp :=
  ((x.value limbBits : ℕ) : Specs.Secp256k1.Fp)

/-- A well-formed emulated field element: normalized limbs and a canonical
(`< P256`) value. On canonical elements `decodeFe` is injective
(`BigInt.value_inj`), so spec-level equality is equivalent to limb-wise
equality. -/
def Fe.Valid (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits ∧ x.value limbBits < P256

/-! ## Flagged points -/

/-- A flagged secp256k1 point: affine coordinates as emulated field elements
plus a boolean is-infinity flag. The coordinates carry no meaning when the
flag is set. This is the in-circuit representation of
`Specs.ShortWeierstrass.GroupPoint`. -/
structure FlaggedPoint (F : Type) where
  x : Emu F
  y : Emu F
  isInf : F
deriving ProvableStruct

/-- Decode a flagged point to a spec-level group point. -/
def decodePoint (P : FlaggedPoint (F circomPrime)) :
    Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp :=
  if P.isInf = 1 then .infinity
  else .affine { x := decodeFe P.x, y := decodeFe P.y }

/-- A well-formed flagged point: boolean flag, valid coordinates, and — when
finite — the decoded point lies on the curve. -/
def FlaggedPoint.Valid (P : FlaggedPoint (F circomPrime)) : Prop :=
  IsBool P.isInf ∧ Fe.Valid P.x ∧ Fe.Valid P.y ∧
    (P.isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
        { x := decodeFe P.x, y := decodeFe P.y })

/-- The constant point at infinity (coordinates zero, flag set). -/
def infConst : Var FlaggedPoint (F circomPrime) :=
  { x := zeroConst, y := zeroConst,
    isInf := ((1 : F circomPrime) : Expression (F circomPrime)) }

end Solution.Secp256k1ScalarMulFixedBase
