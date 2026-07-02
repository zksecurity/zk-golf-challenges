import Challenge.Specs.RSASSAPKCS1v15
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
Public interface for this RSASSA-PKCS1-v1_5/SHA256/4096/e=65537 instance.

This file is the trusted boundary: it owns the input/output type and the
statements the implementation must prove. The implementation may be arbitrary,
but its exported proofs must have exactly these types.
-/

namespace Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537

namespace Interface

/-- Number of octets in a 4096-bit RSA modulus/signature. -/
@[reducible] def modulusBytesLen : ℕ :=
  Specs.RSASSAPKCS1v15_SHA256_4096_65537.modulusBytesLen

/-- Number of octets in a SHA-256 digest. -/
@[reducible] def digestBytesLen : ℕ :=
  Specs.RSASSAPKCS1v15.HashAlgorithm.sha256.digestLength

/--
Inputs to RSASSA-PKCS1-v1_5/SHA256/4096/e=65537 verification.

All vectors are byte strings encoded as field elements.
-/
structure Input (F : Type) where
  /-- Big-endian octet encoding of the RSA modulus `N`. -/
  modulus : Vector F modulusBytesLen
  /-- SHA-256 digest of the message being verified. -/
  digest : Vector F digestBytesLen
  /-- Big-endian octet encoding of the RSA signature `S`. -/
  signature : Vector F modulusBytesLen
deriving ProvableStruct

abbrev Output : TypeMap := unit

section

-- we are working over the circom prime
def circomPrime : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

axiom hCircomPrime : circomPrime.Prime
instance : Fact circomPrime.Prime := ⟨hCircomPrime⟩

/--
  Interpret a field-element byte vector as the corresponding natural bytes.
-/
def fieldBytesToNat {n : ℕ} (xs : Vector (F circomPrime) n) : Vector ℕ n :=
  xs.map ZMod.val

def Assumptions (input : Input (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop :=
  Specs.RSASSAPKCS1v15_SHA256_4096_65537.Assumptions
    (fieldBytesToNat input.modulus)
    (fieldBytesToNat input.digest)
    (fieldBytesToNat input.signature)

/--
Soundness statement: the public inputs satisfy RFC 8017
RSASSA-PKCS1-v1_5 verification for SHA-256, a 4096-bit modulus, and public
exponent `e = 65537`.
-/
def Spec (input : Input (F circomPrime)) (_output : Output (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop :=
  Specs.RSASSAPKCS1v15_SHA256_4096_65537.Spec
    (fieldBytesToNat input.modulus)
    (fieldBytesToNat input.digest)
    (fieldBytesToNat input.signature)

/--
Honest-prover assumptions. Because this instance is an assertion circuit, a
complete prover must be given inputs that already satisfy the verification spec.
-/
def ProverAssumptions
    (input : Input (F circomPrime)) (data : ProverData (F circomPrime)) (_hint : ProverHint (F circomPrime)) : Prop :=
  Assumptions input data ∧ Spec input () data

/-- No additional prover-visible output property is needed for an assertion. -/
def ProverSpec
    (_input : Input (F circomPrime)) (_output : Output (F circomPrime)) (_hint : ProverHint (F circomPrime)) : Prop :=
  True

end

end Interface

end Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537
