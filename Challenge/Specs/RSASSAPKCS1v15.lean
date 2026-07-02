import Mathlib.Data.Nat.Log

namespace Specs.RSASSAPKCS1v15

/--
  OS2IP converts an octet string to a nonnegative integer.
-/
def os2ip {n : ℕ} (xs : Vector ℕ n) : ℕ :=
  xs.foldl (fun acc x => acc * 256 + x) 0

/--
  I2OSP converts a nonnegative integer to an octet string of a specified length.
-/
def i2osp (x xLen : ℕ) : Option (Vector ℕ xLen) :=
  if x < 256 ^ xLen then
    some (Vector.ofFn fun i => x / 256 ^ (xLen - 1 - i.val) % 256)
  else
    none

/--
  An octet string represented as a vector of natural numbers.
-/
@[reducible] def IsOctetString {n : ℕ} (xs : Vector ℕ n) : Prop :=
  ∀ i : Fin n, xs[i] < 256

/--
  A natural number `n` has exactly `bits` bits.
-/
@[reducible] def HasBitSize (n bits : ℕ) : Prop :=
  2 ^ (bits - 1) ≤ n ∧ n < 2 ^ bits

/--
  RSAVP1: recover the message representative from a signature representative.
-/
def rsavp1? (n : ℕ) (e : ℕ) (s : ℕ) : Option ℕ :=
  if s < n then
    some (s ^ e % n)
  else
    none

/--
  Hash algorithms listed by RFC 8017 Appendix B.1 with fixed DER DigestInfo
  prefixes in Section 9.2.
-/
inductive HashAlgorithm where
  | md2
  | md5
  | sha1
  | sha224
  | sha256
  | sha384
  | sha512
  | sha512_224
  | sha512_256
deriving DecidableEq, Repr

namespace HashAlgorithm

/--
  Digest length, in octets.
-/
def digestLength : HashAlgorithm → ℕ
  | md2 => 16
  | md5 => 16
  | sha1 => 20
  | sha224 => 28
  | sha256 => 32
  | sha384 => 48
  | sha512 => 64
  | sha512_224 => 28
  | sha512_256 => 32

/--
  DER `DigestInfo` prefix length, in octets.
-/
def digestInfoPrefixLength : HashAlgorithm → ℕ
  | md2 => 18
  | md5 => 18
  | sha1 => 15
  | sha224 => 19
  | sha256 => 19
  | sha384 => 19
  | sha512 => 19
  | sha512_224 => 19
  | sha512_256 => 19

/--
  DER `DigestInfo` prefix from RFC 8017, Section 9.2.
-/
def digestInfoPrefix : (alg : HashAlgorithm) → Vector ℕ alg.digestInfoPrefixLength
  | md2 =>
      #v[0x30, 0x20, 0x30, 0x0c, 0x06, 0x08, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
        0x02, 0x02, 0x05, 0x00, 0x04, 0x10]
  | md5 =>
      #v[0x30, 0x20, 0x30, 0x0c, 0x06, 0x08, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
        0x02, 0x05, 0x05, 0x00, 0x04, 0x10]
  | sha1 =>
      #v[0x30, 0x21, 0x30, 0x09, 0x06, 0x05, 0x2b, 0x0e, 0x03, 0x02, 0x1a, 0x05,
        0x00, 0x04, 0x14]
  | sha224 =>
      #v[0x30, 0x2d, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
        0x04, 0x02, 0x04, 0x05, 0x00, 0x04, 0x1c]
  | sha256 =>
      #v[0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
        0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20]
  | sha384 =>
      #v[0x30, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
        0x04, 0x02, 0x02, 0x05, 0x00, 0x04, 0x30]
  | sha512 =>
      #v[0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
        0x04, 0x02, 0x03, 0x05, 0x00, 0x04, 0x40]
  | sha512_224 =>
      #v[0x30, 0x2d, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
        0x04, 0x02, 0x05, 0x05, 0x00, 0x04, 0x1c]
  | sha512_256 =>
      #v[0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
        0x04, 0x02, 0x06, 0x05, 0x00, 0x04, 0x20]

end HashAlgorithm

/-- DER `DigestInfo` value for `digest`. -/
def digestInfo (alg : HashAlgorithm) (digest : Vector ℕ alg.digestLength) :
    Vector ℕ (alg.digestInfoPrefixLength + alg.digestLength) :=
  alg.digestInfoPrefix ++ digest

/-- EMSA-PKCS1-v1_5 encoding for an already-computed digest. -/
def emsaPkcs1v15Encode? (alg : HashAlgorithm) (digest : Vector ℕ alg.digestLength) (emLen : ℕ) :
    Option (Vector ℕ emLen) :=
  let t := digestInfo alg digest
  let tLen := alg.digestInfoPrefixLength + alg.digestLength
  if h : IsOctetString digest ∧ tLen + 11 ≤ emLen then
    let em := (#v[0x00, 0x01] : Vector ℕ 2) ++
      Vector.replicate (emLen - tLen - 3) 0xff ++
      (#v[0x00] : Vector ℕ 1) ++
      t
    some (Vector.cast (by omega) em)
  else
    none

/-- RFC 8017 RSASSA-PKCS1-v1_5 verification for a signature octet string.

The only difference with RFC 8017 is that we take the modulus as a byte vector
instead of a natural number.
Given nOctets (the byte encoding of N) we define N := os2ip nOctets
-/
def verifySignature {modulusBytesLen : ℕ} (alg : HashAlgorithm) (e : ℕ)
    (n : Vector ℕ modulusBytesLen)
    (h : Vector ℕ alg.digestLength)
    (signature : Vector ℕ modulusBytesLen) : Bool :=
  let n := os2ip n
  let signature := os2ip signature

  let recovered := rsavp1? n e signature
  let expected := emsaPkcs1v15Encode? alg h modulusBytesLen

  match recovered, expected with
  | some r, some e => i2osp r modulusBytesLen == some e
  | _, _ => false


def Assumptions {modulusBytesLen : ℕ} (alg : HashAlgorithm)
    (n : Vector ℕ modulusBytesLen)
    (h : Vector ℕ alg.digestLength)
    (signature : Vector ℕ modulusBytesLen) : Prop :=
  -- n is a byte string
  IsOctetString n ∧

  -- digest is a byte string
  IsOctetString h ∧

  -- signature is a byte string
  IsOctetString signature ∧

  -- the representative integer of n has the correct bit size
  HasBitSize (os2ip n) (modulusBytesLen * 8)

  -- NOTE: an additional assumption that we do not encode formally here is that
  -- h is the digest of the message M under the claimed hash algorithm, i.e. that
  -- h = H(M) for the same H as the one specified by alg.


def Spec {modulusBytesLen : ℕ} (alg : HashAlgorithm) (e : ℕ)
    (n : Vector ℕ modulusBytesLen)
    (h : Vector ℕ alg.digestLength)
    (signature : Vector ℕ modulusBytesLen) : Prop :=
  verifySignature alg e n h signature = true

end Specs.RSASSAPKCS1v15


/-
 Concrete instances of RSASSA-PKCS1-v1_5/SHA-256 verification for 2048- and 4096-bit moduli and public exponents 3 and 65537.
-/

namespace Specs.RSASSAPKCS1v15_SHA256_2048_3

@[reducible] def algorithm := Specs.RSASSAPKCS1v15.HashAlgorithm.sha256
@[reducible] def modulusBytesLen := 2048 / 8
@[reducible] def publicExponent := 3

def Assumptions := Specs.RSASSAPKCS1v15.Assumptions (modulusBytesLen := modulusBytesLen) algorithm
def Spec := Specs.RSASSAPKCS1v15.Spec (modulusBytesLen := modulusBytesLen) algorithm publicExponent

end Specs.RSASSAPKCS1v15_SHA256_2048_3

namespace Specs.RSASSAPKCS1v15_SHA256_2048_65537

@[reducible] def algorithm := Specs.RSASSAPKCS1v15.HashAlgorithm.sha256
@[reducible] def modulusBytesLen := 2048 / 8
@[reducible] def publicExponent := 65537

def Assumptions := Specs.RSASSAPKCS1v15.Assumptions (modulusBytesLen := modulusBytesLen) algorithm
def Spec := Specs.RSASSAPKCS1v15.Spec (modulusBytesLen := modulusBytesLen) algorithm publicExponent

end Specs.RSASSAPKCS1v15_SHA256_2048_65537

namespace Specs.RSASSAPKCS1v15_SHA256_4096_3

@[reducible] def algorithm := Specs.RSASSAPKCS1v15.HashAlgorithm.sha256
@[reducible] def modulusBytesLen := 4096 / 8
@[reducible] def publicExponent := 3

def Assumptions := Specs.RSASSAPKCS1v15.Assumptions (modulusBytesLen := modulusBytesLen) algorithm
def Spec := Specs.RSASSAPKCS1v15.Spec (modulusBytesLen := modulusBytesLen) algorithm publicExponent

end Specs.RSASSAPKCS1v15_SHA256_4096_3

namespace Specs.RSASSAPKCS1v15_SHA256_4096_65537

@[reducible] def algorithm := Specs.RSASSAPKCS1v15.HashAlgorithm.sha256
@[reducible] def modulusBytesLen := 4096 / 8
@[reducible] def publicExponent := 65537

def Assumptions := Specs.RSASSAPKCS1v15.Assumptions (modulusBytesLen := modulusBytesLen) algorithm
def Spec := Specs.RSASSAPKCS1v15.Spec (modulusBytesLen := modulusBytesLen) algorithm publicExponent

end Specs.RSASSAPKCS1v15_SHA256_4096_65537
