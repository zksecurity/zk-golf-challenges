import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Theorems
import Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface

/-!
# Byte ↔ bit ↔ limb glue for the RSASSA-PKCS1-v1_5 / SHA256 / 4096 instance

Pure helper definitions (no proofs) used by `Main.lean` to bridge the byte-vector
`Input` of the trusted Challenge interface to the big-integer (`BigInt 34`)
inputs of the verified RSA core (`ModExp`, `LessThan`, `Equal`).

## Conventions

The byte vectors of the interface are **big-endian**: index `0` is the most
significant byte. For a `modulusBytesLen = 512`-byte vector the global bit index
`p ∈ [0, 4096)` of byte `j` (with `j = 0` the MSB), bit `t ∈ [0,8)` (the `2^t`
place of byte `j`) is

  `bitIndexOfByte j t = 8 * (511 - j) + t`.

Hence the integer denoted is `Σ_p bit[p] · 2^p` (little-endian over bits), and
each limb `k ∈ [0,34)` collects the 121 bits `[121·k, 121·k + 121)` (clamped to
`< 4096`), as an affine `Expression`:

  `limb_k = Σ_{t, 121·k+t < 4096, t < 121} bit[121·k + t] · 2^t`.

Limbs `0..32` are full 121-bit limbs (covering bits `0..3992`); limb `33` holds
the top 103 bits (`3993..4095`). Each limb is `< 2^121` by construction.

The EM (encoded message) for PKCS#1-v1_5 is also a 512-byte big-endian vector;
its low 256 bits are exactly the SHA-256 digest bits, the rest are the constant
DigestInfo/padding prefix.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace Bytes

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537

/-- Number of 121-bit limbs. -/
@[reducible] def numLimbs : ℕ := 34

/-- The limb width `B` (bits per limb). -/
@[reducible] def limbBits : ℕ := 121

/-- Total bit width covered by the modulus/signature/EM (`4096`). -/
@[reducible] def totalBits : ℕ := 4096

/-! ## Index helpers -/

/-- Global bit index of bit `t` of big-endian byte `j` (byte `0` = MSB), in a
`512`-byte (`4096`-bit) vector. -/
@[reducible] def bitIndexOfByte (j t : ℕ) : ℕ := 8 * (511 - j) + t

/-- Global bit index of bit `t` of big-endian digest byte `dj` (`dj = 0` = MSB),
within the low `256` digest bits. The 32 digest bytes occupy bits `[0, 256)`
exactly (least significant digest byte = digest byte 31). -/
@[reducible] def digestBitIndex (dj t : ℕ) : ℕ := 8 * (31 - dj) + t

/-! ## Byte reconstruction helper -/

/-- The affine expression `Σ_{t<8} bits[base + t] · 2^t` reconstructing the byte
value at flat bit offset `base`. Requires `base + 8 ≤ n`. Used to wire byte/bit
consistency in the `ByteBlock` assertion and to recompose limbs in
`BytesLemmas`. -/
def byteFromBits {n : ℕ} (bits : Vector (Expression (F circomPrime)) n)
    (base : ℕ) : Expression (F circomPrime) :=
  Fin.foldl 8 (fun acc t =>
    acc +
      (if h : base + t.val < n then bits[base + t.val]'h else 0) *
        (((2 ^ t.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0

/-! ## Limb packing -/

/-- Pack a `totalBits`-bit boolean expression vector into a `BigInt 34` of
affine limbs: limb `k = Σ_{t<121, 121·k+t<4096} bits[121·k + t] · 2^t`. -/
def packLimbs (bits : Vector (Expression (F circomPrime)) totalBits) :
    Var (BigInt numLimbs) (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    Fin.foldl limbBits (fun acc t =>
      let p : ℕ := limbBits * k.val + t.val
      acc +
        (if h : p < totalBits then bits[p]'h else 0) *
          (((2 ^ t.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0

/-! ## PKCS#1-v1_5 encoded-message (EM) constant prefix

EM is a 512-byte big-endian octet string:

* byte 0   = 0x00
* byte 1   = 0x01
* bytes 2..459   = 0xff   (458 bytes)
* byte 460 = 0x00
* bytes 461..479 = SHA-256 DER DigestInfo prefix (19 bytes):
    `30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20`
* bytes 480..511 = the 32 digest bytes (the variable part).

The digest occupies the low 256 bits `[0,256)`; everything else is constant. -/

/-- The 19-byte SHA-256 DER DigestInfo prefix. -/
def derPrefix : Vector ℕ 19 :=
  #v[0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
     0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20]

/-- The constant EM byte value at big-endian byte index `j ∈ [0,512)`, for the
non-digest positions. (Digest positions `j ∈ [480,512)` are handled separately
by wiring in the digest bits; the value returned here for those positions is
`0` and is unused.) -/
def emByteConst (j : ℕ) : ℕ :=
  if j = 0 then 0x00
  else if j = 1 then 0x01
  else if 2 ≤ j ∧ j ≤ 459 then 0xff
  else if j = 460 then 0x00
  else if 461 ≤ j ∧ j ≤ 479 then (if h : j - 461 < 19 then derPrefix[j - 461] else 0)
  else 0

/-- The constant EM bit value at global bit index `p ∈ [0,4096)` for the
non-digest positions (`p ≥ 256`): bit `p % 8` of the constant EM byte
`511 - p / 8`. For `p < 256` the value is `0` (those bits come from the digest
and are wired in separately). -/
def emConstBit (p : ℕ) : F circomPrime :=
  if p < 256 then 0
  else
    let j : ℕ := 511 - p / 8
    let t : ℕ := p % 8
    ((emByteConst j / 2 ^ t % 2 : ℕ) : F circomPrime)

/-- Build the `4096`-bit EM expression vector: bits `[0,256)` are the digest bits
`digBits`, bits `[256,4096)` are the constant prefix bits `emConstBit`. -/
def emBits (digBits : Vector (Expression (F circomPrime)) 256) :
    Vector (Expression (F circomPrime)) totalBits :=
  Vector.ofFn fun p : Fin totalBits =>
    if h : p.val < 256 then digBits[p.val]'h
    else (Expression.const (emConstBit p.val))

end Bytes
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
