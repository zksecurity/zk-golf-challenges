import Challenge.Instances.SHA256.Interface
import Solution.SHA256.BitwiseOps

/-!
# Shared definitions for the SHA-256 instance circuit

Pure definitions (no constraints, no proofs) shared by the padding check,
length-flag check and digest selection gadgets, and by `Main`.

## Padded-message layout

The prover witnesses the padded message as `paddedBlocksLen * 16 * 32` bits,
laid out as `paddedBlocksLen` blocks of 16 words of 32 bits. Within a word,
bits are LSB-first (`valueBits` convention), and the four bytes of a word are
big-endian: byte `k ∈ [0,4)` of word `w` occupies bits `8*(3-k) .. 8*(3-k)+7`.

Byte index `j ∈ [0, paddedBlocksLen*64)` of the padded message lives in
block `j / 64`, word `(j % 64) / 4`, byte-in-word `j % 4`.
-/

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface (inputBufferLen)

/-- Maximum number of SHA-256 padding blocks for `inputBufferLen` bytes. -/
@[reducible] def paddedBlocksLen : ℕ := 5

/-- A prover-witnessed padded SHA-256 message, flattened as `5 * 16 * 32` block bits. -/
@[reducible] def paddedBitsLen : ℕ := paddedBlocksLen * 16 * 32

/-- Number of bytes in the padded-message buffer. -/
@[reducible] def paddedBytesLen : ℕ := paddedBlocksLen * 64

abbrev SHA256PaddedBits := fields paddedBitsLen

/-- Number of SHA-256 blocks needed to hash a `len`-byte message
(matches the block count of `Specs.SHA256.pad`). -/
def numBlocksForLen (len : ℕ) : ℕ :=
  (len + (55 + 64 - len % 64) % 64 + 9) / 64

/-!
## ℕ-level padded byte values
-/

/-- The expected padded byte at position `j` for a message of length `len`,
for the positions that do not come from the message itself:
`0x80` right after the message, then zeros, then the 8-byte big-endian bit
length at the end of block `numBlocksForLen len`, then zeros in the unused
trailing blocks. -/
def specPaddedByteConst (len j : ℕ) : ℕ :=
  let totalLen := numBlocksForLen len * 64
  if j = len then 0x80
  else if j < totalLen - 8 then 0
  else if j < totalLen then len * 8 / 2 ^ (8 * (totalLen - 1 - j)) % 256
  else 0

/-- The expected padded byte at position `j` for message bytes `msg`
truncated at length `len`. Agrees with the byte stream of
`Specs.SHA256.pad (truncate msg len)` on the first `numBlocksForLen len * 64`
bytes, and is zero afterwards. -/
def specPaddedByte (msg : Vector ℕ inputBufferLen) (len j : ℕ) : ℕ :=
  if h : j < len ∧ j < inputBufferLen then msg[j]'h.2
  else specPaddedByteConst len j

/-!
## Flat bit-vector indexing
-/

/-- Flat index (into the `paddedBitsLen` bit vector) of bit `t` of padded byte `j`. -/
def paddedBitIndex (j t : ℕ) : ℕ :=
  j / 64 * 512 + j % 64 / 4 * 32 + 8 * (3 - j % 4) + t

lemma paddedBitIndex_lt {j t : ℕ} (hj : j < paddedBytesLen) (ht : t < 8) :
    paddedBitIndex j t < paddedBitsLen := by
  unfold paddedBitIndex
  simp only [paddedBytesLen, paddedBitsLen, paddedBlocksLen] at hj ⊢
  omega

/-- The ℕ value of padded byte `j`, assembled from the witnessed bits. -/
def paddedByteVal (padded : Vector (F p) paddedBitsLen) (j : Fin paddedBytesLen) : ℕ :=
  Finset.univ.sum fun (t : Fin 8) =>
    (padded[paddedBitIndex j.val t.val]'(paddedBitIndex_lt j.isLt t.isLt)).val * 2 ^ t.val

/-- The ℕ value of byte `b` (big-endian position) of a 32-bit word of field bits. -/
def wordByteVal (w : Vector (F p) 32) (b : Fin 4) : ℕ :=
  Finset.univ.sum fun (t : Fin 8) =>
    (w[8 * (3 - b.val) + t.val]'(by omega)).val * 2 ^ t.val

/-!
## One-hot length flags
-/

/-- `flags` is the one-hot indicator vector of the value `ℓ`. -/
def OneHotAt (flags : Vector (F p) inputBufferLen) (ℓ : ℕ) : Prop :=
  ∀ k : Fin inputBufferLen, flags[k] = if k.val = ℓ then 1 else 0

/-!
## Expression-level helpers
-/

/-- Byte `byte` (big-endian position) of a 32-bit word, as a linear expression
in the word's bits. -/
def byteFromWord (word : Var (fields 32) (F p)) (byte : Fin 4) :
    Expression (F p) :=
  Fin.foldl 8
    (fun acc bit =>
      acc + word[8 * (3 - byte.val) + bit.val]'(by omega) *
        (((2 ^ bit.val : ℕ) : F p) : Expression (F p)))
    0

/-- Bit `bit` of word `word` of block `block` of the flat padded-bit vector. -/
def paddedBit
    (padded : Var SHA256PaddedBits (F p))
    (block : Fin paddedBlocksLen) (word : Fin 16) (bit : Fin 32) :
    Expression (F p) :=
  padded[block.val * 16 * 32 + word.val * 32 + bit.val]'(by
    have hb : block.val < 5 := block.isLt
    have hw := word.isLt
    have hbit := bit.isLt
    change block.val * 16 * 32 + word.val * 32 + bit.val < 5 * 16 * 32
    omega)

/-- Block `block` of the flat padded-bit vector, as a 16-word variable block. -/
def paddedBlock
    (padded : Var SHA256PaddedBits (F p))
    (block : Fin paddedBlocksLen) : Var SHA256Block (F p) :=
  Vector.ofFn fun word => Vector.ofFn fun bit => paddedBit padded block word bit

/-- The 32-bit word of the flat padded-bit vector containing padded byte `j`. -/
def paddedWord
    (padded : Var SHA256PaddedBits (F p))
    (j : Fin paddedBytesLen) : Var (fields 32) (F p) :=
  Vector.ofFn fun (bit : Fin 32) =>
    padded[j.val / 64 * 512 + j.val % 64 / 4 * 32 + bit.val]'(by
      have hj := j.isLt
      have hb := bit.isLt
      simp only [paddedBytesLen, paddedBlocksLen] at hj
      change _ < 5 * 16 * 32
      omega)

/-- The expected padded byte at position `j` as an expression: a
`lenFlags`-weighted sum over all possible message lengths.

This is written in **factored** form so the asserted constraint is a single R1CS
row even when `message` is a vector of input *variables*. The naive form
`∑ lenFlags[len] · (message[j] or const)` multiplies the one-hot selector by the
message in every summand, which the syntactic single-row check (`isR1CSRow`)
rejects as a rank-2+ product. Here the message contribution is pulled out as one
genuine product `message[j] · (∑_{len > j} lenFlags[len])`, leaving a constant
part that is purely affine:

* `constPart` collects the padding-constant contributions (lengths `len ≤ j`);
* the message term is `message[j]` times the one-hot mass on lengths `len > j`.

By `OneHotAt` the coefficient sum evaluates to `1` exactly when `j < ℓ`, so this
agrees value-for-value with the naive definition (see `eval_expectedPaddedByte`). -/
def expectedPaddedByte
    (message : Var (fields inputBufferLen) (F p))
    (lenFlags : Var (fields inputBufferLen) (F p))
    (j : Fin paddedBytesLen) : Expression (F p) :=
  (Fin.foldl inputBufferLen
    (fun acc len =>
      acc + lenFlags[len] *
        (if j.val < len.val then 0 else ((specPaddedByteConst len.val j.val : ℕ) : F p)))
    0)
  + (if h : j.val < inputBufferLen then message[j.val]'h else 0) *
      (Fin.foldl inputBufferLen
        (fun acc len => acc + (if j.val < len.val then lenFlags[len] else 0))
        0)

/-- Select the entry of `states` holding the digest for a `len`-byte message:
the state after `numBlocksForLen len` compressions. Generic over the state
representation so it can be used both at the variable and at the value level. -/
def stateForLen {α : Type} (states : Vector α paddedBlocksLen) (len : ℕ) : α :=
  match numBlocksForLen len with
  | 1 => states[0]
  | 2 => states[1]
  | 3 => states[2]
  | 4 => states[3]
  | _ => states[4]

/-!
## Witness values
-/

/-- The one-hot length-flag witness values for message length `len`. -/
def lenFlagsValue (len : ℕ) : Vector (F p) inputBufferLen :=
  Vector.ofFn fun k => if k.val = len then 1 else 0

/-- The padded-bit witness values for message bytes `msg` truncated at `len`:
bit `i % 8` of padded byte `i/512 * 64 + i % 512 / 32 * 4 + (3 - i % 32 / 8)`. -/
def paddedBitsValue (msg : Vector ℕ inputBufferLen) (len : ℕ) :
    Vector (F p) paddedBitsLen :=
  Vector.ofFn fun i =>
    let byteIdx := i.val / 512 * 64 + i.val % 512 / 32 * 4 + (3 - i.val % 32 / 8)
    ((specPaddedByte msg len byteIdx / 2 ^ (i.val % 8) % 2 : ℕ) : F p)

end Solution.SHA256
end
