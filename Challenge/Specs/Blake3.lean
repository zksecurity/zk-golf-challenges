import Clean.Utils.Bitwise
import Clean.Utils.Vector
import Mathlib.Data.Nat.Log

namespace Specs.Blake3

/-
  The BLAKE3 hash function, following the official specification "BLAKE3: one
  function, fast everywhere" (O'Connor, Aumasson, Neves, Wilcox-O'Hearn,
  revision of 2021-10-29), Sections 2.1-2.7, and matching the reference
  implementation in the BLAKE3 repository (reference_impl/reference_impl.rs).

  Words are 32 bits wide and every byte encoding is little-endian. The
  message is split into 1024-byte chunks; each chunk is compressed 64-byte
  block by 64-byte block into an 8-word chaining value, and the chunk
  chaining values are the leaves of a binary tree whose parent nodes are
  compressed pairwise up to a root node. The digest is squeezed from the
  root compression, 64 bytes per output block counter value, which makes the
  output extendable (XOF); the default digest is the first 32 bytes.

  The three modes (hash, keyed_hash, derive_key) differ only in the key
  words and the domain-separation flags passed to `keyedHashBytes`.
-/

-- Initial value: the same constants as SHA-256's H0 (first 32 bits of the
-- fractional parts of the square roots of the first 8 primes).
def iv : Vector ℕ 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

-- Domain-separation flags (spec Table 3).
@[reducible] def chunkStart : ℕ := 0x01
@[reducible] def chunkEnd : ℕ := 0x02
@[reducible] def parent : ℕ := 0x04
@[reducible] def root : ℕ := 0x08
@[reducible] def keyedHash : ℕ := 0x10
@[reducible] def deriveKeyContext : ℕ := 0x20
@[reducible] def deriveKeyMaterial : ℕ := 0x40

/--
  The quarter-round function `g` (spec Section 2.2): mix message words
  `mx, my` into the state entries at positions `a, b, c, d`.
-/
def g (v : Vector ℕ 16) (a b c d : Fin 16) (mx my : ℕ) : Vector ℕ 16 :=
  let va := add32 (add32 v[a.val] v[b.val]) mx
  let vd := rotRight32 (v[d.val] ^^^ va) 16
  let vc := add32 v[c.val] vd
  let vb := rotRight32 (v[b.val] ^^^ vc) 12
  let va := add32 (add32 va vb) my
  let vd := rotRight32 (vd ^^^ va) 8
  let vc := add32 vc vd
  let vb := rotRight32 (vb ^^^ vc) 7
  ((((v.set a.val va).set b.val vb).set c.val vc).set d.val vd)

-- One round (spec Section 2.2): `g` down the four columns of the 4×4 state,
-- then down the four diagonals, consuming the 16 message words in order.
def roundFn (v m : Vector ℕ 16) : Vector ℕ 16 :=
  let v := g v 0 4 8 12 m[0] m[1]
  let v := g v 1 5 9 13 m[2] m[3]
  let v := g v 2 6 10 14 m[4] m[5]
  let v := g v 3 7 11 15 m[6] m[7]
  let v := g v 0 5 10 15 m[8] m[9]
  let v := g v 1 6 11 12 m[10] m[11]
  let v := g v 2 7 8 13 m[12] m[13]
  g v 3 4 9 14 m[14] m[15]

-- The message word permutation applied between rounds (spec Table 1): word
-- i of the next round's message block is word σ(i) of the current one, with
-- σ = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8].
def permute (m : Vector ℕ 16) : Vector ℕ 16 :=
  #v[m[2], m[6], m[3], m[10], m[7], m[0], m[4], m[13],
     m[1], m[11], m[12], m[5], m[9], m[14], m[15], m[8]]

/--
  The compression function (spec Section 2.2): compress the 16-word message
  `block` into the 8-word chaining value `cv` under the 64-bit counter `t`,
  the block byte-length `len`, and the domain flags `flags`. Seven rounds
  are applied to the 16-word state, permuting the message words between
  rounds, and the state is folded in half by XOR. All 16 output words are
  returned: the first 8 are the new chaining value, and the extended output
  uses all 16.
-/
def compress (cv : Vector ℕ 8) (block : Vector ℕ 16) (t len flags : ℕ) :
    Vector ℕ 16 :=
  let state : Vector ℕ 16 := #v[
    cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
    iv[0], iv[1], iv[2], iv[3],
    t % 2 ^ 32, t / 2 ^ 32 % 2 ^ 32, len, flags
  ]
  let v := (Fin.foldl 7 (fun (vm : Vector ℕ 16 × Vector ℕ 16) _ =>
    (roundFn vm.1 vm.2, permute vm.2)) (state, block)).1
  Vector.ofFn fun i =>
    if h : i.val < 8 then
      v[i.val] ^^^ v[i.val + 8]
    else
      v[i.val] ^^^ cv[i.val - 8]

/-- The first 8 words of a compression: the updated chaining value. -/
def compressCV (cv : Vector ℕ 8) (block : Vector ℕ 16) (t len flags : ℕ) :
    Vector ℕ 8 :=
  let v := compress cv block t len flags
  Vector.ofFn fun i => v[i.val]'(by omega)

/-- Pack a bit string into `n` 32-bit words: bit `32·i + j` of the string is
    bit `j` of word `i`. -/
def bitsToWords (n : ℕ) (s : Vector ℕ (32 * n)) : Vector ℕ n :=
  Vector.ofFn fun i =>
    Fin.foldl 32 (fun acc (j : Fin 32) =>
      acc + s[32 * i.val + j.val]'(by omega) * 2 ^ j.val) 0

/-- Unpack `n` 32-bit words into a bit string: bit `32·i + j` of the string
    is bit `j` of word `i` (so the bit string is also the little-endian bit
    serialization of the words' byte string, with bit `8·k + b` holding bit
    `b` of byte `k`). -/
def wordsToBits {n : ℕ} (words : Vector ℕ n) : Vector ℕ (32 * n) :=
  Vector.ofFn fun i => words[i.val / 32]'(by omega) / 2 ^ (i.val % 32) % 2

/--
  The compression function on raw bits: the 28 input words — the 8-word
  chaining value, the 16-word message block, the two 32-bit counter halves
  (low first), the block byte-length, and the flags — packed into 896 bits,
  and the 16 output words unpacked into 512 bits, both with bit `32·i + j`
  of the string holding bit `j` of word `i`.
-/
def compressBits (input : Vector ℕ 896) : Vector ℕ 512 :=
  let w := bitsToWords 28 input
  wordsToBits (compress
    (Vector.ofFn fun i : Fin 8 => w[i.val]'(by omega))
    (Vector.ofFn fun i : Fin 16 => w[i.val + 8]'(by omega))
    (w[24] + 2 ^ 32 * w[25]) w[26] w[27])

/-- Little-endian 32-bit word `i` of a byte string, reading bytes past the
    end as zero (short blocks are zero-padded). -/
def wordAt (bytes : List ℕ) (i : ℕ) : ℕ :=
  bytes.getD (4 * i) 0 + bytes.getD (4 * i + 1) 0 * 2 ^ 8 +
    bytes.getD (4 * i + 2) 0 * 2 ^ 16 + bytes.getD (4 * i + 3) 0 * 2 ^ 24

/-- Parse up to 64 bytes into a block of 16 little-endian 32-bit words. -/
def bytesToBlock (bytes : List ℕ) : Vector ℕ 16 :=
  Vector.ofFn fun i => wordAt bytes i.val

/--
  A node of the hash tree just before its final compression: the last block
  of a chunk, or a parent node (spec Section 2.6). Keeping the node in this
  pre-compression form is what allows the root node to be compressed once
  per output block counter value for the extended output.
-/
structure Output where
  inputCV : Vector ℕ 8
  block : Vector ℕ 16
  counter : ℕ
  blockLen : ℕ
  flags : ℕ
deriving DecidableEq

/-- The chaining value of a non-root node. -/
def chainingValue (o : Output) : Vector ℕ 8 :=
  compressCV o.inputCV o.block o.counter o.blockLen o.flags

/-- The number of 64-byte blocks in a chunk of `len ≤ 1024` bytes; the empty
    chunk still consists of one (zero-length) block. -/
def numBlocks (len : ℕ) : ℕ := max 1 ((len + 63) / 64)

/--
  The pre-compression output node of chunk number `t` holding the bytes `d`
  (at most 1024 of them), under `key` and mode flags `flags` (spec Section
  2.3). All blocks of the chunk are compressed with the chunk number as the
  counter; the first block carries `chunkStart`, the last carries
  `chunkEnd`, and a short or empty final block is zero-padded while its real
  byte length is passed to the compression.
-/
def chunkOutput (key : Vector ℕ 8) (flags t : ℕ) (d : List ℕ) : Output :=
  let n := numBlocks d.length
  let cv := Fin.foldl (n - 1) (fun cv (i : Fin (n - 1)) =>
    compressCV cv (bytesToBlock ((d.drop (64 * i.val)).take 64)) t 64
      (flags ||| (if i.val = 0 then chunkStart else 0))) key
  { inputCV := cv
    block := bytesToBlock (d.drop (64 * (n - 1)))
    counter := t
    blockLen := d.length - 64 * (n - 1)
    flags := flags ||| (if n = 1 then chunkStart else 0) ||| chunkEnd }

/--
  The pre-compression output node of a parent over the child chaining
  values `l` and `r` (spec Section 2.4): its block is the two concatenated
  chaining values, its counter is 0, and its length is a full 64-byte block.
-/
def parentOutput (key : Vector ℕ 8) (flags : ℕ) (l r : Vector ℕ 8) : Output :=
  { inputCV := key
    block := l ++ r
    counter := 0
    blockLen := 64
    flags := flags ||| parent }

/-- The number of 1024-byte chunks of a message of `len` bytes; the empty
    message still consists of one (empty) chunk. -/
def numChunks (len : ℕ) : ℕ := max 1 ((len + 1023) / 1024)

/-- The number of chunks in the left subtree of a tree of `n ≥ 2` chunks:
    the largest power of two strictly smaller than `n` (spec Section 2.1). -/
def leftChunks (n : ℕ) : ℕ := 2 ^ Nat.log 2 (n - 1)

/-- The number of bytes in the left subtree of a message of `len > 1024`
    bytes: 1024 for each of its `leftChunks` full chunks. -/
def leftLen (len : ℕ) : ℕ := 1024 * leftChunks (numChunks len)

theorem leftLen_pos_lt {len : ℕ} (h : 1024 < len) :
    0 < leftLen len ∧ leftLen len < len := by
  have hp : 2 ^ Nat.log 2 (numChunks len - 1) ≤ numChunks len - 1 :=
    Nat.pow_log_le_self 2 (by simp only [numChunks]; omega)
  have h2 : 0 < 2 ^ Nat.log 2 (numChunks len - 1) := Nat.two_pow_pos _
  simp only [leftLen, leftChunks, numChunks] at *
  omega

/--
  The pre-compression output node at the top of the subtree hashing the
  bytes `d`, whose leftmost chunk is chunk number `t` (spec Section 2.1): a
  single chunk if `d` fits in one, and otherwise a parent node whose left
  subtree covers the largest power-of-two number of chunks strictly smaller
  than the total (so the left subtree is always complete).
-/
def subtreeOutput (key : Vector ℕ 8) (flags t : ℕ) (d : List ℕ) : Output :=
  if _h : d.length ≤ 1024 then
    chunkOutput key flags t d
  else
    parentOutput key flags
      (chainingValue (subtreeOutput key flags t (d.take (leftLen d.length))))
      (chainingValue (subtreeOutput key flags
        (t + leftChunks (numChunks d.length)) (d.drop (leftLen d.length))))
termination_by d.length
decreasing_by
  · have hb := leftLen_pos_lt (len := d.length) (by omega)
    simp only [List.length_take]
    omega
  · have hb := leftLen_pos_lt (len := d.length) (by omega)
    simp only [List.length_drop]
    omega

/--
  The extended output (spec Section 2.6): `outLen` bytes squeezed from the
  root node `o` by compressing it once per 64-byte output block, with the
  output block index as the counter and the `root` flag set. Output words
  are serialized as little-endian bytes.
-/
def rootOutputBytes (o : Output) (outLen : ℕ) : Vector ℕ outLen :=
  Vector.ofFn fun i =>
    (compress o.inputCV o.block (i.val / 64) o.blockLen
        (o.flags ||| root))[i.val % 64 / 4]'(by omega)
      / 2 ^ (8 * (i.val % 4)) % 2 ^ 8

/-- Hash `msg` under the 8 `key` words and mode `flags` into `outLen` bytes. -/
def keyedHashBytes (key : Vector ℕ 8) (flags : ℕ) (msg : List ℕ)
    (outLen : ℕ) : Vector ℕ outLen :=
  rootOutputBytes (subtreeOutput key flags 0 msg) outLen

/-- The 8 little-endian key words of a 32-byte key (spec Section 2.5). -/
def keyWords (key : Vector ℕ 32) : Vector ℕ 8 :=
  Vector.ofFn fun i => wordAt key.toList i.val

/-- BLAKE3 in hash mode with extended output: the first `outLen` bytes of
    the XOF of message `msg`. -/
def blake3Xof {len : ℕ} (msg : Vector ℕ len) (outLen : ℕ) : Vector ℕ outLen :=
  keyedHashBytes iv 0 msg.toList outLen

/-- BLAKE3 in hash mode: the default 32-byte digest. -/
def blake3 {len : ℕ} (msg : Vector ℕ len) : Vector ℕ 32 :=
  blake3Xof msg 32

/-- BLAKE3 in keyed_hash mode: `outLen` output bytes keyed by the 32-byte
    `key` (spec Section 2.5). -/
def blake3Keyed {len : ℕ} (key : Vector ℕ 32) (msg : Vector ℕ len)
    (outLen : ℕ) : Vector ℕ outLen :=
  keyedHashBytes (keyWords key) keyedHash msg.toList outLen

/-- BLAKE3 in derive_key mode (spec Section 2.7): hash the `context` string
    in derive_key_context mode into a 32-byte context key, then hash the key
    `material` in derive_key_material mode keyed by the context key. -/
def blake3DeriveKey {ctxLen mLen : ℕ} (context : Vector ℕ ctxLen)
    (material : Vector ℕ mLen) (outLen : ℕ) : Vector ℕ outLen :=
  let contextKey := keyedHashBytes iv deriveKeyContext context.toList 32
  keyedHashBytes (keyWords contextKey) deriveKeyMaterial material.toList outLen

/--
  A bit string represented as a vector of natural numbers.
-/
@[reducible] def IsBitString {n : ℕ} (xs : Vector ℕ n) : Prop :=
  ∀ i : Fin n, xs[i] < 2

def CompressAssumptions (input : Vector ℕ 896) : Prop :=
  -- input is a bit string
  IsBitString input

def CompressSpec (input : Vector ℕ 896) (output : Vector ℕ 512) : Prop :=
  output = compressBits input

end Specs.Blake3
