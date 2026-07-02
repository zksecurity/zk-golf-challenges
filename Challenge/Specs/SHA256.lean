import Clean.Utils.Bitwise
import Clean.Utils.Vector

namespace Specs.SHA256

-- Round constants: first 32 bits of the fractional parts of cube roots of first 64 primes
def K : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

-- Initial hash values: first 32 bits of fractional parts of square roots of first 8 primes
def H0 : Vector ℕ 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

def not32 (a : ℕ) : ℕ := a ^^^ 0xffffffff

-- σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)
def lowerSigma0 (x : ℕ) : ℕ := rotRight32 x 7 ^^^ rotRight32 x 18 ^^^ (x / 2^3)

-- σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)
def lowerSigma1 (x : ℕ) : ℕ := rotRight32 x 17 ^^^ rotRight32 x 19 ^^^ (x / 2^10)

-- Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x)
def upperSigma0 (x : ℕ) : ℕ := rotRight32 x 2 ^^^ rotRight32 x 13 ^^^ rotRight32 x 22

-- Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x)
def upperSigma1 (x : ℕ) : ℕ := rotRight32 x 6 ^^^ rotRight32 x 11 ^^^ rotRight32 x 25

def Ch (e f g : ℕ) : ℕ := (e &&& f) ^^^ (not32 e &&& g)

def Maj (a b c : ℕ) : ℕ := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

-- One round of the SHA-256 compression function
-- state = [a, b, c, d, e, f, g, h]
def sha256Round (state : Vector ℕ 8) (k w : ℕ) : Vector ℕ 8 :=
  let a := state[0]; let b := state[1]; let c := state[2]; let d := state[3]
  let e := state[4]; let f := state[5]; let g := state[6]; let h := state[7]
  let t1 := add32 (add32 (add32 (add32 h (upperSigma1 e)) (Ch e f g)) k) w
  let t2 := add32 (upperSigma0 a) (Maj a b c)
  #v[add32 t1 t2, a, b, c, add32 d t1, e, f, g]

-- Expand a 16-word block into a 64-word message schedule
def messageSchedule (block : Vector ℕ 16) : Vector ℕ 64 :=
  let init : Vector ℕ 64 := Vector.mapFinRange 64 fun i =>
    if h : i.val < 16 then block.get ⟨i.val, h⟩ else 0
  Fin.foldl 48 (fun w (i : Fin 48) =>
    let j := i.val + 16
    let wj := add32 (add32 (lowerSigma1 w[j - 2])  w[j - 7])
                    (add32 (lowerSigma0 w[j - 15]) w[j - 16])
    have hj   : j     < 64 := by omega
    w.set (⟨j, hj⟩ : Fin 64) wj) init

-- Apply 64 rounds of SHA-256 to the state using the message schedule
def sha256Compress (state : Vector ℕ 8) (w : Vector ℕ 64) : Vector ℕ 8 :=
  Fin.foldl 64 (fun s i => sha256Round s K[i].toNat w[i]) state

-- Process one 512-bit block (16 big-endian 32-bit words)
def compressBlock (state : Vector ℕ 8) (block : Vector ℕ 16) : Vector ℕ 8 :=
  let w := messageSchedule block
  let state' := sha256Compress state w
  Vector.mapFinRange 8 fun i => add32 state[i] state'[i]

-- Parse 4 bytes in big-endian order into a 32-bit word
def bytesToWord32BE (b0 b1 b2 b3 : ℕ) : ℕ :=
  b0 * 2^24 + b1 * 2^16 + b2 * 2^8 + b3

-- Parse 64 bytes into a block of 16 big-endian 32-bit words
def bytesToBlock (bytes : Vector ℕ 64) : Vector ℕ 16 :=
  Vector.mapFinRange 16 fun (i : Fin 16) =>
    bytesToWord32BE bytes[4 * i.val] bytes[4 * i.val + 1]
      bytes[4 * i.val + 2] bytes[4 * i.val + 3]

-- SHA-256 padding (FIPS 180-4):
--   append 0x80, then zeros until message length ≡ 56 (mod 64) bytes,
--   then the original bit length as a big-endian 64-bit integer
def pad {len : ℕ} (msg : Vector ℕ len) :
    Vector (Vector ℕ 16) ((len + (55 + 64 - len % 64) % 64 + 9) / 64) :=
  let bitLen := len * 8
  let zeros  := (55 + 64 - len % 64) % 64
  let numBlocks := (len + zeros + 9) / 64
  let totalLen := numBlocks * 64
  let padded : Vector ℕ totalLen := Vector.mapFinRange totalLen fun i =>
    if h : i.val < len then
      msg[i.val]
    else if i.val = len then
      0x80
    else if i.val < totalLen - 8 then
      0
    else
      bitLen / 2 ^ (8 * (totalLen - 1 - i.val)) % 256
  (padded.toChunks ⟨64, by decide⟩).map bytesToBlock

def sha256 {len : ℕ} (msg : Vector ℕ len) : Vector ℕ 8 :=
  (pad msg).foldl compressBlock H0

/--
  Truncate a buffer to the first `len` bytes.
-/
def truncate {bufferLen : ℕ} (input : Vector ℕ bufferLen) (len : ℕ)
    (h : len ≤ bufferLen) : Vector ℕ len :=
  Vector.ofFn fun i => input[i.val]'(Nat.lt_of_lt_of_le i.isLt h)


/--
  An octet string represented as a vector of natural numbers.
-/
@[reducible] def IsByteArray {n : ℕ} (xs : Vector ℕ n) : Prop :=
  ∀ i : Fin n, xs[i] < 256


def Assumptions {bufferLen : ℕ}
    (input : Vector ℕ bufferLen)
    (len : ℕ) : Prop :=
  -- input is a byte string
  IsByteArray input ∧

  -- the data length is less than the buffer length
  len < bufferLen


def Spec {bufferLen : ℕ}
    (input : Vector ℕ bufferLen) (len : ℕ)
    (output: Vector ℕ 8) : Prop :=
  if h : len ≤ bufferLen then
    let truncated := truncate input len h
    output = sha256 truncated
  else
    False

end Specs.SHA256
