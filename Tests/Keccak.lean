import Challenge.Specs.Keccak

namespace Specs.Keccak.Tests

/-
  Test vectors from several independent sources:

  * The Keccak team's reference test suite (XKCP):
    https://github.com/XKCP/XKCP, tests/TestVectors/
    KeccakF-{200,400,800,1600}-IntermediateValues.txt. Those files list, for
    each width, the round constants, the ρ offsets, and every intermediate
    state of Keccak-f applied to the all-zero state and then once more to its
    output. (The once-permuted zero state is also pinned by independent
    implementations, e.g. cloudflare/circl, simd/keccakf1600/f1600x_test.go.)

  * NIST FIPS 202 example digests: SHA3-224/256/384/512 and SHAKE128 of the
    empty message, and SHA3-256 of "abc", absorb a single padded block, so
    each digest checks one Keccak-f[1600] call on a nonzero input.

  * The Keccak-256 hash of the empty string (legacy 0x01 padding), the
    constant replicated by every Ethereum client.

  All state literals below use the spec's lane order: index x + 5·y, rows are
  y = 0, ..., 4.
-/

def zeroState : Vector ℕ 25 := Vector.replicate 25 0

-- Round constants. The generating definition from The Keccak Reference,
-- Section 1.2: rc(t) is the constant coefficient of x^t mod
-- x⁸ + x⁶ + x⁵ + x⁴ + 1 over GF(2), and bit 2^j − 1 of RC[i] is rc(j + 7i)
-- for 0 ≤ j ≤ ℓ.

/-- Multiply a bit-packed GF(2) polynomial by x, modulo x⁸ + x⁶ + x⁵ + x⁴ + 1. -/
def lfsrStep (p : ℕ) : ℕ :=
  let p := 2 * p
  if p < 2 ^ 8 then p else p ^^^ 0x171

/-- x^t mod x⁸ + x⁶ + x⁵ + x⁴ + 1, bit-packed. -/
def lfsrPow : ℕ → ℕ
  | 0 => 1
  | t + 1 => lfsrStep (lfsrPow t)

/-- rc(t): the constant coefficient of x^t mod x⁸ + x⁶ + x⁵ + x⁴ + 1. -/
def rcBit (t : ℕ) : ℕ := lfsrPow t % 2

/-- RC[i] for lane width 2^ℓ, generated from the LFSR sequence. -/
def roundConstantOfLFSR (l i : ℕ) : ℕ :=
  Fin.foldl (l + 1) (fun acc (j : Fin (l + 1)) => acc + rcBit (j.val + 7 * i) * 2 ^ (2 ^ j.val - 1)) 0

-- The start of the LFSR sequence: x^t mod x⁸ + x⁶ + x⁵ + x⁴ + 1 is x^t itself
-- for t < 8, so rc(1), ..., rc(7) are 0, and the first feedback gives
-- x⁸ ≡ x⁶ + x⁵ + x⁴ + 1, so rc(8) = 1.
example :
    (Vector.ofFn fun t : Fin 16 => rcBit t.val) =
      #v[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1] := by
  native_decide

-- The LFSR polynomial is primitive, so the sequence has period 255.
example : lfsrPow 255 = 1 := by native_decide

-- The spec's 64-bit table is exactly the LFSR-generated sequence at ℓ = 6.
example : (Vector.ofFn fun i : Fin 24 => roundConstantOfLFSR 6 i.val) = roundConstants := by
  native_decide

-- Official per-width round-constant tables (XKCP). Keccak-f[25 · 2^ℓ] uses the
-- first 12 + 2ℓ entries; for w < 64 they are the 64-bit constants mod 2^w.

def rc200Official : Vector ℕ 18 := #v[
  0x01, 0x82, 0x8a, 0x00, 0x8b, 0x01, 0x81, 0x09, 0x8a,
  0x88, 0x09, 0x0a, 0x8b, 0x8b, 0x89, 0x03, 0x02, 0x80
]

def rc400Official : Vector ℕ 20 := #v[
  0x0001, 0x8082, 0x808a, 0x8000, 0x808b, 0x0001, 0x8081, 0x8009, 0x008a, 0x0088,
  0x8009, 0x000a, 0x808b, 0x008b, 0x8089, 0x8003, 0x8002, 0x0080, 0x800a, 0x000a
]

def rc800Official : Vector ℕ 22 := #v[
  0x00000001, 0x00008082, 0x0000808a, 0x80008000, 0x0000808b, 0x80000001,
  0x80008081, 0x00008009, 0x0000008a, 0x00000088, 0x80008009, 0x8000000a,
  0x8000808b, 0x0000008b, 0x00008089, 0x00008003, 0x00008002, 0x00000080,
  0x0000800a, 0x8000000a, 0x80008081, 0x00008080
]

example : (Vector.ofFn fun i : Fin 18 => roundConstants[i.val] % 2 ^ 8) = rc200Official := by
  native_decide

example : (Vector.ofFn fun i : Fin 20 => roundConstants[i.val] % 2 ^ 16) = rc400Official := by
  native_decide

example : (Vector.ofFn fun i : Fin 22 => roundConstants[i.val] % 2 ^ 32) = rc800Official := by
  native_decide

-- The LFSR generation at smaller ℓ agrees with truncating the 64-bit constants.
example : (Vector.ofFn fun i : Fin 18 => roundConstantOfLFSR 3 i.val) = rc200Official := by
  native_decide

example : (Vector.ofFn fun i : Fin 20 => roundConstantOfLFSR 4 i.val) = rc400Official := by
  native_decide

example : (Vector.ofFn fun i : Fin 22 => roundConstantOfLFSR 5 i.val) = rc800Official := by
  native_decide

-- ρ offsets.

/--
  The ρ offsets via the recurrence of The Keccak Reference, Section 1.2:
  r[0,0] = 0 and, walking (x, y) ← (y, 2x + 3y) from (1, 0),
  r[x,y] = (t+1)(t+2)/2 at step t.
-/
def rhoOffsetsOfRecurrence : Vector ℕ 25 :=
  (Fin.foldl 24 (fun (acc : Vector ℕ 25 × ℕ × ℕ) (t : Fin 24) =>
      let (r, x, y) := acc
      (r.setIfInBounds (x + 5 * y) ((t.val + 1) * (t.val + 2) / 2), y, (2 * x + 3 * y) % 5))
    (Vector.replicate 25 0, 1, 0)).1

example : rhoOffsetsOfRecurrence = rhoOffsets := by native_decide

-- Official reduced offset tables (XKCP): the spec's unreduced offsets mod w.

def rhoOffsetsMod64Official : Vector ℕ 25 := #v[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14
]

def rhoOffsetsMod8Official : Vector ℕ 25 := #v[
  0, 1, 6, 4, 3,
  4, 4, 6, 7, 4,
  3, 2, 3, 1, 7,
  1, 5, 7, 5, 0,
  2, 2, 5, 0, 6
]

example : (Vector.ofFn fun i : Fin 25 => rhoOffsets[i] % 64) = rhoOffsetsMod64Official := by
  native_decide

example : (Vector.ofFn fun i : Fin 25 => rhoOffsets[i] % 8) = rhoOffsetsMod8Official := by
  native_decide

-- rotLeft and notLane unit tests.

example : rotLeft 64 1 1 = 2 := by native_decide
example : rotLeft 64 0x8000000000000000 1 = 1 := by native_decide
example : rotLeft 64 1 0 = 1 := by native_decide
-- offsets are reduced mod w
example : rotLeft 64 1 64 = 1 := by native_decide
example : rotLeft 64 0xf1258f7940e1dde7 0 = 0xf1258f7940e1dde7 := by native_decide
example : rotLeft 8 0x81 1 = 0x03 := by native_decide
example : rotLeft 8 0x81 7 = 0xc0 := by native_decide
example : rotLeft 16 0x8001 4 = 0x0018 := by native_decide
-- every rotation of a 1-bit lane is the identity
example : rotLeft 1 1 3 = 1 := by native_decide
-- rotations compose: 13 + 51 = 64 restores a 64-bit lane
example : rotLeft 64 (rotLeft 64 0xf1258f7940e1dde7 13) 51 = 0xf1258f7940e1dde7 := by
  native_decide

example : notLane 64 0 = 0xffffffffffffffff := by native_decide
example : notLane 64 0xffffffffffffffff = 0 := by native_decide
example : notLane 64 0xf1258f7940e1dde7 = 0x0eda7086bf1e2218 := by native_decide
example : notLane 8 0xf0 = 0x0f := by native_decide
example : notLane 1 0 = 1 := by native_decide
example : notLane 1 1 = 0 := by native_decide

-- Round 0 on the all-zero state: θ, ρ, π, χ all fix zero and ι injects RC[0].
example : theta 64 zeroState = zeroState := by native_decide
example : rho 64 zeroState = zeroState := by native_decide
example : pi zeroState = zeroState := by native_decide
example : chi 64 zeroState = zeroState := by native_decide
example : iota 0x0000000000000001 zeroState = zeroState.set 0 1 := by native_decide

-- The state entering round 1 (after round 0 on all-zero); the same for every
-- width, since RC[0] mod 2^w = 1.
def afterRound0 : Vector ℕ 25 := zeroState.set 0 1

-- Keccak-f[1600] round 1, step by step (XKCP intermediate values).

def f1600Round1Theta : Vector ℕ 25 := #v[
  0x0000000000000001, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000002,
  0x0000000000000000, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000002,
  0x0000000000000000, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000002,
  0x0000000000000000, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000002,
  0x0000000000000000, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000002
]

def f1600Round1Rho : Vector ℕ 25 := #v[
  0x0000000000000001, 0x0000000000000002, 0x0000000000000000, 0x0000000000000000, 0x0000000010000000,
  0x0000000000000000, 0x0000100000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000200000,
  0x0000000000000000, 0x0000000000000400, 0x0000000000000000, 0x0000000000000000, 0x0000010000000000,
  0x0000000000000000, 0x0000200000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000200,
  0x0000000000000000, 0x0000000000000004, 0x0000000000000000, 0x0000000000000000, 0x0000000000008000
]

def f1600Round1Pi : Vector ℕ 25 := #v[
  0x0000000000000001, 0x0000100000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000008000,
  0x0000000000000000, 0x0000000000200000, 0x0000000000000000, 0x0000200000000000, 0x0000000000000000,
  0x0000000000000002, 0x0000000000000000, 0x0000000000000000, 0x0000000000000200, 0x0000000000000000,
  0x0000000010000000, 0x0000000000000000, 0x0000000000000400, 0x0000000000000000, 0x0000000000000000,
  0x0000000000000000, 0x0000000000000000, 0x0000010000000000, 0x0000000000000000, 0x0000000000000004
]

def f1600Round1Chi : Vector ℕ 25 := #v[
  0x0000000000000001, 0x0000100000000000, 0x0000000000008000, 0x0000000000000001, 0x0000100000008000,
  0x0000000000000000, 0x0000200000200000, 0x0000000000000000, 0x0000200000000000, 0x0000000000200000,
  0x0000000000000002, 0x0000000000000200, 0x0000000000000000, 0x0000000000000202, 0x0000000000000000,
  0x0000000010000400, 0x0000000000000000, 0x0000000000000400, 0x0000000010000000, 0x0000000000000000,
  0x0000010000000000, 0x0000000000000000, 0x0000010000000004, 0x0000000000000000, 0x0000000000000004
]

def f1600Round1Iota : Vector ℕ 25 := #v[
  0x0000000000008083, 0x0000100000000000, 0x0000000000008000, 0x0000000000000001, 0x0000100000008000,
  0x0000000000000000, 0x0000200000200000, 0x0000000000000000, 0x0000200000000000, 0x0000000000200000,
  0x0000000000000002, 0x0000000000000200, 0x0000000000000000, 0x0000000000000202, 0x0000000000000000,
  0x0000000010000400, 0x0000000000000000, 0x0000000000000400, 0x0000000010000000, 0x0000000000000000,
  0x0000010000000000, 0x0000000000000000, 0x0000010000000004, 0x0000000000000000, 0x0000000000000004
]

example : theta 64 afterRound0 = f1600Round1Theta := by native_decide
example : rho 64 f1600Round1Theta = f1600Round1Rho := by native_decide
example : pi f1600Round1Rho = f1600Round1Pi := by native_decide
example : chi 64 f1600Round1Pi = f1600Round1Chi := by native_decide
example : iota 0x0000000000008082 f1600Round1Chi = f1600Round1Iota := by native_decide

-- A whole round at once: round 1 is R with RC[1] on the round-0 output.
example : keccakRound 64 0x0000000000008082 afterRound0 = f1600Round1Iota := by native_decide

-- Keccak-f[200] round 1, step by step (XKCP intermediate values).

def f200Round1Theta : Vector ℕ 25 := #v[
  0x01, 0x01, 0x00, 0x00, 0x02,
  0x00, 0x01, 0x00, 0x00, 0x02,
  0x00, 0x01, 0x00, 0x00, 0x02,
  0x00, 0x01, 0x00, 0x00, 0x02,
  0x00, 0x01, 0x00, 0x00, 0x02
]

def f200Round1Rho : Vector ℕ 25 := #v[
  0x01, 0x02, 0x00, 0x00, 0x10,
  0x00, 0x10, 0x00, 0x00, 0x20,
  0x00, 0x04, 0x00, 0x00, 0x01,
  0x00, 0x20, 0x00, 0x00, 0x02,
  0x00, 0x04, 0x00, 0x00, 0x80
]

def f200Round1Pi : Vector ℕ 25 := #v[
  0x01, 0x10, 0x00, 0x00, 0x80,
  0x00, 0x20, 0x00, 0x20, 0x00,
  0x02, 0x00, 0x00, 0x02, 0x00,
  0x10, 0x00, 0x04, 0x00, 0x00,
  0x00, 0x00, 0x01, 0x00, 0x04
]

def f200Round1Chi : Vector ℕ 25 := #v[
  0x01, 0x10, 0x80, 0x01, 0x90,
  0x00, 0x00, 0x00, 0x20, 0x20,
  0x02, 0x02, 0x00, 0x00, 0x00,
  0x14, 0x00, 0x04, 0x10, 0x00,
  0x01, 0x00, 0x05, 0x00, 0x04
]

def f200Round1Iota : Vector ℕ 25 := #v[
  0x83, 0x10, 0x80, 0x01, 0x90,
  0x00, 0x00, 0x00, 0x20, 0x20,
  0x02, 0x02, 0x00, 0x00, 0x00,
  0x14, 0x00, 0x04, 0x10, 0x00,
  0x01, 0x00, 0x05, 0x00, 0x04
]

example : theta 8 afterRound0 = f200Round1Theta := by native_decide
example : rho 8 f200Round1Theta = f200Round1Rho := by native_decide
example : pi f200Round1Rho = f200Round1Pi := by native_decide
example : chi 8 f200Round1Pi = f200Round1Chi := by native_decide
example : iota 0x82 f200Round1Chi = f200Round1Iota := by native_decide

example : keccakRound 8 0x82 afterRound0 = f200Round1Iota := by native_decide

-- Keccak-f[400] round 1, step by step (XKCP intermediate values).

def f400Round1Theta : Vector ℕ 25 := #v[
  0x0001, 0x0001, 0x0000, 0x0000, 0x0002,
  0x0000, 0x0001, 0x0000, 0x0000, 0x0002,
  0x0000, 0x0001, 0x0000, 0x0000, 0x0002,
  0x0000, 0x0001, 0x0000, 0x0000, 0x0002,
  0x0000, 0x0001, 0x0000, 0x0000, 0x0002
]

def f400Round1Rho : Vector ℕ 25 := #v[
  0x0001, 0x0002, 0x0000, 0x0000, 0x1000,
  0x0000, 0x1000, 0x0000, 0x0000, 0x0020,
  0x0000, 0x0400, 0x0000, 0x0000, 0x0100,
  0x0000, 0x2000, 0x0000, 0x0000, 0x0200,
  0x0000, 0x0004, 0x0000, 0x0000, 0x8000
]

def f400Round1Pi : Vector ℕ 25 := #v[
  0x0001, 0x1000, 0x0000, 0x0000, 0x8000,
  0x0000, 0x0020, 0x0000, 0x2000, 0x0000,
  0x0002, 0x0000, 0x0000, 0x0200, 0x0000,
  0x1000, 0x0000, 0x0400, 0x0000, 0x0000,
  0x0000, 0x0000, 0x0100, 0x0000, 0x0004
]

def f400Round1Chi : Vector ℕ 25 := #v[
  0x0001, 0x1000, 0x8000, 0x0001, 0x9000,
  0x0000, 0x2020, 0x0000, 0x2000, 0x0020,
  0x0002, 0x0200, 0x0000, 0x0202, 0x0000,
  0x1400, 0x0000, 0x0400, 0x1000, 0x0000,
  0x0100, 0x0000, 0x0104, 0x0000, 0x0004
]

def f400Round1Iota : Vector ℕ 25 := #v[
  0x8083, 0x1000, 0x8000, 0x0001, 0x9000,
  0x0000, 0x2020, 0x0000, 0x2000, 0x0020,
  0x0002, 0x0200, 0x0000, 0x0202, 0x0000,
  0x1400, 0x0000, 0x0400, 0x1000, 0x0000,
  0x0100, 0x0000, 0x0104, 0x0000, 0x0004
]

example : theta 16 afterRound0 = f400Round1Theta := by native_decide
example : rho 16 f400Round1Theta = f400Round1Rho := by native_decide
example : pi f400Round1Rho = f400Round1Pi := by native_decide
example : chi 16 f400Round1Pi = f400Round1Chi := by native_decide
example : iota 0x8082 f400Round1Chi = f400Round1Iota := by native_decide

example : keccakRound 16 0x8082 afterRound0 = f400Round1Iota := by native_decide

-- Keccak-f[800] round 1, step by step (XKCP intermediate values).

def f800Round1Theta : Vector ℕ 25 := #v[
  0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000002,
  0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000002,
  0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000002,
  0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000002,
  0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000002
]

def f800Round1Rho : Vector ℕ 25 := #v[
  0x00000001, 0x00000002, 0x00000000, 0x00000000, 0x10000000,
  0x00000000, 0x00001000, 0x00000000, 0x00000000, 0x00200000,
  0x00000000, 0x00000400, 0x00000000, 0x00000000, 0x00000100,
  0x00000000, 0x00002000, 0x00000000, 0x00000000, 0x00000200,
  0x00000000, 0x00000004, 0x00000000, 0x00000000, 0x00008000
]

def f800Round1Pi : Vector ℕ 25 := #v[
  0x00000001, 0x00001000, 0x00000000, 0x00000000, 0x00008000,
  0x00000000, 0x00200000, 0x00000000, 0x00002000, 0x00000000,
  0x00000002, 0x00000000, 0x00000000, 0x00000200, 0x00000000,
  0x10000000, 0x00000000, 0x00000400, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000100, 0x00000000, 0x00000004
]

def f800Round1Chi : Vector ℕ 25 := #v[
  0x00000001, 0x00001000, 0x00008000, 0x00000001, 0x00009000,
  0x00000000, 0x00202000, 0x00000000, 0x00002000, 0x00200000,
  0x00000002, 0x00000200, 0x00000000, 0x00000202, 0x00000000,
  0x10000400, 0x00000000, 0x00000400, 0x10000000, 0x00000000,
  0x00000100, 0x00000000, 0x00000104, 0x00000000, 0x00000004
]

def f800Round1Iota : Vector ℕ 25 := #v[
  0x00008083, 0x00001000, 0x00008000, 0x00000001, 0x00009000,
  0x00000000, 0x00202000, 0x00000000, 0x00002000, 0x00200000,
  0x00000002, 0x00000200, 0x00000000, 0x00000202, 0x00000000,
  0x10000400, 0x00000000, 0x00000400, 0x10000000, 0x00000000,
  0x00000100, 0x00000000, 0x00000104, 0x00000000, 0x00000004
]

example : theta 32 afterRound0 = f800Round1Theta := by native_decide
example : rho 32 f800Round1Theta = f800Round1Rho := by native_decide
example : pi f800Round1Rho = f800Round1Pi := by native_decide
example : chi 32 f800Round1Pi = f800Round1Chi := by native_decide
example : iota 0x00008082 f800Round1Chi = f800Round1Iota := by native_decide

example : keccakRound 32 0x00008082 afterRound0 = f800Round1Iota := by native_decide

-- π on the marker state A[x + 5y] = x + 5y exposes the full lane relocation:
-- lane (x, y) receives lane (x + 3y, x).
example :
    pi (Vector.ofFn fun i => i.val) = #v[
       0,  6, 12, 18, 24,
       3,  9, 10, 16, 22,
       1,  7, 13, 19, 20,
       4,  5, 11, 17, 23,
       2,  8, 14, 15, 21
    ] := by
  native_decide

-- π moves lane (1, 0) to (0, 2): x' = y = 0, y' = 2x + 3y = 2.
example : lane (pi (zeroState.set 1 0xab)) 0 2 = 0xab := by native_decide

-- χ combines each row lane with its two right neighbours: a ⊕ (¬b ∧ c).
example :
    chi 8 (#v[
      0b11001100, 0b10101010, 0b11110000, 0b00001111, 0b01011010,
      0, 0, 0, 0, 0,
      0, 0, 0, 0, 0,
      0, 0, 0, 0, 0,
      0, 0, 0, 0, 0
    ] : Vector ℕ 25) = #v[
      0x9c, 0xa5, 0xa0, 0x8b, 0x78,
      0, 0, 0, 0, 0,
      0, 0, 0, 0, 0,
      0, 0, 0, 0, 0,
      0, 0, 0, 0, 0
    ] := by
  native_decide

-- Full permutations of the all-zero state, applied once and twice, for all
-- four officially published widths (XKCP).

def f200AfterOne : Vector ℕ 25 := #v[
  0x3c, 0x28, 0x26, 0x84, 0x1c,
  0xb3, 0x5c, 0x17, 0x1e, 0xaa,
  0xe9, 0xb8, 0x11, 0x13, 0x4c,
  0xea, 0xa3, 0x85, 0x2c, 0x69,
  0xd2, 0xc5, 0xab, 0xaf, 0xea
]

def f200AfterTwo : Vector ℕ 25 := #v[
  0x1b, 0xef, 0x68, 0x94, 0x92,
  0xa8, 0xa5, 0x43, 0xa5, 0x99,
  0x9f, 0xdb, 0x83, 0x4e, 0x31,
  0x66, 0xa1, 0x4b, 0xe8, 0x27,
  0xd9, 0x50, 0x40, 0x47, 0x9e
]

def f400AfterOne : Vector ℕ 25 := #v[
  0x09f5, 0x40ac, 0x0fa9, 0x14f5, 0xe89f,
  0xeca0, 0x5bd1, 0x7870, 0xeff0, 0xbf8f,
  0x0337, 0x6052, 0xdc75, 0x0ec9, 0xe776,
  0x5246, 0x59a1, 0x5d81, 0x6d95, 0x6e14,
  0x633e, 0x58ee, 0x71ff, 0x714c, 0xb38e
]

def f400AfterTwo : Vector ℕ 25 := #v[
  0xe537, 0xd5d6, 0xdbe7, 0xaaf3, 0x9bc7,
  0xca7d, 0x86b2, 0xfdec, 0x692c, 0x4e5b,
  0x67b1, 0x15ad, 0xa7f7, 0xa66f, 0x67ff,
  0x3f8a, 0x2f99, 0xe2c2, 0x656b, 0x5f31,
  0x5ba6, 0xca29, 0xc224, 0xb85c, 0x097c
]

def f800AfterOne : Vector ℕ 25 := #v[
  0xe531d45d, 0xf404c6fb, 0x23a0bf99, 0xf1f8452f, 0x51ffd042,
  0xe539f578, 0xf00b80a7, 0xaf973664, 0xbf5af34c, 0x227a2424,
  0x88172715, 0x9f685884, 0xb15cd054, 0x1bf4fc0e, 0x6166fa91,
  0x1a9e599a, 0xa3970a1f, 0xab659687, 0xafab8d68, 0xe74b1015,
  0x34001a98, 0x4119eff3, 0x930a0e76, 0x87b28070, 0x11efe996
]

def f800AfterTwo : Vector ℕ 25 := #v[
  0x75bf2d0d, 0x9b610e89, 0xc826af40, 0x64cd84ab, 0xf905bdd6,
  0xbc832835, 0x5f8001b9, 0x15662cce, 0x8e38c95e, 0x701fe543,
  0x1b544380, 0x89acdeff, 0x51edb5de, 0x0e9702d9, 0x6c19aa16,
  0xa2913eee, 0x60754e9a, 0x9819063c, 0xf4709254, 0xd09f9084,
  0x772da259, 0x1db35df7, 0x5aa60162, 0x358825d5, 0xb3783bab
]

def f1600AfterOne : Vector ℕ 25 := #v[
  0xf1258f7940e1dde7, 0x84d5ccf933c0478a, 0xd598261ea65aa9ee, 0xbd1547306f80494d, 0x8b284e056253d057,
  0xff97a42d7f8e6fd4, 0x90fee5a0a44647c4, 0x8c5bda0cd6192e76, 0xad30a6f71b19059c, 0x30935ab7d08ffc64,
  0xeb5aa93f2317d635, 0xa9a6e6260d712103, 0x81a57c16dbcf555f, 0x43b831cd0347c826, 0x01f22f1a11a5569f,
  0x05e5635a21d9ae61, 0x64befef28cc970f2, 0x613670957bc46611, 0xb87c5a554fd00ecb, 0x8c3ee88a1ccf32c8,
  0x940c7922ae3a2614, 0x1841f924a2c509e4, 0x16f53526e70465c2, 0x75f644e97f30a13b, 0xeaf1ff7b5ceca249
]

def f1600AfterTwo : Vector ℕ 25 := #v[
  0x2d5c954df96ecb3c, 0x6a332cd07057b56d, 0x093d8d1270d76b6c, 0x8a20d9b25569d094, 0x4f9c4f99e5e7f156,
  0xf957b9a2da65fb38, 0x85773dae1275af0d, 0xfaf4f247c3d810f7, 0x1f1b9ee6f79a8759, 0xe4fecc0fee98b425,
  0x68ce61b6b9ce68a1, 0xdeea66c4ba8f974f, 0x33c43d836eafb1f5, 0xe00654042719dbd9, 0x7cf8a9f009831265,
  0xfd5449a6bf174743, 0x97ddad33d8994b40, 0x48ead5fc5d0be774, 0xe3b8c8ee55b7b03c, 0x91a0226e649e42e9,
  0x900e3129e7badd7b, 0x202a9ec5faa3cce8, 0x5b3402464e1c3db6, 0x609f4e62a44c1059, 0x20d06cd26a8fbf5c
]

example : keccakF 3 zeroState = f200AfterOne := by native_decide
example : keccakF 3 f200AfterOne = f200AfterTwo := by native_decide

example : keccakF 4 zeroState = f400AfterOne := by native_decide
example : keccakF 4 f400AfterOne = f400AfterTwo := by native_decide

example : keccakF 5 zeroState = f800AfterOne := by native_decide
example : keccakF 5 f800AfterOne = f800AfterTwo := by native_decide

example : keccakF 6 zeroState = f1600AfterOne := by native_decide
example : keccakF 6 f1600AfterOne = f1600AfterTwo := by native_decide

-- Round 0 of the second Keccak-f[1600] example, step by step (XKCP): unlike
-- the sparse single-bit states above, this exercises every step on a dense
-- state with all bit positions populated.

def f1600AfterOneTheta : Vector ℕ 25 := #v[
  0xaf463273ca4d877d, 0xaf9fdf84cec209d0, 0x28c573db9cdda7ba, 0xabbcda349e794c02, 0xfd3cb094025a23b6,
  0xa1f41927f522354e, 0xbbb4f6dd5944099e, 0x71068fc9ec9e2022, 0xbb993bf3eae000d3, 0x4687a426b0860f85,
  0xb5391435a9bb8caf, 0x82ecf55bf0736f59, 0x7cf829d3e1485b0b, 0x5511acc9f2becd69, 0x77e6d18b71aca57e,
  0x5b86de50ab75f4fb, 0x4ff4ed8f71cb3ea8, 0x9c6b255041436845, 0xaed5c751be290b84, 0xfa2a161b7cc6c129,
  0xca6fc42824967c8e, 0x330bea595fc747be, 0xeba860e3dd836b96, 0x635fd9ed8ec9a474, 0x9ce501ea3ce551a8
]

def f1600AfterOneRho : Vector ℕ 25 := #v[
  0xaf463273ca4d877d, 0x5f3fbf099d8413a1, 0x8a315cf6e73769ee, 0x49e794c02abbcda3, 0xa012d11db7e9e584,
  0x522354ea1f41927f, 0x4099ebbb4f6dd594, 0x41a3f27b2788089c, 0x69ddcc9df9f57000, 0x426b0860f854687a,
  0xa9c8a1ad4ddc657d, 0xb3d56fc1cdbd660b, 0x42d85be7c14e9f0a, 0x93e57d9ad2aa2359, 0xd652bf3bf368c5b8,
  0xebe9f6b70dbca156, 0x67d509fe9db1ee39, 0x92a820a1b422ce35, 0xea37c5217095dab8, 0x2a161b7cc6c129fa,
  0x10a09259f23b29bf, 0xcc2fa9657f1d1ef8, 0xdd750c1c7bb06d72, 0x74635fd9ed8ec9a4, 0x407a8f39546a2739
]

def f1600AfterOnePi : Vector ℕ 25 := #v[
  0xaf463273ca4d877d, 0x4099ebbb4f6dd594, 0x42d85be7c14e9f0a, 0xea37c5217095dab8, 0x407a8f39546a2739,
  0x49e794c02abbcda3, 0x426b0860f854687a, 0xa9c8a1ad4ddc657d, 0x67d509fe9db1ee39, 0xdd750c1c7bb06d72,
  0x5f3fbf099d8413a1, 0x41a3f27b2788089c, 0x93e57d9ad2aa2359, 0x2a161b7cc6c129fa, 0x10a09259f23b29bf,
  0xa012d11db7e9e584, 0x522354ea1f41927f, 0xb3d56fc1cdbd660b, 0x92a820a1b422ce35, 0x74635fd9ed8ec9a4,
  0x8a315cf6e73769ee, 0x69ddcc9df9f57000, 0xd652bf3bf368c5b8, 0xebe9f6b70dbca156, 0xcc2fa9657f1d1ef8
]

def f1600AfterOneChi : Vector ℕ 25 := #v[
  0xad0622374a4f8d77, 0xe8be6fbb7ffc9524, 0x429051ffc524ba0b, 0x4533f563fa905afc, 0x00e346b1514a77b9,
  0xe067354d2f33c8a6, 0x047e00326875e27a, 0x31e8a5ad2fdc643f, 0x6757993e9dba6eb8, 0xdf7d043cabf44d2a,
  0xcd7bb2894da630e0, 0x69b1f01f23c9003e, 0x8345fd9be290235c, 0x6509367ccb453bfa, 0x1020d22bd03321a3,
  0x01c6fa1c77558184, 0x520b54ca2f431a4b, 0xd79630998431678b, 0x12b8a0a5a643ea35, 0x26425b3be58edbdf,
  0x1c336fd4e53fec56, 0x40748c19f5615046, 0xd254b67b8169db10, 0xe9f9a2258d9ec050, 0xade3296c67dd0ef8
]

def f1600AfterOneIota : Vector ℕ 25 := #v[
  0xad0622374a4f8d76, 0xe8be6fbb7ffc9524, 0x429051ffc524ba0b, 0x4533f563fa905afc, 0x00e346b1514a77b9,
  0xe067354d2f33c8a6, 0x047e00326875e27a, 0x31e8a5ad2fdc643f, 0x6757993e9dba6eb8, 0xdf7d043cabf44d2a,
  0xcd7bb2894da630e0, 0x69b1f01f23c9003e, 0x8345fd9be290235c, 0x6509367ccb453bfa, 0x1020d22bd03321a3,
  0x01c6fa1c77558184, 0x520b54ca2f431a4b, 0xd79630998431678b, 0x12b8a0a5a643ea35, 0x26425b3be58edbdf,
  0x1c336fd4e53fec56, 0x40748c19f5615046, 0xd254b67b8169db10, 0xe9f9a2258d9ec050, 0xade3296c67dd0ef8
]

example : theta 64 f1600AfterOne = f1600AfterOneTheta := by native_decide
example : rho 64 f1600AfterOneTheta = f1600AfterOneRho := by native_decide
example : pi f1600AfterOneRho = f1600AfterOnePi := by native_decide
example : chi 64 f1600AfterOnePi = f1600AfterOneChi := by native_decide
example : iota 0x0000000000000001 f1600AfterOneChi = f1600AfterOneIota := by native_decide

example : keccakRound 64 0x0000000000000001 f1600AfterOne = f1600AfterOneIota := by
  native_decide

-- Structural properties of the steps, checked on the official dense states:
-- θ is GF(2)-linear, the π lane permutation has order 24, and ι is an
-- involution.
example :
    theta 64 (Vector.ofFn fun i => f1600AfterOne[i] ^^^ f1600AfterTwo[i]) =
      (Vector.ofFn fun i => (theta 64 f1600AfterOne)[i] ^^^ (theta 64 f1600AfterTwo)[i]) := by
  native_decide

example : Fin.foldl 24 (fun A (_ : Fin 24) => pi A) f1600AfterOne = f1600AfterOne := by
  native_decide

example :
    iota 0x8000000080008008 (iota 0x8000000080008008 f1600AfterOne) = f1600AfterOne := by
  native_decide

-- Round-prefix checkpoints on the all-zero state (XKCP): the mid-permutation
-- state after 12 rounds pins the round-constant sequencing, not just the
-- final state.

/-- The first `n` rounds of Keccak-f[1600]. -/
def keccakF1600Rounds (n : Fin 25) (A : Vector ℕ 25) : Vector ℕ 25 :=
  Fin.foldl n.val (fun A (i : Fin n.val) => keccakRound 64 roundConstants[i.val] A) A

def f1600AfterRound11 : Vector ℕ 25 := #v[
  0x4089b1d2ef5d3a26, 0x8409f6c9be239ecb, 0x12657d5a4568ead5, 0x4d9f3e32387e66d3, 0x3be7f6680bb1c847,
  0x61ed7fb0ce6ca6af, 0x3671348a3fbd6487, 0x81e9f633f01dcf03, 0xab5eefa38e5546d9, 0x8298d4e430062494,
  0x3229e84a8e1704c2, 0x56f221867a1b3140, 0xdb7043cf08757bb2, 0x52de6de69935b888, 0x98a1c2d38194eda1,
  0x9af85d4549fb53c7, 0x667e09de6b59e740, 0xc08877b3d1a7a9f3, 0x5da108d19209739f, 0xe0e096ffe4ff71ea,
  0x77badafbfd43d602, 0x50a13329b93c785f, 0xf8ae145adffbe076, 0x366d5164bb8f0bb5, 0x438298aa08f16a54
]

example : keccakF1600Rounds 0 zeroState = zeroState := by native_decide
example : keccakF1600Rounds 1 zeroState = afterRound0 := by native_decide
example : keccakF1600Rounds 2 zeroState = f1600Round1Iota := by native_decide
example : keccakF1600Rounds 12 zeroState = f1600AfterRound11 := by native_decide
example : keccakF1600Rounds 24 zeroState = f1600AfterOne := by native_decide

-- The 1600-bit string interface.

def zeroBits : Vector ℕ 1600 := Vector.replicate 1600 0

example : bitsToState zeroBits = zeroState := by native_decide

-- state ↔ bits roundtrips
example : bitsToState (stateToBits f1600AfterOne) = f1600AfterOne := by native_decide
example :
    stateToBits (bitsToState (Vector.ofFn fun i => i.val % 2)) =
      (Vector.ofFn fun i => i.val % 2) := by
  native_decide

-- Bit-index convention (FIPS 202, Section 3.1.2): state bit 64·i + z is bit z
-- of lane i, so bit 1 is bit 1 of lane (0, 0), bit 64 is bit 0 of lane (1, 0),
-- and bit 1599 is the top bit of lane (4, 4).
example : bitsToState (zeroBits.set 1 1) = zeroState.set 0 2 := by native_decide
example : bitsToState (zeroBits.set 64 1) = zeroState.set 1 1 := by native_decide
example : bitsToState (zeroBits.set 1599 1) = zeroState.set 24 0x8000000000000000 := by
  native_decide

-- Spot-check bits of the official state: lane (0,0) = 0xf1258f7940e1dde7 ends
-- in binary ...11100111, and lane (24,4) has its top bit set.
example : (stateToBits f1600AfterOne)[0] = 1 := by native_decide
example : (stateToBits f1600AfterOne)[3] = 0 := by native_decide
example : (stateToBits f1600AfterOne)[64] = 0 := by native_decide
example : (stateToBits f1600AfterOne)[65] = 1 := by native_decide
example : (stateToBits f1600AfterOne)[1599] = 1 := by native_decide

-- Keccak-f[1600] end to end on bit strings, against the official vectors.
example : keccakF1600 zeroBits = stateToBits f1600AfterOne := by native_decide
example : keccakF1600 (stateToBits f1600AfterOne) = stateToBits f1600AfterTwo := by
  native_decide

-- The permutation maps bit strings to bit strings.
example : IsBitString (keccakF1600 zeroBits) := by native_decide
example : IsBitString (keccakF1600 (stateToBits f1600AfterOne)) := by native_decide

-- Byte serialization. The XKCP files also print the permuted state as a byte
-- string (bit 8k + j of the state is bit j of byte k), which pins the bit
-- order of the interface against the official serialization.

/-- Group a 1600-bit string into 200 bytes, least-significant bit first. -/
def bitsToBytes (s : Vector ℕ 1600) : Vector ℕ 200 :=
  Vector.ofFn fun k =>
    Fin.foldl 8 (fun acc (j : Fin 8) => acc + s[8 * k.val + j.val] * 2 ^ j.val) 0

/-- Spread 200 bytes into a 1600-bit string, least-significant bit first. -/
def bytesToBits (bs : Vector ℕ 200) : Vector ℕ 1600 :=
  Vector.ofFn fun i => bs[i.val / 8] / 2 ^ (i.val % 8) % 2

def f1600AfterOneBytes : Vector ℕ 200 := #v[
  0xe7, 0xdd, 0xe1, 0x40, 0x79, 0x8f, 0x25, 0xf1, 0x8a, 0x47,
  0xc0, 0x33, 0xf9, 0xcc, 0xd5, 0x84, 0xee, 0xa9, 0x5a, 0xa6,
  0x1e, 0x26, 0x98, 0xd5, 0x4d, 0x49, 0x80, 0x6f, 0x30, 0x47,
  0x15, 0xbd, 0x57, 0xd0, 0x53, 0x62, 0x05, 0x4e, 0x28, 0x8b,
  0xd4, 0x6f, 0x8e, 0x7f, 0x2d, 0xa4, 0x97, 0xff, 0xc4, 0x47,
  0x46, 0xa4, 0xa0, 0xe5, 0xfe, 0x90, 0x76, 0x2e, 0x19, 0xd6,
  0x0c, 0xda, 0x5b, 0x8c, 0x9c, 0x05, 0x19, 0x1b, 0xf7, 0xa6,
  0x30, 0xad, 0x64, 0xfc, 0x8f, 0xd0, 0xb7, 0x5a, 0x93, 0x30,
  0x35, 0xd6, 0x17, 0x23, 0x3f, 0xa9, 0x5a, 0xeb, 0x03, 0x21,
  0x71, 0x0d, 0x26, 0xe6, 0xa6, 0xa9, 0x5f, 0x55, 0xcf, 0xdb,
  0x16, 0x7c, 0xa5, 0x81, 0x26, 0xc8, 0x47, 0x03, 0xcd, 0x31,
  0xb8, 0x43, 0x9f, 0x56, 0xa5, 0x11, 0x1a, 0x2f, 0xf2, 0x01,
  0x61, 0xae, 0xd9, 0x21, 0x5a, 0x63, 0xe5, 0x05, 0xf2, 0x70,
  0xc9, 0x8c, 0xf2, 0xfe, 0xbe, 0x64, 0x11, 0x66, 0xc4, 0x7b,
  0x95, 0x70, 0x36, 0x61, 0xcb, 0x0e, 0xd0, 0x4f, 0x55, 0x5a,
  0x7c, 0xb8, 0xc8, 0x32, 0xcf, 0x1c, 0x8a, 0xe8, 0x3e, 0x8c,
  0x14, 0x26, 0x3a, 0xae, 0x22, 0x79, 0x0c, 0x94, 0xe4, 0x09,
  0xc5, 0xa2, 0x24, 0xf9, 0x41, 0x18, 0xc2, 0x65, 0x04, 0xe7,
  0x26, 0x35, 0xf5, 0x16, 0x3b, 0xa1, 0x30, 0x7f, 0xe9, 0x44,
  0xf6, 0x75, 0x49, 0xa2, 0xec, 0x5c, 0x7b, 0xff, 0xf1, 0xea
]

example : bitsToBytes (stateToBits f1600AfterOne) = f1600AfterOneBytes := by native_decide
example : bitsToBytes (keccakF1600 zeroBits) = f1600AfterOneBytes := by native_decide
example : bitsToState (bytesToBits f1600AfterOneBytes) = f1600AfterOne := by native_decide

-- Hash-derived vectors (independent of XKCP). A SHA-3/SHAKE input that fits in
-- one rate-sized block is absorbed as a single XOR into the all-zero state, so
-- the digest is a prefix of one Keccak-f[1600] output: the state is the padded
-- block (domain-separation byte after the message, 0x80 at the last rate byte)
-- followed by zero capacity bytes.

/-- The first `outLen` bytes of the permuted state: one absorb + squeeze. -/
def squeezeBytes (input : Vector ℕ 200) (outLen : ℕ) (h : outLen ≤ 200 := by omega) :
    Vector ℕ outLen :=
  Vector.ofFn fun i => (bitsToBytes (keccakF1600 (bytesToBits input)))[i.val]'(by omega)

-- SHA3-224("") = 6b4e03423667dbb7...5b5a6bc7 (FIPS 202; rate 144 bytes).
example :
    squeezeBytes (((Vector.replicate 200 0).set 0 0x06).set 143 0x80) 28 = #v[
      0x6b, 0x4e, 0x03, 0x42, 0x36, 0x67, 0xdb, 0xb7, 0x3b, 0x6e,
      0x15, 0x45, 0x4f, 0x0e, 0xb1, 0xab, 0xd4, 0x59, 0x7f, 0x9a,
      0x1b, 0x07, 0x8e, 0x3f, 0x5b, 0x5a, 0x6b, 0xc7
    ] := by
  native_decide

-- SHA3-256("") = a7ffc6f8bf1ed766...80f8434a (FIPS 202; rate 136 bytes).
example :
    squeezeBytes (((Vector.replicate 200 0).set 0 0x06).set 135 0x80) 32 = #v[
      0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1,
      0x47, 0x56, 0xa0, 0x61, 0xd6, 0x62, 0xf5, 0x80, 0xff, 0x4d,
      0xe4, 0x3b, 0x49, 0xfa, 0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8,
      0x43, 0x4a
    ] := by
  native_decide

-- SHA3-256("abc") = 3a985da74fe225b2...11431532 (FIPS 202).
example :
    squeezeBytes
      (((((Vector.replicate 200 0).set 0 0x61).set 1 0x62).set 2 0x63).set 3 0x06
        |>.set 135 0x80) 32 = #v[
      0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c,
      0x17, 0x2d, 0x6b, 0xd3, 0x90, 0xbd, 0x85, 0x5f, 0x08, 0x6e,
      0x3e, 0x9d, 0x52, 0x5b, 0x46, 0xbf, 0xe2, 0x45, 0x11, 0x43,
      0x15, 0x32
    ] := by
  native_decide

-- SHA3-384("") = 0c63a75b845e4f7d...58d5f004 (FIPS 202; rate 104 bytes).
example :
    squeezeBytes (((Vector.replicate 200 0).set 0 0x06).set 103 0x80) 48 = #v[
      0x0c, 0x63, 0xa7, 0x5b, 0x84, 0x5e, 0x4f, 0x7d, 0x01, 0x10,
      0x7d, 0x85, 0x2e, 0x4c, 0x24, 0x85, 0xc5, 0x1a, 0x50, 0xaa,
      0xaa, 0x94, 0xfc, 0x61, 0x99, 0x5e, 0x71, 0xbb, 0xee, 0x98,
      0x3a, 0x2a, 0xc3, 0x71, 0x38, 0x31, 0x26, 0x4a, 0xdb, 0x47,
      0xfb, 0x6b, 0xd1, 0xe0, 0x58, 0xd5, 0xf0, 0x04
    ] := by
  native_decide

-- SHA3-512("") = a69f73cca23a9ac5...28 1dcd26 (FIPS 202; rate 72 bytes).
example :
    squeezeBytes (((Vector.replicate 200 0).set 0 0x06).set 71 0x80) 64 = #v[
      0xa6, 0x9f, 0x73, 0xcc, 0xa2, 0x3a, 0x9a, 0xc5, 0xc8, 0xb5,
      0x67, 0xdc, 0x18, 0x5a, 0x75, 0x6e, 0x97, 0xc9, 0x82, 0x16,
      0x4f, 0xe2, 0x58, 0x59, 0xe0, 0xd1, 0xdc, 0xc1, 0x47, 0x5c,
      0x80, 0xa6, 0x15, 0xb2, 0x12, 0x3a, 0xf1, 0xf5, 0xf9, 0x4c,
      0x11, 0xe3, 0xe9, 0x40, 0x2c, 0x3a, 0xc5, 0x58, 0xf5, 0x00,
      0x19, 0x9d, 0x95, 0xb6, 0xd3, 0xe3, 0x01, 0x75, 0x85, 0x86,
      0x28, 0x1d, 0xcd, 0x26
    ] := by
  native_decide

-- SHAKE128("", 32) = 7f9c2ba4e88f827d...fa66ef26 (FIPS 202; rate 168 bytes,
-- domain byte 0x1f).
example :
    squeezeBytes (((Vector.replicate 200 0).set 0 0x1f).set 167 0x80) 32 = #v[
      0x7f, 0x9c, 0x2b, 0xa4, 0xe8, 0x8f, 0x82, 0x7d, 0x61, 0x60,
      0x45, 0x50, 0x76, 0x05, 0x85, 0x3e, 0xd7, 0x3b, 0x80, 0x93,
      0xf6, 0xef, 0xbc, 0x88, 0xeb, 0x1a, 0x6e, 0xac, 0xfa, 0x66,
      0xef, 0x26
    ] := by
  native_decide

-- Keccak-256("") = c5d2460186f7233c...5d85a470, the empty hash replicated by
-- every Ethereum client (legacy 0x01 padding; rate 136 bytes).
example :
    squeezeBytes (((Vector.replicate 200 0).set 0 0x01).set 135 0x80) 32 = #v[
      0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e,
      0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0, 0xe5, 0x00, 0xb6, 0x53,
      0xca, 0x82, 0x27, 0x3b, 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85,
      0xa4, 0x70
    ] := by
  native_decide

-- Spec-level statements.
example : Assumptions zeroBits := by
  simp only [Assumptions]
  native_decide

example : Spec zeroBits (stateToBits f1600AfterOne) := by
  simp only [Spec]
  native_decide

-- A wrong output must not satisfy the Spec, and a non-bit input must fail the
-- Assumptions.
example : ¬ Spec zeroBits (stateToBits f1600AfterTwo) := by
  simp only [Spec]
  native_decide

example : ¬ Assumptions (zeroBits.set 0 2) := by
  simp only [Assumptions]
  native_decide

end Specs.Keccak.Tests
