import Challenge.Specs.KeccakP800
import Challenge.Utils.F2Bits

namespace Specs.KeccakP800.Tests

open Challenge.F2Bits

/-- Unpack 25 little-endian 32-bit lanes (index `x + 5 * y`) into a GF(2) state. -/
def lanesToState (words : Vector ℕ 25) : State (F p2) :=
  Vector.ofFn fun i : Fin stateBits =>
    have h : i.val / laneBits < 25 := by
      have hi : i.val < 800 := i.isLt
      show i.val / 32 < 25
      omega
    if natBit (words[i.val / laneBits]'h) (i.val % laneBits) = 0 then 0 else 1

/-- Pack a GF(2) state into 25 little-endian 32-bit lanes. -/
def stateToLanes (state : State (F p2)) : Vector ℕ 25 :=
  toWords laneBits 25 state

/-!
## Tables

The round constants and ρ offsets, as tabulated at the top of the XKCP
reference trace for Keccak-f[800]:
<https://github.com/XKCP/XKCP/blob/master/tests/TestVectors/KeccakF-800-IntermediateValues.txt>.
-/

example : roundConstants = #v[
  0x00000001, 0x00008082, 0x0000808a, 0x80008000, 0x0000808b, 0x80000001,
  0x80008081, 0x00008009, 0x0000008a, 0x00000088, 0x80008009, 0x8000000a,
  0x8000808b, 0x0000008b, 0x00008089, 0x00008003, 0x00008002, 0x00000080,
  0x0000800a, 0x8000000a, 0x80008081, 0x00008080
] := by native_decide

-- ρ offsets at index x + 5·y (rows are y = 0, ..., 4).
example : (Vector.ofFn fun i : Fin 25 => rhoOffset (i.val % 5) (i.val / 5)) = #v[
   0,  1, 30, 28, 27,
   4, 12,  6, 23, 20,
   3, 10, 11, 25,  7,
   9, 13, 15, 21,  8,
  18,  2, 29, 24, 14
] := by native_decide

/-!
## Keccak-f[800] = Keccak-p[800, 22] against the published vectors

The XKCP trace applies Keccak-f[800] to the all-zero state and then once more
to the result, listing every intermediate state. `f800AfterOne` and
`f800AfterTwo` are the two outputs; `afterTenOfZero` and
`afterTenOfAfterOne` are the states after the first 10 rounds (the
"After iota" state of "Round 9") of each application.
-/

def zeroLanes : Vector ℕ 25 := Vector.replicate 25 0

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

def afterTenOfZero : Vector ℕ 25 := #v[
  0x050da5be, 0xa1e90e64, 0xf58ed739, 0x07fe8fea, 0x60a567f2,
  0x16dfb209, 0x32d9e63a, 0x03438836, 0xd471fb9a, 0x220b364b,
  0x4a5b0b69, 0x807d6543, 0x5e399128, 0xbe9c8f39, 0xb318882b,
  0x17ab82b7, 0x45d7789a, 0x122cd832, 0x7e6ba9a6, 0x3da6fa0a,
  0x412a119a, 0x02f25e4c, 0x403742d4, 0x24181bc3, 0xb3fc4bc8
]

def afterTenOfAfterOne : Vector ℕ 25 := #v[
  0xbcc8527e, 0xd5a45cfc, 0x35f840e1, 0xe12f4600, 0xd6bae8c9,
  0xa49a85bb, 0x3f902c15, 0x695c0039, 0xa69e3ffc, 0xfb90a756,
  0x226f0841, 0xfdb165a8, 0xd91ac230, 0x64a7c86e, 0xf553e427,
  0xb436235f, 0xc1d2df89, 0x97286367, 0xa4b7ae42, 0x253721bf,
  0x76c5681c, 0x6663d85b, 0xfca615c5, 0xc672cd5a, 0x216b9308
]

-- The bit-level 22-round permutation over GF(2) reproduces the XKCP outputs.
example : stateToLanes (keccakF800 (lanesToState zeroLanes)) = f800AfterOne := by
  native_decide
example : stateToLanes (keccakF800 (lanesToState f800AfterOne)) = f800AfterTwo := by
  native_decide

-- So does the lane-level reference, through both `keccakF` and `keccakP`.
example : Specs.Keccak.keccakF 5 zeroLanes = f800AfterOne := by native_decide
example : Specs.Keccak.keccakP 5 22 (by decide) f800AfterOne = f800AfterTwo := by native_decide

-- Keccak-p[800, 0] is the identity.
example : stateToLanes (keccakP 0 (by decide) (lanesToState f800AfterOne)) = f800AfterOne := by
  native_decide

/-!
## Keccak-p[800, 12]

Keccak-p[800, 12] runs the last 12 rounds of Keccak-f[800]: applied to the state
after the first 10 rounds of either XKCP trace, it must produce that trace's
output. The remaining vectors are structured inputs whose outputs were
computed with an independent Keccak-p[800] implementation validated against
every intermediate state of the XKCP trace; the lane-level `Specs.Keccak.keccakP`
reproduces them below.
-/

structure PermutationVector where
  inputLanes : Vector ℕ 25
  outputLanes : Vector ℕ 25

def permutationVectors : Vector PermutationVector 10 := #v[
  -- XKCP trace, first application: rounds 10, ..., 21 of Keccak-f[800](0).
  { inputLanes := afterTenOfZero, outputLanes := f800AfterOne },
  -- XKCP trace, second application.
  { inputLanes := afterTenOfAfterOne, outputLanes := f800AfterTwo },
  -- the all-zero state.
  {
    inputLanes := Vector.replicate 25 0
    outputLanes := #v[
      0x256e3e0b, 0xd2eb9acb, 0xc1257f4d, 0xed369666, 0xf74ecfa9,
      0xd54deac9, 0x178e308c, 0x6819ea93, 0x118d9fad, 0x01fe06c2,
      0x448de291, 0xa42b4292, 0x627af65a, 0x9749f0c6, 0xc5f2c18f,
      0x48b13a9a, 0xd08133c7, 0x03f6b92b, 0xee81a0e2, 0x38b8e2ca,
      0xe914ba14, 0x2d3df2b8, 0x357a532e, 0x498091ac, 0xdd6f823a
    ]
  },
  -- bytes `i % 251`.
  {
    inputLanes := #v[
      0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110,
      0x17161514, 0x1b1a1918, 0x1f1e1d1c, 0x23222120, 0x27262524,
      0x2b2a2928, 0x2f2e2d2c, 0x33323130, 0x37363534, 0x3b3a3938,
      0x3f3e3d3c, 0x43424140, 0x47464544, 0x4b4a4948, 0x4f4e4d4c,
      0x53525150, 0x57565554, 0x5b5a5958, 0x5f5e5d5c, 0x63626160
    ]
    outputLanes := #v[
      0x75d46537, 0x17c54873, 0x5fc8e23d, 0x3761ab54, 0x8c48d4ae,
      0x176cbc50, 0x089167fe, 0x6a72d4dd, 0x989bcc1c, 0x66bf8aa3,
      0x5a65a130, 0x77d36fb0, 0xd5d6f17e, 0x591b13aa, 0xc49efe0d,
      0xe9bfe3dd, 0x8445a595, 0x9b5a554d, 0xe8cbec2c, 0x8a74ad4b,
      0x802a771c, 0xf0809086, 0xa481466b, 0xf0e10a78, 0x16848873
    ]
  },
  -- all bytes `0xff`.
  {
    inputLanes := Vector.replicate 25 0xffffffff
    outputLanes := #v[
      0x8d6f7388, 0xf7d8f2c1, 0xe6cfed45, 0x88d863a1, 0xbcc562be,
      0x5f5ded95, 0x0cc36102, 0x962a0a06, 0x3ff191a4, 0xf97e80e2,
      0xcf5450a4, 0x6fc53ff1, 0x4f77aeec, 0x0482c248, 0x03125f4c,
      0x9a63dfe4, 0x13290861, 0x6a943a1c, 0xd4a5006c, 0xde61e507,
      0xcccc41ea, 0xa82329a0, 0xfad2f44f, 0xbaf9213c, 0x1e860659
    ]
  },
  -- alternating bytes `0xaa`, `0x55`.
  {
    inputLanes := Vector.replicate 25 0x55aa55aa
    outputLanes := #v[
      0xff52274e, 0xdc428171, 0x4798ff88, 0xacb7c7e0, 0xe727bb1e,
      0x70ead979, 0x5bc345bc, 0x4b6eb87f, 0xacf4ff22, 0xa3e6e209,
      0xeb2d9507, 0xf87aaa91, 0xb033d980, 0xf6475775, 0xeac22f3f,
      0xe2e2b43b, 0xa62452c0, 0x31112cad, 0x16342d45, 0x4a9e6084,
      0xaa86ef86, 0x08759811, 0xba1cb3ba, 0x58e05031, 0xf0f25db9
    ]
  },
  -- a single set bit at state bit 0.
  {
    inputLanes := Vector.ofFn fun i : Fin 25 => if i.val = 0 then 1 else 0
    outputLanes := #v[
      0x67554e65, 0x95047f18, 0x8c78e786, 0x8f7d9b63, 0x71556156,
      0x7f9dd4ae, 0x94c0841f, 0x9029acaf, 0x2f173427, 0x6f3c9a92,
      0xfe4b894e, 0xc9d7887a, 0x92b70514, 0x0fabeef2, 0x410c4249,
      0xd762d8fc, 0x8a6964d5, 0xdf12e841, 0xeaa1f383, 0xf9a38b74,
      0x6205a7ed, 0x93e59e2a, 0xb73b4b26, 0xc2deaba7, 0xdd6ea5b7
    ]
  },
  -- a single set bit at state bit 799.
  {
    inputLanes := Vector.ofFn fun i : Fin 25 => if i.val = 24 then 0x80000000 else 0
    outputLanes := #v[
      0xe1a349ef, 0x6d117dc6, 0x0c1f6080, 0xafc0dc63, 0x2b10390b,
      0x83ac3271, 0x570b17e0, 0x5c1ca533, 0xdde474e0, 0xb8dbe422,
      0xf4d902a6, 0xec2d7771, 0x661f910b, 0x99f30504, 0x2a2a3a85,
      0xc43f6f79, 0xcaaa8822, 0x7af338d5, 0x8d592805, 0x74f07223,
      0xa23723ce, 0x3637a71a, 0x83f114d7, 0xc7285f1d, 0xd6cc441b
    ]
  },
  -- bytes `(73 i + 41) mod 256`.
  {
    inputLanes := #v[
      0x04bb7229, 0x28df964d, 0x4c03ba71, 0x7027de95, 0x944b02b9,
      0xb86f26dd, 0xdc934a01, 0x00b76e25, 0x24db9249, 0x48ffb66d,
      0x6c23da91, 0x9047feb5, 0xb46b22d9, 0xd88f46fd, 0xfcb36a21,
      0x20d78e45, 0x44fbb269, 0x681fd68d, 0x8c43fab1, 0xb0671ed5,
      0xd48b42f9, 0xf8af661d, 0x1cd38a41, 0x40f7ae65, 0x641bd289
    ]
    outputLanes := #v[
      0x034c6483, 0x53152831, 0x3e8fe461, 0xa43d16cc, 0x32841196,
      0xd807cec7, 0x5d902456, 0x5fb3220f, 0x83312fba, 0x65d8bdb9,
      0xba712ef3, 0x2bd604ac, 0x06b261a4, 0x2b955ab5, 0x7b46397c,
      0xcafab2c4, 0x50c1eb06, 0x9dc34a5f, 0xab288962, 0xbcd0e3f4,
      0x28bd3ed9, 0xe6e480d7, 0x6e75a61a, 0xaeec1dde, 0xdaddb089
    ]
  },
  -- bytes `(i² + 17 i + 29) mod 256`.
  {
    inputLanes := #v[
      0x59432f1d, 0xc5a78b71, 0x512b07e5, 0xfdcfa379, 0xc9935f2d,
      0xb5773b01, 0xc17b37f5, 0xed9f5309, 0x39e38f3d, 0xa547eb91,
      0x31cb6705, 0xdd6f0399, 0xa933bf4d, 0x95179b21, 0xa11b9715,
      0xcd3fb329, 0x1983ef5d, 0x85e74bb1, 0x116bc725, 0xbd0f63b9,
      0x89d31f6d, 0x75b7fb41, 0x81bbf735, 0xaddf1349, 0xf9234f7d
    ]
    outputLanes := #v[
      0xdb6f0dc4, 0x2d147577, 0x9dd8aecd, 0x854875ee, 0xacdd6def,
      0xf2b6c38e, 0xc3955363, 0xe1317d2f, 0x7655f643, 0x9b06809d,
      0x6aa3cd3c, 0xc545343e, 0xa361e02a, 0x57403fdd, 0xc08631d4,
      0xb2fb9bdc, 0x83c85f8f, 0x06d8db89, 0x5553f9fa, 0xbca6564c,
      0x3a80dc52, 0x3bec34b3, 0xcb395efe, 0x133e7295, 0x9739cec0
    ]
  }
]

example : ∀ i : Fin 10,
    let v := permutationVectors[i]
    stateToLanes (keccakP800_12 (lanesToState v.inputLanes)) = v.outputLanes := by
  native_decide

-- The bit-level and lane-level formulations agree on Keccak-p[800, 12] ...
example : ∀ i : Fin 10,
    let v := permutationVectors[i]
    Specs.Keccak.keccakP 5 12 (by decide) v.inputLanes = v.outputLanes := by
  native_decide

-- ... and on the full Keccak-f[800] of every vector input.
example : ∀ i : Fin 10,
    let v := permutationVectors[i]
    stateToLanes (keccakF800 (lanesToState v.inputLanes)) = Specs.Keccak.keccakF 5 v.inputLanes := by
  native_decide

end Specs.KeccakP800.Tests
