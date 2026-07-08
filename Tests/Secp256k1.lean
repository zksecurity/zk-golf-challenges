import Challenge.Specs.Secp256k1

-- Test vectors for naive double-and-add scalar multiplication on secp256k1.
-- Every [k]G / [k]P value was cross-checked against two independent
-- implementations of the group law and python-ecdsa; k = 112233445566778899
-- matches the widely published point-multiplication vectors. The vectors
-- exercise the exceptional branches too: [n]G ends in a P + (-P)
-- cancellation, [2n]G doubles the point at infinity, [2n+1]G recovers.

namespace Specs.Secp256k1.Tests

open Specs.ShortWeierstrass Specs.Secp256k1

/-- MSB-first bit decomposition of `k`, for building test scalars. Bits of
`k` at position `n` and above are dropped. -/
def toBits (n k : ℕ) : Vector ℕ n :=
  Vector.ofFn fun i => k / 2 ^ (n - 1 - i.val) % 2

-- `toBits` is MSB-first: 0xb5 = 0b10110101.
example : toBits 8 0xb5 = #v[1, 0, 1, 1, 0, 1, 0, 1] := by native_decide

-- `toBits` is a right inverse of the spec's bit decoder.
example : scalarOfBits (toBits 256 0x18ebbb95eed0e13) = 0x18ebbb95eed0e13 := by
  native_decide

-- Entries outside {0, 1} are not bits: `scalarMul` treats them as 0 while
-- `scalarOfBits` does not — `IsBitArray` is the assumption ruling them out.
example : scalarMul curve (#v[2] : Vector ℕ 1) G = .infinity := by native_decide
example : scalarOfBits (#v[2] : Vector ℕ 1) = 2 := by native_decide

-- The generator lies on the curve, as do the curve parameters we transcribed.
example : OnCurve curve G := by native_decide

-- The fixed-base spec is literally the variable-base spec applied to `G`.
example (bits : Vector ℕ scalarBits) (output : GroupPoint Fp) :
    Specs.Secp256k1ScalarMulFixedBase.Spec bits output ↔
      Specs.Secp256k1ScalarMul.Spec bits G output :=
  Iff.rfl

/-- `[2]G`. -/
def twoG : Point Fp := {
  x := 0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5
  y := 0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a
}

/-- `[3]G`. -/
def threeG : Point Fp := {
  x := 0xf9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9
  y := 0x388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672
}

/-- `[5]G`. -/
def fiveG : Point Fp := {
  x := 0x2f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4
  y := 0xd8ac222636e5e3d6d4dba9dda6c9c426f788271bab0d6840dca87d3aa6ac62d6
}

-- k = 0: the naive algorithm never leaves the point at infinity.
example : scalarMul curve (toBits 256 0) G = .infinity := by native_decide

-- k = 1: `[1]G = G`.
example : scalarMul curve (toBits 256 1) G = .affine G := by native_decide

-- k = 2: a pure doubling path.
example : scalarMul curve (toBits 256 2) G = .affine twoG := by native_decide

-- k = 3: doubling followed by a final add.
example : scalarMul curve (toBits 256 3) G = .affine threeG := by native_decide

/-- Published point-multiplication vector: `[112233445566778899]G`. -/
example : scalarMul curve (toBits 256 112233445566778899) G = .affine {
  x := 0xa90cc3d3f3e146daadfc74ca1372207cb4b725ae708cef713a98edd73d99ef29
  y := 0x5a79d6b289610c68bc3b47f3d72f9788a26a06868b4d8e433e1e2ad76fb7dc76
} := by native_decide

/-- A 256-bit-wide scalar (the leading hex digits of π's fraction). -/
def kPi : ℕ := 0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89

-- `toBits` produces genuine bit arrays.
example : IsBitArray (toBits 256 kPi) := by native_decide

example : scalarMul curve (toBits 256 kPi) G = .affine {
  x := 0x359805af09494a6015501a5f5ebadee846461f6191914596ed9856f7c7d59e06
  y := 0x5c116c04cad47238f2a427b4696375ea69324db42c14bfce56acd75cf9cb4b7b
} := by native_decide

-- k = n - 1: yields `-G = (G.x, -G.y)`.
example : scalarMul curve (toBits 256 (order - 1)) G = .affine { x := G.x, y := -G.y } := by
  native_decide

-- k = n: the run ends with the `[n-1]G + G = (-G) + G` cancellation, so the
-- result is the point at infinity.
example : scalarMul curve (toBits 256 order) G = .infinity := by native_decide

-- The same scalar with a wider encoding keeps the leading-zero behavior honest.
example : scalarMul curve (toBits 320 order) G = .infinity := by native_decide

-- Direct group-law exceptional cases.
example : add curve .infinity (.affine G) = .affine G := by native_decide
example : add curve (.affine G) .infinity = .affine G := by native_decide
example : add curve (.affine G) (.affine { x := G.x, y := -G.y }) = .infinity := by
  native_decide

-- k = n - 2: another cancellation-adjacent scalar, yielding `-[2]G`.
example : scalarMul curve (toBits 256 (order - 2)) G = .affine {
  x := twoG.x
  y := -twoG.y
} := by native_decide

-- k = n + 2 at 320-bit width: crosses the identity and recovers `[2]G`.
example : scalarMul curve (toBits 320 (order + 2)) G = .affine twoG := by native_decide

-- k = 2n (320-bit encoding): the accumulator reaches the point at infinity
-- mid-run (`[n]G`) and the final step doubles it.
example : scalarMul curve (toBits 320 (2 * order)) G = .infinity := by native_decide

-- k = 2n - 1: ends one step before the second identity crossing, yielding `-G`.
example : scalarMul curve (toBits 320 (2 * order - 1)) G = .affine { x := G.x, y := -G.y } := by
  native_decide

-- k = 2n + 1 (320-bit encoding): the accumulator passes through the point at
-- infinity and recovers by the final add, `𝒪 + G = G`.
example : scalarMul curve (toBits 320 (2 * order + 1)) G = .affine G := by
  native_decide

-- k = 2n + 2: the same recovery path followed by one more doubling.
example : scalarMul curve (toBits 320 (2 * order + 2)) G = .affine twoG := by
  native_decide

-- Top-bit scalars exercise leading-one 256-bit paths.
example : scalarMul curve (toBits 256 (2 ^ 255)) G = .affine {
  x := 0xb23790a42be63e1b251ad6c94fdef07271ec0aada31db6c3e8bd32043f8be384
  y := 0xfc6b694919d55edbe8d50f88aa81f94517f004f4149ecb58d10a473deb19880e
} := by native_decide

example : scalarMul curve (toBits 256 (2 ^ 256 - 1)) G = .affine {
  x := 0x9166c289b9f905e55f9e3df9f69d7f356b4a22095f894f4715714aa4b56606af
  y := 0xf181eb966be4acb5cff9e16b66d809be94e214f06c93fd091099af98499255e7
} := by native_decide

-- Variable base: `[5]([2]G) = [10]G`.
example : scalarMul curve (toBits 256 5) twoG = .affine {
  x := 0xa0434d9e47f3c86235477c7b1ae6ae5d3442d49b1943c2b752a68e2a47e247c7
  y := 0x893aba425419bc27a3b6c7e693a24c696f794c2ed877a1593cbee53b037368d7
} := by native_decide

def randomScalar0 : ℕ :=
  0x86587cb7a684ba1060ef20d63f7793591d45dfb886c26f440ff8c69f98face83

def randomScalar1 : ℕ :=
  0x6c9ed6373487298bcc1b048db870cf8097b6eee66084046e0309b3b99f4d9608

def randomScalar2 : ℕ :=
  0x7f9bc64feaada942ef43a1d6ea519e9ec882668936660c964aa6b2a7f5a647d1

def randomScalar3 : ℕ :=
  0xda6ec6792448124b044739d62d62e0e8af88b87525b16d06649874fa21b779d8

def randomScalar4 : ℕ :=
  0x6e09f88c2459934f50f1f29525c41a8071c2ef9a925967d21ab335cf6d9c50e9

example : scalarMul curve (toBits 256 randomScalar0) G = .affine {
  x := 0xe14d34408eb0219e59de0ef1b75386868faa750d1006d003738e470a4385f8f8
  y := 0xa6c0c3e5e5ada9ffee9671b37b362b11b3c5b1b8bc03dc7f2fb23ce6efc52381
} := by native_decide

example : scalarMul curve (toBits 256 randomScalar1) G = .affine {
  x := 0x14913b63d104237278d37f417e89e108fd83c989722df65561e4966b076f880d
  y := 0xa85e933bea6bbea2fa1dac5c6ade9898579c577c6c670693b2cb0dfadd43207b
} := by native_decide

example : scalarMul curve (toBits 256 randomScalar2) G = .affine {
  x := 0xce6b80907f7d40d363f91e3b7fca0d7c370ea035661409acadea7803fe63b051
  y := 0xe40485459bf8e25b8d70ceb44bcde37cb1645ec418892bf158f6e64b7085ad1b
} := by native_decide

example : scalarMul curve (toBits 256 randomScalar3) G = .affine {
  x := 0x7a6e791b1d160a1df0b01a915b5d9e95d28ce902333d09ceb7c5af5e7db4be9e
  y := 0xb38677642ecb5cebd2724c6e11e171499cc84aa425907c0270a93db3e0a7d14b
} := by native_decide

example : scalarMul curve (toBits 256 randomScalar4) G = .affine {
  x := 0x58caf12a4c06907ba666480db14dd26c2ffb72b810bf8dcc2f013ce0921e24f6
  y := 0xef1a7283428cb819f1f2efb2856a0d79d8bc45157c6702ba26d1cd3fab3b6486
} := by native_decide

/-- Random variable base `[randomScalar0 + 1]G`. -/
def randomBase0 : Point Fp := {
  x := 0x63d67d52aa431a1444ffe34e65f1c42507d9d9eea8e9e267bbf11c8a58d4a8a3
  y := 0xb4a9517e7fb21abf778fa039b41c771e4b2ee3aa467ab19b1fa1bb55f7397862
}

/-- Random variable base `[randomScalar2 + 1]G`. -/
def randomBase1 : Point Fp := {
  x := 0x483cfb65678313825aa72dec553946827bf9df815f2c88173eb2dc34280b7004
  y := 0x8463b6928f77d24a45edcb499ba38eafc6f234e3166d4cdf1e01f38a4197b76a
}

/-- Random variable base `[randomScalar4 + 1]G`. -/
def randomBase2 : Point Fp := {
  x := 0xb6391aff8b6a735e4d3040858addbe0a90c6ecc238bce1358e27928155491077
  y := 0xe3640c1eacbfff63b1c162cc72934ce68f1d22c83b41f89258cbb44ecfd14e54
}

example : OnCurve curve randomBase0 := by native_decide
example : OnCurve curve randomBase1 := by native_decide
example : OnCurve curve randomBase2 := by native_decide

example : scalarMul curve (toBits 256 randomScalar1) randomBase0 = .affine {
  x := 0x2ad1121657f18d362c303b1d6a6f4165fb814523a676f111e90ffa2984857c7b
  y := 0xdc92159ab9a84a9ff37c2349dee94843c4c011f62f7cb51b16ad240441009a61
} := by native_decide

example : scalarMul curve (toBits 256 0) randomBase0 = .infinity := by native_decide
example : scalarMul curve (toBits 256 order) randomBase0 = .infinity := by native_decide

example : scalarMul curve (toBits 256 0xda6ec6792448124b044739d62d62e0e8af88b87525b16d06649874fa21b779d8)
    randomBase1 = .affine {
  x := 0x6c7329c2810dd5da7368cbb95a5def0115405e54a33f6c76e7b6bc81dae8d3a1
  y := 0xb88e9576d6500b6412fb927e0984d9d4bb91a74d6cc8bff801c09725c0277139
} := by native_decide

example : scalarMul curve (toBits 256 0x31ef6f5d3585f531cffee0abe12321c7d554033eda301bcd5a9b95b23132541d)
    randomBase2 = .affine {
  x := 0xad60e4a40fadf7d4ed887f02f2ef055bf141660c62c798454d8aadcd2d6885c6
  y := 0x6851127e56ccb63bfe74fcf536a71c3bab08fa309f74115aa425a4f8267b48f5
} := by native_decide

-- Variable base with a full-width scalar: `[kPi]([2]G)`.
example : scalarMul curve (toBits 256 kPi) twoG = .affine {
  x := 0x7cfb1a7312996f0a013a7f15c5d73c99876218030db10566612bfca5e258113c
  y := 0x39d2e5cd66367ec0a6f8201e284c9592ff98da7d5f91b3c3087db2ae82aed7ad
} := by native_decide

-- Scalars longer than the field size: a 320-bit encoding of `n + 5` wraps
-- around the group order to `[5]G`.
example : scalarMul curve (toBits 320 (order + 5)) G = .affine fiveG := by native_decide

/-- A 320-bit-wide scalar exceeding both the field size and the group order. -/
def kLong : ℕ :=
  0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c8913198a2e03707344

example : scalarMul curve (toBits 320 kLong) G = .affine {
  x := 0xcec32ea41fe641e17257712c86da4f0b75d6c9c290a5dd34978aa1970660d1ea
  y := 0xc03038e2b25d8e3dc2b40499554088fff3dba28b5270c0b30553165dad5816d7
} := by native_decide

-- Leading zero bits do not change the result: `[3]G` at 320-bit width.
example : scalarMul curve (toBits 320 3) G = .affine threeG := by native_decide

end Specs.Secp256k1.Tests
