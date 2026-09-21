import Challenge.Specs.Bls12381G1

-- Test vectors for naive double-and-add scalar multiplication on BLS12-381
-- G1 (`y² = x³ + 4` over the 381-bit prime field). All [k]G / [k]P values,
-- the subgroup-membership facts, and the curve parameters were
-- cross-checked against py_ecc's reference BLS12-381 implementation
-- (`py_ecc.bls12_381`). The parameters (base field prime, subgroup order
-- r, cofactor h₁, and the G1 generator) are the IETF/Zcash BLS12-381
-- parameters; the tests below re-derive them from the BLS parameterization
-- and check the generator lies on the curve and in the prime-order subgroup.

namespace Specs.Bls12381G1.Tests

open Specs.ShortWeierstrass Specs.Bls12381G1

/-- MSB-first bit decomposition of `k`, for building test scalars. Bits of
`k` at position `n` and above are dropped. -/
def toBits (n k : ℕ) : Vector ℕ n :=
  Vector.ofFn fun i => k / 2 ^ (n - 1 - i.val) % 2

-- `toBits` is MSB-first: 0xb5 = 0b10110101.
example : toBits 8 0xb5 = #v[1, 0, 1, 1, 0, 1, 0, 1] := by native_decide

-- `toBits` is a right inverse of the spec's bit decoder.
example : scalarOfBits (toBits 255 0x18ebbb95eed0e13) = 0x18ebbb95eed0e13 := by
  native_decide

-- The BLS parameterization: with z = -0xd201000000010000,
--   r  = z⁴ - z² + 1,
--   p  = (z-1)²(z⁴-z²+1)/3 + z  (a 381-bit prime),
--   h₁ = (z-1)²/3.
-- `z` is negative; the transcription below uses `u = -z` and re-expresses the
-- identities over `ℕ` (z⁴ = u⁴, z² = u², (z-1)² = (u+1)², z⁴-z²+1 = r):
--   r  = u⁴ - u² + 1,
--   p  = (u+1)²·r/3 - u,
--   h₁ = (u+1)²/3.

/-- The BLS parameter `|z|` (with `z = -u`, `u` below). -/
def z : ℕ := 0xd201000000010000

example : order = z ^ 4 - z ^ 2 + 1 := by native_decide
example : p = (z + 1) ^ 2 * (z ^ 4 - z ^ 2 + 1) / 3 - z := by native_decide
example : cofactor = (z + 1) ^ 2 / 3 := by native_decide

example : p < 2 ^ 381 := by native_decide
example : 2 ^ 380 < p := by native_decide
example : order < 2 ^ 255 := by native_decide
example : scalarBits = 255 := by native_decide

-- The generator lies on the curve, as do the curve parameters we transcribed.
example : OnCurve curve G := by native_decide

-- The generator generates the prime-order subgroup: [r]G = 𝒪.
example : nsmul order (.affine G) = .infinity := by native_decide
example : InSubgroup (.affine G) := by native_decide

-- Small multiples of G stay in the subgroup: the subgroup is closed.

/-- `[2]G`. -/
def twoG : Point Fp := {
  x := 0x572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e
  y := 0x166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d28
}

/-- `[3]G`. -/
def threeG : Point Fp := {
  x := 0x9ece308f9d1f0131765212deca99697b112d61f9be9a5f1f3780a51335b3ff981747a0b2ca2179b96d2c0c9024e5224
  y := 0x32b80d3a6f5b09f8a84623389c5f80ca69a0cddabc3097f9d9c27310fd43be6e745256c634af45ca3473b0590ae30d1
}

/-- `[5]G`. -/
def fiveG : Point Fp := {
  x := 0x10e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc
  y := 0x16ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e2
}

example : InSubgroup (.affine twoG) := by native_decide
example : InSubgroup (.affine fiveG) := by native_decide

-- The cofactor is nontrivial: E(𝔽_p) has points outside the subgroup. The
-- point `H` below is killed by `h₁`'s complement side (it is `[r]Q` for an
-- on-curve `Q` and `h₁·r` is the full group order), and it is *not* killed
-- by `[r]·`, so it lies outside the order-`r` subgroup. This is exactly the
-- input the variable-base challenge's assumptions rule out.
def H : Point Fp := {
  x := 0x7652583c291f70025fe8cb6d9849caddc75bdf3eef50b778751294f8433ca94fb2760125723af33e8298cfd9074a560
  y := 0xde08326a1918652db2cce187802abb2b98fa6c8dd65f73ac421c42e2dfef2a6bfbd48106681bf268dd2396890de621a
}

example : OnCurve curve H := by native_decide
example : ¬ InSubgroup (.affine H) := by native_decide

-- Concrete cofactor-clearing spot checks: [h₁]P lands in the subgroup both
-- for subgroup points and for the out-of-subgroup H.
example : InSubgroup (nsmul cofactor (.affine G)) := by native_decide
example : InSubgroup (nsmul cofactor (.affine H)) := by native_decide

-- k = 0: the naive algorithm never leaves the point at infinity.
example : scalarMul curve (toBits 255 0) G = .infinity := by native_decide

-- k = 1: `[1]G = G`.
example : scalarMul curve (toBits 255 1) G = .affine G := by native_decide

-- k = 2: a pure doubling path.
example : scalarMul curve (toBits 255 2) G = .affine twoG := by native_decide

-- k = 3: doubling followed by a final add.
example : scalarMul curve (toBits 255 3) G = .affine threeG := by native_decide

-- k = 5.
example : scalarMul curve (toBits 255 5) G = .affine fiveG := by native_decide

-- The fixed-base spec does *not* carry the variable-base spec's subgroup
-- obligation: the base point is the fixed generator `G`, known to generate
-- the prime-order subgroup (checked above by `native_decide`), so the output
-- `[k]G` automatically lies in it.

-- k = r - 1: yields `-G = (G.x, -G.y)`.
example : scalarMul curve (toBits 255 (order - 1)) G
    = .affine { x := G.x, y := -G.y } := by native_decide

-- k = r: the run ends with the `[r-1]G + G = (-G) + G` cancellation, so the
-- result is the point at infinity.
example : scalarMul curve (toBits 255 order) G = .infinity := by native_decide

-- k = r + 1 at 255-bit width: crosses the identity and recovers `[1]G`.
example : scalarMul curve (toBits 255 (order + 1)) G = .affine G := by native_decide

-- k = r + 2: the same wrap-around followed by one more add: `[2]G`.
example : scalarMul curve (toBits 255 (order + 2)) G = .affine twoG := by native_decide

-- k = 2r (a 256-bit scalar, so 256 bits): the accumulator reaches the point
-- at infinity mid-run and the final step doubles it.
example : scalarMul curve (toBits 256 (2 * order)) G = .infinity := by native_decide

-- The top-bit scalar `2²⁵⁵ - 1` exceeds the subgroup order; the naive
-- algorithm computes `[(2²⁵⁵-1) mod r]G`.
example : scalarMul curve (toBits 255 (2 ^ 255 - 1)) G = .affine {
  x := 0x487be9bea3a7c11195a6a2f8b939d3a0a1427fa31d3ee09b570988b75970dcc5634ae489b822cfd81aaf4f972fc8886
  y := 0x107daaed8c46595711daf34979be8e29a45e707ba1072ede29cf8affe9fb0e654db8c83a31df533cddf4e037b9723ff1
} := by native_decide

-- Direct group-law exceptional cases.
example : add curve .infinity (.affine G) = .affine G := by native_decide
example : add curve (.affine G) .infinity = .affine G := by native_decide
example : add curve (.affine G) (.affine { x := G.x, y := -G.y }) = .infinity := by
  native_decide

/-- A large scalar (the leading hex digits of π's fraction; 255 bits). -/
def kPi : ℕ := 0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89

-- `toBits` produces genuine bit arrays at the challenge width.
example : IsBitArray (toBits 255 kPi) := by native_decide

example : scalarMul curve (toBits 255 kPi) G = .affine {
  x := 0x9b8eb1b6c8e2bf67fe98f422325b689565571b0567841ad809b1373c1fe2ce6e1cfb06b2ccdc0bfc0cf8ec136733aa8
  y := 0x84d7fd90c707b34013b9ce4b75ac4984d149e1de485f71af9570187292e154f4a67820ef7a3961d3da830260d243cc8
} := by native_decide

def randomScalar0 : ℕ :=
  0x86587cb7a684ba1060ef20d63f7793591d45dfb886c26f440ff8c69f98face83

def randomScalar1 : ℕ :=
  0x6c9ed6373487298bcc1b048db870cf8097b6eee66084046e0309b3b99f4d9608

def randomScalar2 : ℕ :=
  0xda6ec6792448124b044739d62d62e0e8af88b87525b16d06649874fa21b779d8

def randomScalar3 : ℕ :=
  0x31ef6f5d3585f531cffee0abe12321c7d554033eda301bcd5a9b95b23132541d

-- Random fixed-base vectors.
example : scalarMul curve (toBits 255 0x18ebbb95eed0e13) G = .affine {
  x := 0xe8115c8089ad37a162f621de187887c0b3774c9422de3de4ae2034a066de5bf9f9b32a9787402f7cd4dd75dc27e28bc
  y := 0xdf708b1da39f3a808cf8bc49149ebee51bcbdf97b718728f38acebb180d80e330150874426112c9e12d93aad7ec35b4
} := by native_decide

-- Variable base: base points in the prime-order subgroup (multiples of G).

/-- `[randomScalar0]G`, a subgroup point. -/
def P0 : Point Fp := {
  x := 0x95a655f3d2349fc21b8c8eda40f10462ea81b960a4cd95075a32fd7d86e07ff205aea930cab0ff48b9b3eb6f05c3717
  y := 0x14209a90e5da45786b3a44df9211a119c3182409625ebafa29fe044c5083e64ddd1c87d5291c5b833fd999a41465543c
}

/-- `[randomScalar1]G`, a subgroup point. -/
def P1 : Point Fp := {
  x := 0x14a20e23e7dfa4033017f7d39d5a4e643a206f8df2726c68a32ec909bf05f000ceb3865deecadc38e89bcfd396996166
  y := 0x2350f8d63fc86f46a0582fbaf3375d867531066274691eb35b5f16e412b6f98a54cae68fdcc59708a6327d9d28e5df9
}

example : OnCurve curve P0 := by native_decide
example : OnCurve curve P1 := by native_decide

-- The base points we use are in the subgroup, as the assumptions require.
example : InSubgroup (.affine P0) := by native_decide
example : InSubgroup (.affine P1) := by native_decide

-- `[randomScalar2]P0`. (`randomScalar2` is a 256-bit literal — larger than the
-- challenge's 255-bit window — so this vector is checked at 256 bits; the
-- relation accepts any bit sequence.)
example : scalarMul curve (toBits 256 randomScalar2) P0 = .affine {
  x := 0x420ab482cd399b61fbb33e5727a910da071184edd954a691490470ec8ea413161edb9d95b96da5b5e55c38a05a7f227
  y := 0x969c2471c7686fce6ba04735bfea5dcdbd9a4b94487a0beab837423836f322b44afda6f88d76aaca5b5d5bfc3db7da
} := by native_decide

-- `[randomScalar3]P1`.
example : scalarMul curve (toBits 255 randomScalar3) P1 = .affine {
  x := 0x4203b16a121f97092a0d2636b7d701eb77ec22c2f27c9ac74be107e237b91d2f8e8937834d917febab63106aab93cb
  y := 0xb8ccc75e50a1ae71f57f4da5833c4218907b444d6327b3463b819f17d80cfeb1216a3e869f338d29277876f2d503ed0
} := by native_decide

-- k = 0 with a subgroup base: the identity.
example : scalarMul curve (toBits 255 0) P0 = .infinity := by native_decide

-- k = r with a subgroup base: back to the identity, so the output's
-- subgroup membership in the spec is witnessed by the infinity case too.
example : scalarMul curve (toBits 255 order) P0 = .infinity := by native_decide

end Specs.Bls12381G1.Tests
