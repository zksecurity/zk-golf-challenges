import Challenge.Specs.Keccak
import Clean.Utils.Vector

/-!
# Keccak-p[800, nᵣ]

The Keccak-p[800] permutation family (FIPS 202, Section 3.3): Keccak-p[800, nᵣ]
is the last `nᵣ` of the 22 rounds of Keccak-f[800], i.e. rounds `22 - nᵣ`, ...,
`21`. `keccakF800 = keccakP 22` is the full permutation, and the challenge
target `keccakP800_12 = keccakP 12` runs rounds 10 through 21.

This is the bit-level, ring-polymorphic formulation used by the GF(2)
challenge, in the style of `Specs.KangarooTwelve`. Its ρ offsets and round
constants are taken from the lane-level reference `Specs.Keccak`
(`rhoOffsets` reduced mod 32 and `roundConstants` truncated to 32 bits);
`Tests/KeccakP800.lean` checks that the two formulations agree and that the
22-round permutation matches the published XKCP test vectors.

The state layout is the FIPS 202 / XKCP layout: lane `(x, y)` occupies bits
`32 * (x + 5 * y)` through `32 * (x + 5 * y) + 31`, with each 32-bit lane
interpreted little-endian.
-/

namespace Specs.KeccakP800

@[reducible] def laneBits : ℕ := 32
@[reducible] def lanes : ℕ := 25
@[reducible] def stateBits : ℕ := laneBits * lanes
/-- Keccak-f[800] has 12 + 2ℓ = 22 rounds (ℓ = 5). -/
@[reducible] def keccakFRounds : ℕ := 22

abbrev State (α : Type) := Vector α stateBits

/-- Index of a round of Keccak-f[800], selecting its round constant. -/
abbrev RoundIndex := Fin keccakFRounds

def bitIndex (x y z : ℕ) : Fin stateBits :=
  ⟨((x % 5) + 5 * (y % 5)) * laneBits + (z % laneBits), by
    have hx : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hy : y % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hz : z % laneBits < laneBits := Nat.mod_lt _ (by norm_num)
    unfold stateBits laneBits lanes
    omega⟩

@[reducible] def bit {α : Type} (s : State α) (x y z : ℕ) : α :=
  s[bitIndex x y z]

@[reducible] def xOf (i : Fin stateBits) : ℕ := (i.val / laneBits) % 5
@[reducible] def yOf (i : Fin stateBits) : ℕ := ((i.val / laneBits) / 5) % 5
@[reducible] def zOf (i : Fin stateBits) : ℕ := i.val % laneBits

def columnParity {α : Type} [Add α] (s : State α) (x z : ℕ) : α :=
  bit s x 0 z + bit s x 1 z + bit s x 2 z + bit s x 3 z + bit s x 4 z

-- θ: A[x,y,z] ← A[x,y,z] ⊕ C[x−1,z] ⊕ C[x+1,z−1], with C the column parities.
def theta {α : Type} [Add α] (s : State α) : State α :=
  Vector.ofFn fun i : Fin stateBits =>
    let x := xOf i
    let y := yOf i
    let z := zOf i
    bit s x y z + columnParity s (x + 4) z + columnParity s (x + 1) (z + 31)

/-- The ρ rotation offset of lane `(x, y)`: the Keccak offset reduced mod the lane width. -/
def rhoOffset (x y : ℕ) : ℕ :=
  Specs.Keccak.rhoOffsets[(x % 5) + 5 * (y % 5)]'(by omega) % laneBits

-- ρ then π: lane (x, y) is rotated by its ρ offset and moved to (y, 2x + 3y),
-- so the lane arriving at (x', y') comes from (x' + 3y', x').
def rhoPi {α : Type} (s : State α) : State α :=
  Vector.ofFn fun i : Fin stateBits =>
    let x' := xOf i
    let y' := yOf i
    let z := zOf i
    let srcX := (3 * y' + x') % 5
    let srcY := x'
    bit s srcX srcY (z + laneBits - rhoOffset srcX srcY)

-- χ: A[x,y,z] ← A[x,y,z] ⊕ (¬A[x+1,y,z] ∧ A[x+2,y,z]), the only non-linear step.
def chi {α : Type} [Add α] [Mul α] [One α] (s : State α) : State α :=
  Vector.ofFn fun i : Fin stateBits =>
    let x := xOf i
    let y := yOf i
    let z := zOf i
    bit s x y z + (1 + bit s (x + 1) y z) * bit s (x + 2) y z

/-- The Keccak-f[800] round constants RC[0], ..., RC[21]: the 64-bit Keccak
constants truncated to 32-bit lanes (FIPS 202, Section 3.2.5). -/
def roundConstants : Vector ℕ keccakFRounds :=
  Vector.ofFn fun i : RoundIndex => Specs.Keccak.roundConstants[i.val] % 2 ^ laneBits

def natBit (n z : ℕ) : ℕ := (n / 2 ^ z) % 2

def roundConstantBit {α : Type} [Zero α] [One α] (r : RoundIndex) (z : ℕ) : α :=
  if natBit roundConstants[r] z = 0 then 0 else 1

-- ι: A[0,0] ← A[0,0] ⊕ RC[r]
def iota {α : Type} [Add α] [Zero α] [One α] (r : RoundIndex) (s : State α) : State α :=
  Vector.ofFn fun i : Fin stateBits =>
    let x := xOf i
    let y := yOf i
    let z := zOf i
    if x = 0 ∧ y = 0 then
      bit s x y z + roundConstantBit r z
    else
      bit s x y z

/-- Round `r` of Keccak-f[800]: ι[r] ∘ χ ∘ π ∘ ρ ∘ θ. -/
def round {α : Type} [Add α] [Mul α] [Zero α] [One α] (r : RoundIndex) (s : State α) :
    State α :=
  iota r (chi (rhoPi (theta s)))

/--
  Keccak-p[800, nᵣ] (FIPS 202, Section 3.3): the last `nᵣ` rounds of Keccak-f[800],
  i.e. rounds `22 - nᵣ`, ..., `21` in that order. Unfolding the recursion,
  `keccakP (n + 1) s = keccakP n (round (21 - n) s)`.
-/
def keccakP {α : Type} [Add α] [Mul α] [Zero α] [One α] :
    (nr : ℕ) → nr ≤ keccakFRounds → State α → State α
  | 0, _, s => s
  | n + 1, h, s => keccakP n (Nat.le_of_succ_le h) (round ⟨keccakFRounds - 1 - n, by omega⟩ s)

/-- The full Keccak-f[800] permutation: all 22 rounds. -/
def keccakF800 {α : Type} [Add α] [Mul α] [Zero α] [One α] (s : State α) : State α :=
  keccakP keccakFRounds (Nat.le_refl _) s

/-- Keccak-p[800, 12]: the last 12 rounds of Keccak-f[800] (rounds 10, ..., 21). -/
def keccakP800_12 {α : Type} [Add α] [Mul α] [Zero α] [One α] (s : State α) : State α :=
  keccakP 12 (by decide) s

end Specs.KeccakP800
