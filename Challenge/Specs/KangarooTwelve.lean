import Clean.Utils.Vector

/-!
# KangarooTwelve permutation

The reduced Keccak permutation used by TurboSHAKE and KangarooTwelve:
Keccak-p[1600, n_r = 12].  The state layout follows RFC 9861 Appendix A.1:
lane `(x, y)` occupies bits `64 * (x + 5 * y)` through
`64 * (x + 5 * y) + 63`, with each 64-bit lane interpreted little-endian.
-/

namespace Specs.KangarooTwelve

@[reducible] def laneBits : ℕ := 64
@[reducible] def lanes : ℕ := 25
@[reducible] def stateBits : ℕ := laneBits * lanes
@[reducible] def rounds : ℕ := 12

abbrev State (α : Type) := Vector α stateBits

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

def theta {α : Type} [Add α] (s : State α) : State α :=
  Vector.ofFn fun i : Fin stateBits =>
    let x := xOf i
    let y := yOf i
    let z := zOf i
    bit s x y z + columnParity s (x + 4) z + columnParity s (x + 1) (z + 63)

def rhoOffset (x y : ℕ) : ℕ :=
  match x % 5, y % 5 with
  | 0, 0 => 0
  | 1, 0 => 1
  | 2, 0 => 62
  | 3, 0 => 28
  | 4, 0 => 27
  | 0, 1 => 36
  | 1, 1 => 44
  | 2, 1 => 6
  | 3, 1 => 55
  | 4, 1 => 20
  | 0, 2 => 3
  | 1, 2 => 10
  | 2, 2 => 43
  | 3, 2 => 25
  | 4, 2 => 39
  | 0, 3 => 41
  | 1, 3 => 45
  | 2, 3 => 15
  | 3, 3 => 21
  | 4, 3 => 8
  | 0, 4 => 18
  | 1, 4 => 2
  | 2, 4 => 61
  | 3, 4 => 56
  | 4, 4 => 14
  | _, _ => 0

def rhoPi {α : Type} (s : State α) : State α :=
  Vector.ofFn fun i : Fin stateBits =>
    let x' := xOf i
    let y' := yOf i
    let z := zOf i
    let srcX := (3 * y' + x') % 5
    let srcY := x'
    bit s srcX srcY (z + laneBits - rhoOffset srcX srcY)

def chi {α : Type} [Add α] [Mul α] [One α] (s : State α) : State α :=
  Vector.ofFn fun i : Fin stateBits =>
    let x := xOf i
    let y := yOf i
    let z := zOf i
    bit s x y z + (1 + bit s (x + 1) y z) * bit s (x + 2) y z

/-- RFC 9861 Appendix A.1 round constants, as little-endian 64-bit words. -/
def roundConstants : Vector ℕ rounds := #v[
  0x000000008000808B,
  0x800000000000008B,
  0x8000000000008089,
  0x8000000000008003,
  0x8000000000008002,
  0x8000000000000080,
  0x000000000000800A,
  0x800000008000000A,
  0x8000000080008081,
  0x8000000000008080,
  0x0000000080000001,
  0x8000000080008008
]

def natBit (n z : ℕ) : ℕ := (n / 2 ^ z) % 2

def roundConstantBit {α : Type} [Zero α] [One α] (r : Fin rounds) (z : ℕ) : α :=
  if natBit roundConstants[r] z = 0 then 0 else 1

def iota {α : Type} [Add α] [Zero α] [One α] (r : Fin rounds) (s : State α) : State α :=
  Vector.ofFn fun i : Fin stateBits =>
    let x := xOf i
    let y := yOf i
    let z := zOf i
    if x = 0 ∧ y = 0 then
      bit s x y z + roundConstantBit r z
    else
      bit s x y z

def round {α : Type} [Add α] [Mul α] [Zero α] [One α] (r : Fin rounds) (s : State α) :
    State α :=
  iota r (chi (rhoPi (theta s)))

def keccakP1600_12 {α : Type} [Add α] [Mul α] [Zero α] [One α] (s : State α) :
    State α :=
  let s := round (0 : Fin rounds) s
  let s := round (1 : Fin rounds) s
  let s := round (2 : Fin rounds) s
  let s := round (3 : Fin rounds) s
  let s := round (4 : Fin rounds) s
  let s := round (5 : Fin rounds) s
  let s := round (6 : Fin rounds) s
  let s := round (7 : Fin rounds) s
  let s := round (8 : Fin rounds) s
  let s := round (9 : Fin rounds) s
  let s := round (10 : Fin rounds) s
  round (11 : Fin rounds) s

end Specs.KangarooTwelve
