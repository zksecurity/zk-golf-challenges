import Clean.Circuit
import Clean.Utils.Field

/-!
# GF(2) bit-packing helpers

Challenges over the binary field `F 2 = ZMod 2` (flock-style R1CS-over-GF(2))
represent words as flat bit vectors: every field element is a single bit, `+` is
XOR and `*` is AND. Since `2` is prime, the whole prime-field circuit machinery
applies unchanged. These helpers give the little-endian bijection between a
GF(2) bit vector and the natural-number words used by the pure specs.
-/

namespace Challenge.F2Bits

/-- The binary field `GF(2) = ZMod 2`. -/
@[reducible] def p2 : ℕ := 2

instance : Fact (Nat.Prime p2) := ⟨Nat.prime_two⟩

/-- Bit `k` of a GF(2) vector as a natural (`0`/`1`); out-of-range reads `0`. -/
@[reducible] def bitAt {N : ℕ} (v : Vector (F p2) N) (k : ℕ) : ℕ :=
  ZMod.val ((v[k]?).getD 0)

/-- The `w` bits starting at `w * i`, packed little-endian into a word. -/
def wordAt (w : ℕ) {N : ℕ} (v : Vector (F p2) N) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range w, bitAt v (w * i + j) * 2 ^ j

/-- Interpret a GF(2) bit vector as `n` little-endian `w`-bit words. -/
def toWords (w n : ℕ) {N : ℕ} (v : Vector (F p2) N) : Vector ℕ n :=
  Vector.ofFn fun i : Fin n => wordAt w v i.val

/-- Interpret an entire GF(2) bit vector as one little-endian natural. -/
def toNat {N : ℕ} (v : Vector (F p2) N) : ℕ := wordAt N v 0

end Challenge.F2Bits
