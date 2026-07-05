import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Utils.Primes
import Clean.Utils.Bits
import Challenge.Specs.Keccak

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Solution.KeccakF1600

/-- The Keccak state: 25 lanes of 64 bits, one field element per bit. -/
abbrev KeccakBitState := ProvableVector (fields 64) 25

/-- Interpret a bit vector as a natural number (LSB at index 0). -/
def valueBits (bits : Vector (F p) 64) : ℕ :=
  Finset.univ.sum fun (i : Fin 64) => bits[i].val * 2^i.val

/-- All bits are boolean (0 or 1). -/
def Normalized (w : Vector (F p) 64) : Prop :=
  ∀ i : Fin 64, w[i] = 0 ∨ w[i] = 1

/-- Lane values of a state. -/
def stateValue (s : KeccakBitState (F p)) : Vector ℕ 25 :=
  s.map valueBits

/-- All lanes are boolean bit vectors. -/
def StateNormalized (s : KeccakBitState (F p)) : Prop :=
  ∀ i : Fin 25, Normalized s[i.val]

/-- A row of θ parities: 5 lanes of 64 bits. -/
abbrev KeccakBitRow := ProvableVector (fields 64) 5

/-- Lane values of a row. -/
def rowValue (s : KeccakBitRow (F p)) : Vector ℕ 5 :=
  s.map valueBits

/-- All row lanes are boolean bit vectors. -/
def RowNormalized (s : KeccakBitRow (F p)) : Prop :=
  ∀ i : Fin 5, Normalized s[i.val]

/-- Rotate a lane left by `k` bits (mod 64) in value: since bits are LSB-first,
`z[i] = a[(i + 64 − k mod 64) mod 64]`, i.e. an index rotation by `64 − k mod 64`. -/
def rotl {T : Type} (k : ℕ) (a : Vector T 64) : Vector T 64 :=
  a.rotate (64 - k % 64)

/-- Bitwise NOT: maps each bit a[i] ↦ 1 − a[i]. -/
def notBits {T : Type} [One T] [Sub T] (a : Vector T 64) : Vector T 64 :=
  a.map fun ai => 1 - ai

/-- XOR with a 64-bit constant: flips bit i exactly where `c` has bit i set. -/
def xorConst {T : Type} [One T] [Sub T] (c : ℕ) (a : Vector T 64) : Vector T 64 :=
  Vector.ofFn fun (i : Fin 64) =>
    if c.testBit i.val then 1 - a[i] else a[i]

/-- The flat index of the lane that π moves *to* flat index `j`. -/
def piSource (j : Fin 25) : Fin 25 :=
  ⟨(j.val % 5 + 3 * (j.val / 5)) % 5 + 5 * (j.val % 5), by omega⟩

/-- The row neighbour (x+1, y) of the lane at flat index `j`. -/
def chiSource1 (j : Fin 25) : Fin 25 :=
  ⟨(j.val % 5 + 1) % 5 + 5 * (j.val / 5), by omega⟩

/-- The row neighbour (x+2, y) of the lane at flat index `j`. -/
def chiSource2 (j : Fin 25) : Fin 25 :=
  ⟨(j.val % 5 + 2) % 5 + 5 * (j.val / 5), by omega⟩

/-- ι as pure wiring: XOR the round constant into lane 0 only (`xorConst 0 = id`
elsewhere), as a per-lane map so the χ-output var is not indexed at lane 0. -/
def iotaWire {T : Type} [One T] [Sub T] (rc : ℕ) (s : Vector (Vector T 64) 25) :
    Vector (Vector T 64) 25 :=
  Vector.mapFinRange 25 fun j => xorConst (if j.val = 0 then rc else 0) s[j.val]

/-- ρ then π as pure wiring: lane `j` of the result is lane `piSource j` of the
input, rotated left by its ρ offset. -/
def rhoPiWire {T : Type} (s : Vector (Vector T 64) 25) : Vector (Vector T 64) 25 :=
  Vector.ofFn fun (j : Fin 25) =>
    rotl (Specs.Keccak.rhoOffsets[(piSource j).val]) s[(piSource j).val]

/-- Slice a 1600-bit string into 25 lanes: bit z of lane i is bit 64·i + z. -/
def toLanes {T : Type} (bits : Vector T 1600) : Vector (Vector T 64) 25 :=
  Vector.ofFn fun (i : Fin 25) => Vector.ofFn fun (z : Fin 64) => bits[64 * i.val + z.val]

/-- Flatten 25 lanes back into a 1600-bit string. -/
def fromLanes {T : Type} (s : Vector (Vector T 64) 25) : Vector T 1600 :=
  Vector.ofFn fun (j : Fin 1600) => s[j.val / 64][j.val % 64]

/-- θ column parities: C[x] = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]. -/
def thetaCSpec (A : Vector ℕ 25) : Vector ℕ 5 :=
  Vector.ofFn fun x =>
    A[x.val] ^^^ A[x.val + 5] ^^^ A[x.val + 10] ^^^ A[x.val + 15] ^^^ A[x.val + 20]

/-- θ combined parities: D[x] = C[x−1] ⊕ ROT(C[x+1], 1). -/
def thetaDSpec (C : Vector ℕ 5) : Vector ℕ 5 :=
  Vector.ofFn fun x =>
    C[(x.val + 4) % 5] ^^^ Specs.Keccak.rotLeft 64 C[(x.val + 1) % 5] 1

/-- θ update: A[x,y] ⊕ D[x]. -/
def thetaXorSpec (A : Vector ℕ 25) (D : Vector ℕ 5) : Vector ℕ 25 :=
  Vector.ofFn fun i => A[i.val] ^^^ D[i.val % 5]

/-- ρ then π: lane `j` is lane `piSource j` rotated by its ρ offset. -/
def rhoPiSpec (A : Vector ℕ 25) : Vector ℕ 25 :=
  Vector.ofFn fun j =>
    Specs.Keccak.rotLeft 64 A[(piSource j).val] (Specs.Keccak.rhoOffsets[(piSource j).val])

/-- χ: A[x,y] ⊕ (¬A[x+1,y] ∧ A[x+2,y]). -/
def chiSpec (A : Vector ℕ 25) : Vector ℕ 25 :=
  Vector.ofFn fun j =>
    A[j.val] ^^^ (Specs.Keccak.notLane 64 A[(chiSource1 j).val] &&& A[(chiSource2 j).val])

/-- ι: XOR the round constant into lane (0, 0). -/
def iotaSpec (rc : ℕ) (A : Vector ℕ 25) : Vector ℕ 25 :=
  A.set 0 (A[0] ^^^ rc)

end Solution.KeccakF1600
end
