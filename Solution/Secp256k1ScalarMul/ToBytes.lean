import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.ToBytesTheorems

/-!
# Byte decomposition of an emulated field element — `ToBytes`

`FormalCircuit` decomposing an emulated field element (4×64-bit limbs) into
its 32 bytes, little-endian (byte `i` holds bits `[8·i, 8·i + 8)`).

## Strategy

Witness the 32 bytes, range-check each to 8 bits
(`Gadgets.ToBits.rangeCheck`), and assert the affine per-limb recomposition

  `limb_k = Σ_{t < 8} byte_{8·k + t} · 2^(8·t)`

(no cross-limb carries, since the limbs are byte-aligned; each equation's
sides are `< 2^64 ≪ circomPrime`, so there is no field wraparound). The
byte range checks make the decomposition unique, and together with the
recomposition they subsume the limb range check.

The output bytes are fresh witness variables — affine, degree 1 — so they
can be exposed directly as circuit outputs.

Soundness and completeness are fully proved, with the arithmetic content
factored into `ToBytesTheorems` (`soundness_core`, `completeness_core`).
-/

namespace Solution.Secp256k1ScalarMul
namespace ToBytes

/-- Little-endian byte `i` of a natural number. -/
def byteOfNat (v i : ℕ) : ℕ := v / 2 ^ (8 * i) % 256

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields coordBytes) (F circomPrime)) := do
  -- witness the 32 little-endian bytes of the value
  let bytes ← ProvableType.witness (α := fields coordBytes) fun env =>
    Vector.ofFn fun i : Fin coordBytes =>
      ((byteOfNat (evalEmu env x) i.val : ℕ) : F circomPrime)

  -- each byte is 8 bits
  Circuit.forEach bytes (fun b => Gadgets.ToBits.rangeCheck 8 (by decide) b)

  -- per-limb affine recomposition: limb_k = Σ_{t<8} byte_{8k+t} · 2^(8t)
  let constraints := Vector.ofFn fun k : Fin numLimbs =>
    (Fin.foldl bytesPerLimb (fun acc t =>
      acc + bytes[bytesPerLimb * k.val + t.val]'(by
          have hk := k.isLt; have ht := t.isLt
          simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
          omega)
        * (((2 ^ (8 * t.val) : ℕ) : F circomPrime) : Expression (F circomPrime)))
      0)
    - x[k.val]'k.isLt
  Circuit.forEach constraints assertZero

  return bytes

instance elaborated : ElaboratedCircuit (F circomPrime) Emu (fields coordBytes) main := by
  elaborate_circuit

/-- Precondition: the input is a normalized emulated field element. -/
def Assumptions (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits

/-- Postcondition: the outputs are bytes and recompose (little-endian) to the
value of the input. -/
def Spec (x : Emu (F circomPrime)) (out : fields coordBytes (F circomPrime)) : Prop :=
  (∀ i : Fin coordBytes, (out[i]).val < 256) ∧
    Limbs.fromLimbs 8 (out.toList.map ZMod.val) = x.value limbBits

theorem soundness :
    Soundness (Input := Emu) (Output := fields coordBytes) (F circomPrime)
      main Assumptions Spec := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck]
  obtain ⟨h_bytes, h_rows⟩ := h_holds
  refine ⟨fun i => lt_of_lt_of_eq (h_bytes i) (by norm_num), ?_⟩
  apply soundness_core env i₀ input h_bytes
  intro k
  have h := h_rows k
  simp only [Vector.getElem_ofFn] at h
  rw [eval_row_iff] at h
  rw [← h_input, Vector.getElem_map]
  exact h

theorem completeness :
    Completeness (Input := Emu) (Output := fields coordBytes) (F circomPrime)
      main Assumptions := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck]
  obtain ⟨h_wit, -⟩ := h_env
  -- the witnessed value is the input's value
  have hv : evalEmu env input_var = BigInt.value limbBits input := by
    rw [evalEmu, h_input]
    rfl
  -- each witnessed byte is the corresponding byte of the input's value
  have hbyte : ∀ i : Fin coordBytes,
      env.get (i₀ + i.val)
        = ((byteOfNat (BigInt.value limbBits input) i.val : ℕ) : F circomPrime) := by
    intro i
    rw [h_wit i]
    simp only [Vector.getElem_ofFn, hv]
  -- a byte value is < 2^8
  have hbyte_lt : ∀ v j : ℕ, byteOfNat v j < 2 ^ 8 :=
    fun v j => Nat.mod_lt _ (by norm_num)
  refine ⟨fun i => ?_, fun k => ?_⟩
  · -- range checks: the witnessed bytes are 8-bit
    rw [hbyte i, ZMod.val_natCast_of_lt (lt_trans (hbyte_lt _ _)
      (lt_trans (by norm_num) two_pow_64_lt_circomPrime))]
    exact hbyte_lt _ _
  · -- recomposition rows
    simp only [Vector.getElem_ofFn]
    rw [eval_row_iff]
    have hx : Expression.eval env.toEnvironment (input_var[k.val]'k.isLt)
        = input[k.val]'k.isLt := by
      rw [← h_input, Vector.getElem_map]
    rw [hx]
    show (∑ t : Fin bytesPerLimb,
        env.get (i₀ + (bytesPerLimb * k.val + t.val))
          * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = input[k.val]'k.isLt
    apply completeness_core input h_assumptions k
    intro t
    have hidx : bytesPerLimb * k.val + t.val < coordBytes := by
      have hk := k.isLt
      have ht := t.isLt
      simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
      omega
    rw [hbyte ⟨bytesPerLimb * k.val + t.val, hidx⟩]
    simp only [byteOfNat]

/-- The `ToBytes` formal circuit: little-endian byte decomposition of an
emulated field element. -/
def circuit : FormalCircuit (F circomPrime) Emu (fields coordBytes) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end ToBytes
end Solution.Secp256k1ScalarMul
