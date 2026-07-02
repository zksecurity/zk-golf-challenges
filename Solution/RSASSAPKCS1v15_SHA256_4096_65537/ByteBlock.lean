import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Bytes
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Normalize
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Equal
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ByteBlockTheorems
import Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface

/-!
# `ByteBlock` assertion — 32 big-endian bytes are consistent with 256 bits

A `FormalAssertion` (no output) that ties together a 32-byte big-endian block and
a 256-bit vector: it boolean-checks every bit and asserts each byte equals the
little-endian sum of its 8 bits (`digestBitIndex` layout: byte `dj`, `dj = 0` the
block MSB, occupies bits `[8·(31−dj), 8·(31−dj)+8)`).

Both the bytes and the bits are *inputs*: the caller (`BytesToBigInt` /
`PadDigest`) witnesses the bits itself (once, as one clean `varFromOffset`) and
passes 32-byte / 256-bit slices to this assertion. That keeps `packLimbs` running
over the caller's clean witnessed bits (cheap to elaborate), while the bulk
booleanity/consistency constraints are factored here so the caller's direct
operation count stays small enough for its `FormalCircuit` bundle.

Soundness and completeness are fully proved.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace ByteBlock

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open Specs.RSASSAPKCS1v15

/-- Inputs: a 32-byte block and its 256 bits. -/
structure Inputs (F : Type) where
  bytes : Vector F 32
  bits : Vector F 256
deriving ProvableStruct

/-- The `main` circuit: boolean-check the 256 bits and assert byte/bit
consistency. No output (it is an assertion). The two constraint loops are inlined
directly: the booleanity loop asserts `bit · (bit - 1) = 0` for each of the 256
bits, and the digest-consistency loop asserts each of the 32 bytes equals the
little-endian recomposition `byteFromBits` of its 8 bits. -/
def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  Circuit.forEach input.bits (fun b => assertZero (b * (b - 1)))
  Circuit.forEach
    (Vector.ofFn fun dj : Fin 32 =>
      input.bytes[dj.val]'dj.isLt - Bytes.byteFromBits input.bits (Bytes.digestBitIndex dj.val 0))
    assertZero

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

/-- Precondition (for completeness): the block is a genuine octet string. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  ∀ dj : Fin 32, (input.bytes[dj.val]'dj.isLt).val < 256

/-- Postcondition: the bits are boolean and reconstruct each input byte. -/
def Spec (input : Inputs (F circomPrime)) : Prop :=
  (∀ i : Fin 256, (input.bits[i.val]'i.isLt).val < 2) ∧
    (∀ dj : Fin 32, (input.bytes[dj.val]'dj.isLt).val
      = ∑ t : Fin 8, (input.bits[Bytes.digestBitIndex dj.val t.val]'(by
          have := dj.isLt; have := t.isLt
          simp only [Bytes.digestBitIndex]; omega)).val * 2 ^ t.val)

/-- A field element with `.val < 2` is a root of `x · (x − 1)` (the booleanity
constraint), used to discharge the booleanity loop in completeness. -/
private theorem mulSubOne_eq_zero_of_val_lt_two (x : F circomPrime) (h : x.val < 2) :
    x * (x + -1) = 0 := by
  have hcase : x = 0 ∨ x = 1 := by
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with h0 | h1
    · exact Or.inl ((ZMod.val_eq_zero x).mp h0)
    · refine Or.inr ?_
      rw [← ZMod.natCast_zmod_val x, h1, Nat.cast_one]
  rcases hcase with rfl | rfl <;> ring

set_option linter.constructorNameAsVariable false in
theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  obtain ⟨h_bool_holds, h_dig_holds⟩ := h_holds
  -- bit `i` evaluates to a boolean (`< 2`).
  have hbool : ∀ (i : ℕ) (hi : i < 256),
      (Expression.eval env (input_var_bits[i]'hi)).val < 2 :=
    val_lt_two_of_holds env input_var_bits h_bool_holds
  -- translate `input_bits[i] = Expression.eval env input_var_bits[i]`.
  have hbits_eq : ∀ (i : ℕ) (hi : i < 256),
      input_bits[i]'hi = Expression.eval env (input_var_bits[i]'hi) := by
    intro i hi
    rw [← h_input.2, Vector.getElem_map]
  have hbytes_eq : ∀ (j : ℕ) (hj : j < 32),
      input_bytes[j]'hj = Expression.eval env (input_var_bytes[j]'hj) := by
    intro j hj
    rw [← h_input.1, Vector.getElem_map]
  -- read off the per-byte digest-consistency fact from the inlined `forEach`.
  have hz : ∀ (dj : ℕ) (hdj : dj < 32),
      Expression.eval env ((input_var_bytes[dj]'hdj)
        - byteFromBits input_var_bits (digestBitIndex dj 0)) = 0 := by
    intro dj hdj
    have hd := h_dig_holds ⟨dj, hdj⟩
    rw [Vector.getElem_ofFn] at hd
    exact hd
  have hdig : BytesLemmas.DigestConsistent env input_var_bytes input_var_bits :=
    digestConsistent_of_facts env input_var_bytes input_var_bits hbool hz
  refine ⟨?_, ?_⟩
  · -- bits are boolean
    intro i
    rw [hbits_eq i.val i.isLt]
    exact hbool i.val i.isLt
  · -- byte = Σ bits · 2^t
    intro dj
    rw [hbytes_eq dj.val dj.isLt, hdig dj.val dj.isLt]
    apply Finset.sum_congr rfl
    intro t _
    rw [hbits_eq (digestBitIndex dj.val t.val) (by have := t.isLt; simp only [digestBitIndex]; omega)]

set_option linter.constructorNameAsVariable false in
theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  obtain ⟨h_bits_bool, h_byte_eq⟩ := h_spec
  -- translate evaluated-vs-witness facts for bits and bytes.
  have hbits_eq : ∀ (i : ℕ) (hi : i < 256),
      input_bits[i]'hi = Expression.eval env.toEnvironment (input_var_bits[i]'hi) := by
    intro i hi
    rw [← h_input.2, Vector.getElem_map]
  have hbytes_eq : ∀ (j : ℕ) (hj : j < 32),
      input_bytes[j]'hj = Expression.eval env.toEnvironment (input_var_bytes[j]'hj) := by
    intro j hj
    rw [← h_input.1, Vector.getElem_map]
  -- booleanity of the evaluated bits.
  have hbool : ∀ (i : ℕ) (hi : i < 256),
      (Expression.eval env.toEnvironment (input_var_bits[i]'hi)).val < 2 := by
    intro i hi
    rw [← hbits_eq i hi]
    exact h_bits_bool ⟨i, hi⟩
  refine ⟨?_, ?_⟩
  · -- booleanity loop: each bit satisfies `bit · (bit + -1) = 0`.
    intro i
    exact mulSubOne_eq_zero_of_val_lt_two _ (hbool i.val i.isLt)
  · -- digest-consistency loop: each byte equals its bit recomposition.
    -- The per-byte value identity (keyed on a `Fin 32`, the literal digest length).
    have key : ∀ (j : Fin 32),
        (Expression.eval env.toEnvironment (input_var_bytes[(j : ℕ)]'j.isLt)).val
          = ∑ t : Fin 8, (Expression.eval env.toEnvironment
              (input_var_bits[8 * (31 - (j : ℕ)) + t.val]'(by
                have := t.isLt; have := j.isLt; omega))).val * 2 ^ t.val := by
      intro j
      rw [← hbytes_eq j.val j.isLt, h_byte_eq j]
      apply Finset.sum_congr rfl
      intro t _
      rw [hbits_eq (digestBitIndex j.val t.val)
          (by have := t.isLt; simp only [digestBitIndex]; omega),
        getElem_congr_idx (show digestBitIndex j.val t.val = 8 * (31 - j.val) + t.val from by
          simp [digestBitIndex])]
    intro i
    have hi32 : i.val < 32 := i.isLt
    rw [Vector.getElem_ofFn, eval_sub, sub_eq_zero]
    -- both sides are `< 256 < circomPrime`, so equal `.val` gives equality.
    apply ZMod.val_injective
    have hbase : 8 * (31 - i.val) + 8 ≤ 256 := by omega
    rw [BytesLemmas.byteFromBits_val_gen (n := 256) env.toEnvironment input_var_bits
        (8 * (31 - i.val)) hbase hbool]
    exact key ⟨i.val, hi32⟩

/-- The `ByteBlock` formal assertion. -/
def circuit : FormalAssertion (F circomPrime) Inputs :=
  { main := main
    elaborated := elaborated
    Assumptions := Assumptions
    Spec := Spec
    soundness := by simp only [soundness]
    completeness := by simp only [completeness]
    exposedChannels_eq := by intro _ _ exposed h; simp at h }

end ByteBlock
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
