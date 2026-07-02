import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ByteBlock

/-!
# `PadDigest` subcircuit — SHA-256 digest bytes → padded message representative `h`

The EMSA-PKCS1-v1_5 encoding step, **at the bit level**. It witnesses the 256
digest bits, checks them against the digest bytes with a single `ByteBlock`
assertion, then builds the full `4096`-bit encoded message (EM) by splicing those
bits into the **constant** DigestInfo / `00 01 FF…FF 00` PKCS#1 frame (`emBits`)
and packs the result into a `BigInt 34`. This is *where padding is enforced*: the
frame bits are literal constants, so the encoding is fixed by construction.

The output `h` denotes `os2ip (EMSA-PKCS1-v1_5-ENCODE(digest))` and is bounded by
`2 ^ 4088` (the top byte of EM is `0x00`), which lets `main` derive `h < n` from
the modulus bit-size assumption.

Soundness and completeness are fully proved.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace PadDigest

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open Specs.RSASSAPKCS1v15

/-- Bit-witness generator for the digest bytes: bit `i` is bit `i % 8` of
big-endian digest byte `31 - i / 8`. -/
def digestBitsWitness (digest : Var (fields digestBytesLen) (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : Vector (F circomPrime) 256 :=
  Vector.ofFn fun i : Fin 256 =>
    let dj : ℕ := 31 - i.val / 8
    let t : ℕ := i.val % 8
    let byteVal : ℕ :=
      if h : dj < digestBytesLen then
        (Expression.eval env.toEnvironment (digest[dj]'h)).val
      else 0
    ((byteVal / 2 ^ t % 2 : ℕ) : F circomPrime)

/-- The `main` circuit: witness the 256 digest bits, check them against the
digest bytes via one `ByteBlock` assertion, splice them into the constant PKCS#1
frame and pack the resulting EM bits into a `BigInt 34`. -/
def main (digest : Var (fields digestBytesLen) (F circomPrime)) :
    Circuit (F circomPrime) (Var (BigInt numLimbs) (F circomPrime)) := do
  let digBits ← witnessVector 256 (digestBitsWitness digest)
  ByteBlock.circuit { bytes := digest, bits := digBits }
  return Bytes.packLimbs (Bytes.emBits digBits)

instance elaborated :
    ElaboratedCircuit (F circomPrime) (fields digestBytesLen) (BigInt numLimbs) main := by
  elaborate_circuit

/-- Precondition: the digest is a genuine octet string (each byte `< 256`). -/
def Assumptions (digest : (fields digestBytesLen) (F circomPrime)) : Prop :=
  IsOctetString (fieldBytesToNat digest)

/-- Postcondition: the output is a normalized big integer, bounded by `2^4088`,
denoting `os2ip EM` where `EM` is the EMSA-PKCS1-v1_5 encoding of the digest. -/
def Spec (digest : (fields digestBytesLen) (F circomPrime))
    (out : BigInt numLimbs (F circomPrime)) : Prop :=
  out.Normalized limbBits ∧
    out.value limbBits < 2 ^ 4088 ∧
    ∃ EM : Vector ℕ 512,
      emsaPkcs1v15Encode? HashAlgorithm.sha256 (fieldBytesToNat digest) 512 = some EM ∧
        IsOctetString EM ∧
        out.value limbBits = os2ip EM

set_option linter.constructorNameAsVariable false in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  -- Abbreviation for the witnessed bit-variable vector.
  set digBits : Vector (Expression (F circomPrime)) 256 :=
    Vector.mapRange 256 (fun i ↦ var { index := i₀ + i }) with hdigBits
  -- The digest bytes (`input`) form an octet string ⇒ `ByteBlock` assumptions hold.
  have hbb_assum : ByteBlock.circuit.Assumptions { bytes := input, bits := Vector.map (Expression.eval env) digBits } := by
    intro dj
    have h := h_assumptions ⟨dj.val, dj.isLt⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map] at h
    exact h
  -- Run the `ByteBlock` subcircuit spec.
  obtain ⟨hbits_bool, hbyte_eq⟩ := h_holds hbb_assum
  -- Booleanity of the evaluated witnessed bits, as the deliverable lemmas want it.
  have hbool : ∀ (i : ℕ) (h : i < 256), (Expression.eval env (digBits[i]'h)).val < 2 := by
    intro i hi
    have := hbits_bool ⟨i, hi⟩
    simpa only [Fin.getElem_fin, Vector.getElem_map] using this
  -- Octet-string fact for the evaluated digest bytes, as the deliverable lemmas want it.
  have hoct : Specs.RSASSAPKCS1v15.IsOctetString
      (Vector.map (fun e => (Expression.eval env e).val) input_var) := by
    intro i
    rw [Fin.getElem_fin, Vector.getElem_map]
    rw [show (Expression.eval env (input_var[i.val]'i.isLt))
          = input[i.val]'i.isLt from by rw [← h_input, Vector.getElem_map]]
    have h := h_assumptions ⟨i.val, i.isLt⟩
    simpa only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map] using h
  -- Digest-consistency of the evaluated digest bytes vs. evaluated bits.
  have hdig : BytesLemmas.DigestConsistent env input_var digBits := by
    intro dj hdj
    have h := hbyte_eq ⟨dj, hdj⟩
    simp only [Vector.getElem_map] at h
    rw [← h_input] at h
    convert h using 3
    exact (Vector.getElem_map (Expression.eval env) (xs := input_var) hdj).symm
  -- `fieldBytesToNat input = Vector.map (eval) input_var`.
  have hfb : fieldBytesToNat input
      = Vector.map (fun e => (Expression.eval env e).val) input_var := by
    rw [← h_input]; unfold fieldBytesToNat; rw [Vector.map_map]; rfl
  -- Assemble the deliverables.
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- Normalized
    exact BytesLemmas.packLimbs_normalized env (emBits digBits)
      (BytesLemmas.emBits_bitsBool env digBits hbool)
  · -- value < 2^4088
    exact BytesLemmas.em_value_lt env digBits hbool
  · -- ∃ EM, encode = some EM ∧ IsOctetString EM ∧ value = os2ip EM
    obtain ⟨EM, hEM, hval⟩ := BytesLemmas.h_value_eq_emsaEncode env input_var digBits hoct hbool hdig
    refine ⟨EM, ?_, ?_, hval⟩
    · rw [hfb]; exact hEM
    · -- IsOctetString EM
      have hsome := BytesLemmas.emsaEncode_eq_emVec
        (Vector.map (fun e => (Expression.eval env e).val) input_var) hoct
      rw [hsome] at hEM
      cases hEM
      exact BytesLemmas.isOctetString_emVec _ hoct
  · -- requirement (channel-free)
    left
    simp only [ByteBlock.circuit, circuit_norm]

set_option linter.constructorNameAsVariable false in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec]
  have hdbl : digestBytesLen = 32 := rfl
  -- `.val` of a nat-cast below `circomPrime` is the nat itself.
  have hcast : ∀ (n : ℕ), n < 2 → ((n : F circomPrime)).val = n := by
    intro n hn
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hn (by norm_num [circomPrime]))]
  -- Each evaluated digest-byte variable equals the corresponding input byte.
  have hev : ∀ (dj : ℕ) (hdj : dj < digestBytesLen),
      input[dj]'hdj = Expression.eval env.toEnvironment (input_var[dj]'hdj) := by
    intro dj hdj
    rw [← h_input, Vector.getElem_map]
  -- The witnessed bit `i` evaluates to `byteVal_i / 2^(i%8) % 2`, where
  -- `byteVal_i = (eval input_var[31 - i/8]).val` is the big-endian digest byte.
  have hbiteval : ∀ (i : ℕ) (hi : i < 256),
      Expression.eval env.toEnvironment ((Vector.mapRange 256 fun i ↦ var { index := i₀ + i })[i]'hi)
        = (((Expression.eval env.toEnvironment (input_var[31 - i / 8]'(by rw [hdbl]; omega))).val
              / 2 ^ (i % 8) % 2 : ℕ) : F circomPrime) := by
    intro i hi
    rw [Vector.getElem_mapRange]
    rw [show (Expression.eval env.toEnvironment (var { index := i₀ + i })) = env.get (i₀ + i) from rfl]
    have henv := h_env ⟨i, hi⟩
    rw [henv]
    simp only [digestBitsWitness, Vector.getElem_ofFn]
    rw [dif_pos (show 31 - i / 8 < digestBytesLen from by rw [hdbl]; omega)]
  -- Each big-endian digest byte value is `< 256` (octet string assumption).
  have hbyte_lt : ∀ (dj : ℕ) (hdj : dj < 32),
      (Expression.eval env.toEnvironment (input_var[dj]'(by rw [hdbl]; omega))).val < 256 := by
    intro dj hdj
    have h := h_assumptions ⟨dj, by rw [hdbl]; omega⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map] at h
    rw [← hev dj hdj]; exact h
  -- Booleanity of the witnessed bits.
  have hbool : ∀ (i : ℕ) (hi : i < 256),
      (Expression.eval env.toEnvironment ((Vector.mapRange 256 fun i ↦ var { index := i₀ + i })[i]'hi)).val < 2 := by
    intro i hi
    rw [hbiteval i hi, hcast _ (Nat.mod_lt _ (by norm_num))]
    exact Nat.mod_lt _ (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · -- ByteBlock.Assumptions: digest bytes form an octet string.
    intro dj
    have h := h_assumptions ⟨dj.val, dj.isLt⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map] at h
    exact h
  · -- ByteBlock.Spec, part 1: bits boolean.
    intro i
    simp only [Vector.getElem_map]
    exact hbool i.val i.isLt
  · -- ByteBlock.Spec, part 2: byte = Σ bits · 2^t.
    intro dj
    simp only [Vector.getElem_map]
    -- LHS: the digest byte value.  RHS: bit-recomposition of the witnessed bits.
    show ZMod.val (input[dj.val]'dj.isLt) = _
    rw [hev dj.val dj.isLt]
    -- Each bit at `digestBitIndex dj t` evaluates to `byteVal_dj / 2^t % 2`.
    have hsum : (∑ t : Fin 8, (Expression.eval env.toEnvironment
            ((Vector.mapRange 256 fun i ↦ var { index := i₀ + i })[digestBitIndex dj.val t.val]'(by
              have := t.isLt; have := dj.isLt; simp only [digestBitIndex]; omega))).val * 2 ^ t.val)
        = ∑ t : Fin 8, ((Expression.eval env.toEnvironment
              (input_var[dj.val]'(by rw [hdbl]; omega))).val / 2 ^ t.val % 2) * 2 ^ t.val := by
      apply Finset.sum_congr rfl
      intro t _
      have ht := t.isLt
      have hdj := dj.isLt
      have hidx : (8 * (31 - dj.val) + t.val) / 8 = 31 - dj.val := by omega
      have hidx2 : (8 * (31 - dj.val) + t.val) % 8 = t.val := by omega
      rw [hbiteval (digestBitIndex dj.val t.val) (by simp only [digestBitIndex]; omega)]
      rw [hcast _ (Nat.mod_lt _ (by norm_num))]
      simp only [digestBitIndex]
      rw [show (8 * (31 - dj.val) + t.val) % 8 = t.val from by omega]
      rw [getElem_congr_idx (show 31 - (8 * (31 - dj.val) + t.val) / 8 = dj.val from by omega)]
    rw [hsum]
    -- Now `Σ_{t<8} (byteVal / 2^t % 2) · 2^t = byteVal` since `byteVal < 256 = 2^8`.
    rw [Fin.sum_univ_eq_sum_range
        (fun t => ((Expression.eval env.toEnvironment
          (input_var[dj.val]'(by rw [hdbl]; omega))).val / 2 ^ t % 2) * 2 ^ t) 8]
    exact (BytesLemmas.sum_bits_eq _ 8 (hbyte_lt dj.val dj.isLt)).symm

/-- The `PadDigest` formal circuit. -/
def circuit : FormalCircuit (F circomPrime) (fields digestBytesLen) (BigInt numLimbs) := {
  main, elaborated, Assumptions, Spec, soundness, completeness
}

end PadDigest
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
