import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesLemmas
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.LessThan
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExp
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExpTheorems

/-!
# Helpers for the top-level `main` (RSASSA-PKCS1-v1_5 / SHA256 / 4096 / e = 65537)

This file gathers everything `Main.lean` needs but that is not one of the checker
obligations:

* the concrete parameter bundles (`numLimbs`, `bigIntParams4096`, `params4096`)
  and the `Fact (circomPrime > 2)` / `NeZero numLimbs` instances `main` relies on;
* the soundness/completeness support lemmas (`SoundnessLemmas` namespace): the
  channel-requirement obligations for the `LessThan` / `Equal` / `ModExp`
  subcircuits and the `verifySignature_true` / `verifySignature_invert`
  round-trip lemmas;
* the shallow `ModExp` output closed form (`modExp4096_output`), registered with
  `circuit_norm` so `circuit_proof_start` on `main` stays tractable.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace SoundnessLemmas

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open BytesLemmas
open Specs.RSASSAPKCS1v15

instance : Fact (circomPrime > 2) := ⟨by norm_num [circomPrime]⟩
instance : NeZero numLimbs := ⟨by decide⟩

/-- The `LessThan` subcircuit is channel-free, discharging its requirement. -/
theorem lessThan_requirements (P : BigIntParams circomPrime numLimbs)
    (env : Environment (F circomPrime))
    (x : Var (LessThan.Inputs numLimbs) (F circomPrime)) (offset : ℕ) :
    Operations.forAllNoOffset
      { interact := fun i ↦ i.Requirements env,
        subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
      ((LessThan.circuit P x).operations offset) := by
  simp only [circuit_norm]
  left
  rfl

/-- The `Equal` subcircuit is channel-free, discharging its requirement. -/
theorem equal_requirements (P : BigIntParams circomPrime numLimbs)
    (env : Environment (F circomPrime))
    (x : Var (Equal.Inputs numLimbs) (F circomPrime)) (offset : ℕ) :
    Operations.forAllNoOffset
      { interact := fun i ↦ i.Requirements env,
        subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
      ((Equal.circuit P x).operations offset) := by
  simp only [circuit_norm]
  left
  rfl

/-- The `ModExp` subcircuit is channel-free, discharging its requirement. -/
theorem modExp_requirements (P : RSAParams circomPrime numLimbs)
    (env : Environment (F circomPrime))
    (x : Var (ModExp.Inputs numLimbs) (F circomPrime)) (offset : ℕ) :
    Operations.forAllNoOffset
      { interact := fun i ↦ i.Requirements env,
        subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
      ((subcircuit (ModExp.circuit P) x).operations offset) := by
  simp only [circuit_norm]
  left
  rfl

/-! ## Final assembly: `verifySignature` is `true`. -/

/-- Given the verified facts, RFC 8017 `verifySignature` returns `true`. The public
exponent `e` is kept symbolic: the proof never inspects its value, and at the use
site this avoids elaborating the literal power `_ ^ 65537` (which would trip the
`exponentiation.threshold` reduction warning). -/
theorem verifySignature_true (e : ℕ)
    (n_bytes sig_bytes : Vector ℕ 512)
    (h_bytes : Vector ℕ 32)
    (EM : Vector ℕ 512)
    (h_sig_lt : Specs.RSASSAPKCS1v15.os2ip sig_bytes < Specs.RSASSAPKCS1v15.os2ip n_bytes)
    (h_enc : Specs.RSASSAPKCS1v15.emsaPkcs1v15Encode?
      Specs.RSASSAPKCS1v15.HashAlgorithm.sha256 h_bytes 512 = some EM)
    (h_pow : (Specs.RSASSAPKCS1v15.os2ip sig_bytes) ^ e
        % (Specs.RSASSAPKCS1v15.os2ip n_bytes)
      = Specs.RSASSAPKCS1v15.os2ip EM)
    (h_emoct : Specs.RSASSAPKCS1v15.IsOctetString EM) :
    Specs.RSASSAPKCS1v15.verifySignature
        Specs.RSASSAPKCS1v15.HashAlgorithm.sha256 e n_bytes h_bytes sig_bytes = true := by
  simp only [Specs.RSASSAPKCS1v15.verifySignature, Specs.RSASSAPKCS1v15.rsavp1?,
    if_pos h_sig_lt, h_enc, h_pow]
  rw [os2ip_i2osp_roundtrip EM h_emoct]
  simp

end SoundnessLemmas
end Solution.RSASSAPKCS1v15_SHA256_4096_65537


namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537

/-- Generic (circuit-abstract) projection of a subcircuit's output: it equals the
child circuit's declared output. Proved with the circuit abstract, so the `rfl`
is checked once, cheaply — a later instantiation at a heavy child (e.g. `ModExp`)
is a plain substitution and never forces the kernel to unfold the child's
operations. Used by `Main.computableWitness` to keep `ModExp`'s output opaque. -/
theorem subcircuit_output_eq {F : Type} [Field F] {β α : TypeMap}
    [ProvableType β] [ProvableType α]
    (c : FormalCircuit F β α) (b : Var β F) (n : ℕ) :
    (subcircuit c b).output n = c.output b n := rfl

/-- Companion to `subcircuit_output_eq`: the subcircuit's flat local length equals
the child's declared `localLength`. Also proved circuit-abstract, so instantiating
it at `ModExp` never forces the kernel to build `ModExp`'s operations. -/
theorem subcircuit_localLength_eq {F : Type} [Field F] {β α : TypeMap}
    [ProvableType β] [ProvableType α]
    (c : FormalCircuit F β α) (b : Var β F) (n : ℕ) :
    (subcircuit c b).localLength n = c.localLength b := rfl

/-- The circom prime exceeds 2 (needed by the comparison/carry gadgets). -/
instance : Fact (circomPrime > 2) := ⟨by norm_num [circomPrime]⟩

/-- Number of 121-bit limbs covering a 4096-bit modulus: `⌈4096 / 121⌉ = 34`
(`121 · 34 = 4114 ≥ 4096`). -/
abbrev numLimbs : ℕ := 34

instance : NeZero numLimbs := ⟨by decide⟩

/-- Big-integer parameters for 4096-bit RSA over the circom prime: 121-bit
limbs, 34 limbs, 129-bit carries. All field-size hypotheses hold comfortably
(the largest, `hp`, is `≈ 2^249 < 2^254`). -/
def bigIntParams4096 : BigIntParams circomPrime numLimbs where
  B := 121
  W := 129
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide

/-- RSA parameters for this instance: the 4096-bit big-integer params with the
public exponent `e = 65537 = 2^16 + 1`. -/
def params4096 : RSAParams circomPrime numLimbs where
  bigIntParams := bigIntParams4096
  e := 65537

/-- Shallow closed form for the `ModExp` subcircuit output, registered with
`circuit_norm` so it fires inside `circuit_proof_start`.
`eBits 65537 = true :: (15 falses ++ [true])`. The `decide` here is on a
small list and is cheap. -/
private lemma eBits_65537 :
    ModExp.eBits 65537 = true :: (List.replicate 15 false ++ [true]) := by decide

@[circuit_norm]
lemma modExp4096_output (input : Var (ModExp.Inputs numLimbs) (F circomPrime)) (offset : ℕ) :
    (ModExp.circuit params4096).output input offset
      = varFromOffset (BigInt numLimbs)
          (offset + (16 + 1) * ModExp.mulModLen (m := numLimbs) bigIntParams4096.B bigIntParams4096.W
            + numLimbs - ModExp.mulModLen (m := numLimbs) bigIntParams4096.B bigIntParams4096.W) := by
  have h : ModExp.eBits params4096.e
      = true :: false :: (List.replicate 14 false ++ [true]) := by
    show ModExp.eBits 65537 = _
    rw [eBits_65537, show (15 : ℕ) = 14 + 1 from rfl, List.replicate_succ, List.cons_append]
  rw [show (ModExp.circuit params4096).output input offset
        = (ModExp.elaborated params4096).output input offset from rfl,
      ← (ModExp.elaborated params4096).output_eq input offset]
  rw [ModExp.main_output_of_tail params4096 input offset
    (headBit := true) (b2 := false) (r2 := List.replicate 14 false ++ [true]) h]
  congr 2

end Solution.RSASSAPKCS1v15_SHA256_4096_65537


namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace MainTheorems

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSASSAPKCS1v15

/-- Base-`c` digit recomposition: `Σ_{k<m} (r / c^k % c) · c^k = r` when
`r < c^m` and `0 < c`. -/
theorem base_digit_recompose (c : ℕ) :
    ∀ (m r : ℕ), r < c ^ m →
      (∑ k ∈ Finset.range m, (r / c ^ k % c) * c ^ k) = r := by
  intro m
  induction m with
  | zero => intro r h; simp at h ⊢; omega
  | succ k ih =>
    intro r h
    rw [Finset.sum_range_succ']
    -- split off the `k = 0` term: `r % c`; the rest is `c · (recompose of r / c)`.
    have hquot : r / c < c ^ k := by
      rw [pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)
    have key : (∑ t ∈ Finset.range k, (r / c ^ (t + 1) % c) * c ^ (t + 1))
        = c * ∑ t ∈ Finset.range k, ((r / c) / c ^ t % c) * c ^ t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.div_div_eq_div_mul, show c ^ (t + 1) = c * c ^ t from by rw [pow_succ]; ring,
        show r / (c * c ^ t) = r / (c ^ t * c) from by rw [Nat.mul_comm]]
      ring
    rw [key, ih (r / c) hquot]
    simp only [pow_zero, Nat.div_one, mul_one]
    -- `r / c · c + r % c = r`.
    exact Nat.div_add_mod r c

theorem os2ip_of_i2osp (r : ℕ) (v : Vector ℕ 512) (h : i2osp r 512 = some v) :
    os2ip v = r := by
  -- `v` is the octet string of base-256 digits of `r`, so it is octet, and
  -- `os2ip` over the roundtrip recovers `r`. `i2osp_some_inv` keeps the literal
  -- power `256 ^ 512` out of the goal (it lives behind the symbolic `256 ^ len`).
  obtain ⟨hr, hv⟩ := BytesLemmas.i2osp_some_inv h
  subst hv
  rw [BytesLemmas.os2ip_vec_eq_sum_le]
  -- digit `k` (little-endian, byte `511 - k`) is `r / 256^k % 256`.
  have hsum : (∑ k ∈ Finset.range 512,
        (Vector.ofFn (fun i : Fin 512 => r / 256 ^ (512 - 1 - i.val) % 256))[511 - k]! * 2 ^ (8 * k))
      = ∑ k ∈ Finset.range 512, (r / 256 ^ k % 256) * 256 ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [getElem!_pos _ (511 - k) (by omega), Vector.getElem_ofFn]
    rw [show (512 - 1 - (⟨511 - k, by omega⟩ : Fin 512).val) = k from by simp only []; omega]
    rw [show (2 : ℕ) ^ (8 * k) = 256 ^ k from by rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]]
  rw [hsum]
  exact base_digit_recompose 256 512 r hr

/-- Invert the RFC 8017 verification predicate: from
`verifySignature sha256 65537 n h sig = true` recover `os2ip sig < os2ip n` and
the recovered-value equation `os2ip sig ^ 65537 % os2ip n = os2ip EM` for the EM
witnessed by the (deterministic) encoder. -/
theorem verifySignature_invert
    (n_bytes sig_bytes : Vector ℕ 512) (h_bytes : Vector ℕ 32)
    (EM : Vector ℕ 512)
    (h_enc : emsaPkcs1v15Encode? HashAlgorithm.sha256 h_bytes 512 = some EM)
    (h_verify : verifySignature HashAlgorithm.sha256 65537 n_bytes h_bytes sig_bytes = true) :
    os2ip sig_bytes < os2ip n_bytes ∧
      (os2ip sig_bytes) ^ 65537 % (os2ip n_bytes) = os2ip EM := by
  simp only [verifySignature, rsavp1?] at h_verify
  -- `recovered` must be `some _`, forcing `sig < n`.
  by_cases hlt : os2ip sig_bytes < os2ip n_bytes
  · rw [if_pos hlt, h_enc] at h_verify
    -- `i2osp (sig^e % n) 512 == some EM` is `true`.
    rw [beq_iff_eq] at h_verify
    refine ⟨hlt, ?_⟩
    rw [← os2ip_of_i2osp _ EM h_verify]
  · rw [if_neg hlt] at h_verify
    simp at h_verify

end MainTheorems
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
