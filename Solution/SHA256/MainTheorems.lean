import Challenge.Instances.SHA256.Interface
import Solution.SHA256.PaddingTheorems

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface

/-!
# Helper lemmas for the top-level `Main` circuit

Gadget-private helpers (and the witness definitions) used by `main`, its
`soundness`/`completeness` proofs. These re-prove the private `SHA256Rounds`
helpers and bridge `paddedBlock` to `specBlock`. They are stated over the
concrete `circomPrime`. Shared lemmas live in `Theorems`/`PaddingTheorems`.
-/

instance hCircomPrimeLarge : Fact (circomPrime > 2^33) := ⟨by
  norm_num [circomPrime]⟩

def paddedBitsWitness (input : Var Input (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : SHA256PaddedBits (F circomPrime) :=
  paddedBitsValue ((eval env input.message).map ZMod.val) (Expression.eval env input.messageLen).val

def lenFlagsWitness (input : Var Input (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : fields inputBufferLen (F circomPrime) :=
  lenFlagsValue (Expression.eval env input.messageLen).val

/-! ## Local helpers (re-proving private SHA256Rounds helpers) -/

/-- `constWord32 n` evaluated is always normalized. -/
lemma normalized_constWord32 (env : Environment (F circomPrime)) (n : ℕ) :
    Normalized (Vector.map (Expression.eval env) (constWord32 (p := circomPrime) n)) := by
  intro i
  have h : (n / 2^i.val % 2 : ℕ) = 0 ∨ (n / 2^i.val % 2 : ℕ) = 1 := by omega
  rcases h with h | h
  · left; simp [constWord32, Expression.eval, h]
  · right; simp [constWord32, Expression.eval, h]

lemma valueBits_constWord32 (env : Environment (F circomPrime)) (n : ℕ) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p := circomPrime) n)) = n % 2^32 := by
  simp only [valueBits, constWord32]
  have h2 : ∀ i : Fin 32, ((n / 2^i.val % 2 : ℕ) : F circomPrime).val = n / 2^i.val % 2 := by
    intro i
    have hp : 2^33 < circomPrime := hCircomPrimeLarge.out
    have hlt : (n / 2^i.val % 2 : ℕ) < circomPrime := by omega
    exact ZMod.val_natCast_of_lt hlt
  have heq : (∑ i : Fin 32, (Vector.map (Expression.eval env)
        (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F circomPrime))))[i].val * 2^i.val)
      = ∑ i : Fin 32, (n / 2^i.val % 2) * 2^i.val := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [show (Vector.map (Expression.eval env)
          (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F circomPrime))))[i] =
        ((n / 2^i.val % 2 : ℕ) : F circomPrime) from by
      simp [Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]]
    rw [h2 i]
  rw [heq]
  have key : ∀ (m : ℕ), ∑ i : Fin m, (n / 2^i.val % 2) * 2^i.val = n % 2^m := by
    intro m
    induction m with
    | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, pow_zero, Nat.mod_one]
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ih, Nat.mod_pow_succ]; ring
  exact key 32

lemma valueBits_constWord32_of_lt (env : Environment (F circomPrime)) {n : ℕ} (h : n < 2^32) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p := circomPrime) n)) = n := by
  rw [valueBits_constWord32, Nat.mod_eq_of_lt h]

lemma H0_lt (i : ℕ) (hi : i < 8) : Specs.SHA256.H0[i]'hi < 2^32 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    h|h|h|h|h|h|h|h <;> subst h <;> simp [Specs.SHA256.H0]

/-- The `i`-th word of the evaluated H0 const state is `Vector.map (Expression.eval env) (constWord32 H0[i])`. -/
lemma state0_getElem (env : Environment (F circomPrime)) (i : ℕ) (hi : i < 8) :
    (eval env (Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val])))[i]'hi =
      Vector.map (Expression.eval env)
        ((Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val]))[i]'hi) := by
  rw [show Vector.map (Expression.eval env)
        ((Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val]))[i]'hi) =
      eval env ((Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val]))[i]'hi)
      from (CircuitType.eval_var_fields env _).symm]
  exact (getElem_eval_vector (α := fields 32) env
    (Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val])) i hi).symm

/-- `eval env state0` equals `Specs.SHA256.H0` (as values), where `state0` is the H0 const state. -/
lemma state0_value (env : Environment (F circomPrime)) :
    Vector.map valueBits
      (eval env (Vector.ofFn fun i => constWord32 (p := circomPrime) (Specs.SHA256.H0[i.val]))) = Specs.SHA256.H0 := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map, state0_getElem env i hi, Vector.getElem_ofFn]
  exact valueBits_constWord32_of_lt env (H0_lt i hi)

/-- Each word of `eval env state0` is normalized. -/
lemma state0_normalized (env : Environment (F circomPrime)) (i : ℕ) (hi : i < 8) :
    Normalized ((eval env (Vector.ofFn fun i => constWord32 (p := circomPrime) (Specs.SHA256.H0[i.val])))[i]'hi) := by
  rw [state0_getElem env i hi, Vector.getElem_ofFn]
  exact normalized_constWord32 env _

/-! ## Padded-block bridging (paddedBlock ↦ specBlock) -/

/-- The byte index for block `b`, word `w`, byte-in-word `k`. -/
lemma paddedBytes_idx_lt {b w k : ℕ} (hb : b < 5) (hw : w < 16) (hk : k < 4) :
    b * 64 + 4 * w + k < paddedBytesLen := by
  simp only [paddedBytesLen, paddedBlocksLen]; omega

lemma getElem_index_eq {α : Type*} {n : ℕ} (v : Vector α n) (i j : ℕ)
    (hi : i < n) (hj : j < n) (h : i = j) : v[i]'hi = v[j]'hj := by
  subst h; rfl

/-- Word `w` of block `b` of `paddedBlock` is the same word vector as `paddedWord` at byte `b*64+4w+k`,
for any `k < 4`. -/
lemma paddedBlock_word_eq (padded : Var SHA256PaddedBits (F circomPrime))
    (b : Fin paddedBlocksLen) (w : Fin 16) {k : ℕ} (hk : k < 4) :
    (paddedBlock padded b)[w] =
      paddedWord padded ⟨b.val * 64 + 4 * w.val + k, paddedBytes_idx_lt b.isLt w.isLt hk⟩ := by
  rw [paddedBlock, Fin.getElem_fin, Vector.getElem_ofFn]
  apply Vector.ext
  intro bit hbit
  rw [Vector.getElem_ofFn, paddedBit, paddedWord, Vector.getElem_ofFn]
  apply getElem_index_eq
  have hw : w.val < 16 := w.isLt
  have h1 : (b.val * 64 + 4 * w.val + k) / 64 = b.val := by omega
  have h2 : (b.val * 64 + 4 * w.val + k) % 64 = 4 * w.val + k := by omega
  have h3 : (4 * w.val + k) / 4 = w.val := by omega
  rw [h1, h2, h3]; ring

/-- Byte `k` of word `w` of block `b` of the evaluated padded bits is the spec padded byte,
given CheckPad's per-byte spec equation. -/
lemma wordByteVal_block (env : Environment (F circomPrime))
    (padded : Var SHA256PaddedBits (F circomPrime)) (msg : Vector ℕ inputBufferLen) (ℓ : ℕ)
    (h_bytes : ∀ j : Fin paddedBytesLen,
      paddedByteVal (Vector.map (Expression.eval env) padded) j = specPaddedByte msg ℓ j.val)
    (b : Fin paddedBlocksLen) (w : Fin 16) (k : Fin 4) :
    wordByteVal (Vector.map (Expression.eval env) ((paddedBlock padded b)[w])) k
      = specPaddedByte msg ℓ (b.val * 64 + 4 * w.val + k.val) := by
  have hjlt : b.val * 64 + 4 * w.val + k.val < paddedBytesLen :=
    paddedBytes_idx_lt b.isLt w.isLt k.isLt
  rw [paddedBlock_word_eq padded b w k.isLt]
  have hk4 : (b.val * 64 + 4 * w.val + k.val) % 4 = k.val := by have := k.isLt; omega
  have hbyte := wordByteVal_paddedWord env padded
    ⟨b.val * 64 + 4 * w.val + k.val, hjlt⟩
  rw [h_bytes ⟨b.val * 64 + 4 * w.val + k.val, hjlt⟩] at hbyte
  convert hbyte using 2
  exact Fin.ext hk4.symm

/-- The evaluated `paddedBlock b` matches `specBlock`. -/
lemma paddedBlock_value (env : Environment (F circomPrime))
    (padded : Var SHA256PaddedBits (F circomPrime)) (msg : Vector ℕ inputBufferLen) (ℓ : ℕ)
    (h_bytes : ∀ j : Fin paddedBytesLen,
      paddedByteVal (Vector.map (Expression.eval env) padded) j = specPaddedByte msg ℓ j.val)
    (b : Fin paddedBlocksLen) :
    Vector.map valueBits (eval env (paddedBlock padded b)) = specBlock msg ℓ b.val := by
  apply Vector.ext
  intro w hw
  rw [Vector.getElem_map,
    ← getElem_eval_vector (α := fields 32) env (paddedBlock padded b) w hw,
    CircuitType.eval_var_fields]
  rw [valueBits_eq_bytesToWord32BE]
  rw [specBlock, Specs.SHA256.bytesToBlock, Vector.getElem_mapFinRange]
  have e0 := wordByteVal_block env padded msg ℓ h_bytes b ⟨w, hw⟩ 0
  have e1 := wordByteVal_block env padded msg ℓ h_bytes b ⟨w, hw⟩ 1
  have e2 := wordByteVal_block env padded msg ℓ h_bytes b ⟨w, hw⟩ 2
  have e3 := wordByteVal_block env padded msg ℓ h_bytes b ⟨w, hw⟩ 3
  simp only [Fin.isValue, Fin.getElem_fin] at e0 e1 e2 e3
  rw [show ((paddedBlock padded b)[w]'hw) = (paddedBlock padded b)[(⟨w, hw⟩ : Fin 16)] from rfl] at *
  rw [e0, e1, e2, e3, Vector.getElem_ofFn, Vector.getElem_ofFn, Vector.getElem_ofFn,
    Vector.getElem_ofFn]
  congr 1

/-- Each word of an evaluated `paddedBlock` is normalized, given booleanity of the padded bits. -/
lemma paddedBlock_normalized (env : Environment (F circomPrime))
    (padded : Var SHA256PaddedBits (F circomPrime))
    (h_bool : ∀ i : Fin paddedBitsLen, IsBool (Vector.map (Expression.eval env) padded)[i])
    (b : Fin paddedBlocksLen) (w : ℕ) (hw : w < 16) :
    Normalized (eval env ((paddedBlock padded b)[w]'hw)) := by
  intro bit
  rw [CircuitType.eval_var_fields]
  -- (paddedBlock padded b)[w][bit] = padded[b*512 + w*32 + bit]
  have hidx : b.val * 16 * 32 + w * 32 + bit.val < paddedBitsLen := by
    have hb : b.val < 5 := b.isLt
    have := bit.isLt
    simp only [paddedBitsLen, paddedBlocksLen]; omega
  have hget : (Vector.map (Expression.eval env) ((paddedBlock padded b)[w]'hw))[bit] =
      (Vector.map (Expression.eval env) padded)[b.val * 16 * 32 + w * 32 + bit.val]'hidx := by
    rw [paddedBlock, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_ofFn,
      paddedBit, Vector.getElem_map]
  rw [hget]
  have := h_bool ⟨b.val * 16 * 32 + w * 32 + bit.val, hidx⟩
  simp only [IsBool] at this
  exact this

/-- Final digest-selection step: if each candidate state's value equals the chain state,
the selected digest word matches the SHA-256 spec output. -/
lemma digest_final
    (states : Vector (SHA256State (F circomPrime)) paddedBlocksLen)
    (msg : Vector ℕ inputBufferLen) (ℓ : ℕ) (hℓ : ℓ ≤ inputBufferLen)
    (hsv : ∀ k : Fin paddedBlocksLen, Vector.map valueBits states[k] = chainState msg ℓ (k.val + 1))
    (w : Fin 8) (hw : w.val < 8) :
    valueBits ((stateForLen states ℓ)[w.val]'hw) =
      (Specs.SHA256.sha256 (Specs.SHA256.truncate msg ℓ hℓ))[w.val]'hw := by
  have hpos := numBlocksForLen_pos ℓ
  have hle := numBlocksForLen_le hℓ
  simp only [paddedBlocksLen] at hle
  rw [stateForLen_eq states ℓ hℓ]
  rw [sha256_eq_chainState msg ℓ hℓ]
  -- numBlocksForLen ℓ - 1 corresponds to index k with k+1 = numBlocksForLen ℓ
  set nb := numBlocksForLen ℓ with hnb
  have hk : nb - 1 < paddedBlocksLen := by simp only [paddedBlocksLen]; omega
  have := hsv ⟨nb - 1, hk⟩
  have hkv : (⟨nb - 1, hk⟩ : Fin paddedBlocksLen).val + 1 = nb := by simp only; omega
  rw [hkv] at this
  rw [← this, Vector.getElem_map]
  congr 2

end Solution.SHA256
