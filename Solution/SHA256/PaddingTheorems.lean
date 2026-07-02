import Solution.SHA256.Common
import Solution.SHA256.Theorems

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256
open Challenge.Instances.SHA256.Interface (inputBufferLen)

instance : Fact (p > 2) := .mk (by
  have h : (2 : ℕ) < 2^33 := by norm_num
  exact h.trans h_large.out)

/-- Every message needs at least one padding block. -/
theorem numBlocksForLen_pos (len : ℕ) : 1 ≤ numBlocksForLen len := by
  unfold numBlocksForLen
  have hmod : (55 + 64 - len % 64) % 64 < 64 := Nat.mod_lt _ (by omega)
  have hmodlen : len % 64 < 64 := Nat.mod_lt _ (by omega)
  have hge : len % 64 ≤ len := Nat.mod_le _ _
  -- need len + zeros + 9 ≥ 64
  have : 64 ≤ len + (55 + 64 - len % 64) % 64 + 9 := by
    omega
  exact Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)

/-- Messages shorter than the input buffer fit in `paddedBlocksLen` blocks. -/
theorem numBlocksForLen_le {len : ℕ} (h : len ≤ inputBufferLen) :
    numBlocksForLen len ≤ paddedBlocksLen := by
  unfold numBlocksForLen
  simp only [inputBufferLen] at h
  have hmod : (55 + 64 - len % 64) % 64 < 64 := Nat.mod_lt _ (by omega)
  have hlt : (len + (55 + 64 - len % 64) % 64 + 9) / 64 < 6 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  simp only [paddedBlocksLen]
  omega

/-- `getElem` of a chunk of `Vector.toChunks`: entry `i` of chunk `b` is entry
`b * m + i` of the flat vector. -/
private theorem getElem_toChunks {α : Type} {n : ℕ} (m : ℕ+) (v : Vector α (n * m))
    (b i : ℕ) (hb : b < n) (hi : i < m) :
    ((v.toChunks m)[b]'hb)[i]'hi = v[b * m + i]'(by
      have : b * m + i < n * m := by
        calc b * m + i < b * m + m := by omega
          _ = (b + 1) * m := by ring
          _ ≤ n * m := by
            apply Nat.mul_le_mul_right; omega
      exact this) := by
  have hidx : b * m + i < n * m := by
    calc b * m + i < b * m + m := by omega
      _ = (b + 1) * m := by ring
      _ ≤ n * m := by apply Nat.mul_le_mul_right; omega
  have hdiv : (b * m + i) / m = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ m.pos, Nat.div_eq_of_lt hi]; omega
  have hmod : (b * m + i) % m = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hi
  have hflat : (v.toChunks m).flatten[b * m + i]'hidx =
      (v.toChunks m)[(b * m + i) / m][(b * m + i) % m] :=
    Vector.getElem_flatten (xss := v.toChunks m) (i := b * m + i) hidx
  rw [Vector.toChunks_flatten] at hflat
  simp only [hdiv, hmod] at hflat
  exact hflat.symm

/-- `getElem_toChunks` specialised to chunk size `64`, with the flat index stated
as `b * 64 + i` (no `ℕ+` coercion noise). -/
private theorem getElem_toChunks64 {α : Type} {n : ℕ} (v : Vector α (n * 64))
    (b i : ℕ) (hb : b < n) (hi : i < 64) (hbi : b * 64 + i < n * 64) :
    ((v.toChunks ⟨64, by decide⟩)[b]'hb)[i]'hi = v[b * 64 + i]'hbi :=
  getElem_toChunks ⟨64, by decide⟩ v b i hb hi

/-- The `b`-th 16-word block of the spec-padded byte stream. -/
def specBlock (msg : Vector ℕ inputBufferLen) (len b : ℕ) : Vector ℕ 16 :=
  Specs.SHA256.bytesToBlock (Vector.ofFn fun (i : Fin 64) => specPaddedByte msg len (b * 64 + i.val))

/-- The compression-chain state after `k` blocks of the spec-padded stream. -/
def chainState (msg : Vector ℕ inputBufferLen) (len : ℕ) : ℕ → Vector ℕ 8
  | 0 => Specs.SHA256.H0
  | k + 1 => Specs.SHA256.compressBlock (chainState msg len k) (specBlock msg len k)

/-- `truncate`'s entry `j` (for `j < len`) is `msg[j]`. -/
private theorem truncate_getElem (msg : Vector ℕ inputBufferLen) (len : ℕ)
    (h : len ≤ inputBufferLen) (j : ℕ) (hj : j < len) :
    (Specs.SHA256.truncate msg len h)[j]'hj = msg[j]'(Nat.lt_of_lt_of_le hj h) := by
  unfold Specs.SHA256.truncate
  rw [Vector.getElem_ofFn]

/-- The raw `pad` byte function agrees with `specPaddedByte` on the padded range. -/
private theorem pad_byte_eq (msg : Vector ℕ inputBufferLen) (len : ℕ)
    (h : len ≤ inputBufferLen) (j : ℕ) (hj : j < numBlocksForLen len * 64) :
    (if hjl : j < len then (Specs.SHA256.truncate msg len h)[j]'hjl
      else if j = len then (0x80 : ℕ)
      else if j < numBlocksForLen len * 64 - 8 then 0
      else len * 8 / 2 ^ (8 * (numBlocksForLen len * 64 - 1 - j)) % 256)
      = specPaddedByte msg len j := by
  unfold specPaddedByte specPaddedByteConst
  by_cases hjl : j < len
  · rw [dif_pos hjl, truncate_getElem msg len h j hjl, dif_pos ⟨hjl, Nat.lt_of_lt_of_le hjl h⟩]
  · rw [dif_neg hjl, dif_neg (fun hc => hjl hc.1)]
    -- now compare the const branches; the spec has extra `else 0` for j ≥ totalLen
    by_cases he : j = len
    · rw [if_pos he, if_pos he]
    · rw [if_neg he, if_neg he]
      by_cases h8 : j < numBlocksForLen len * 64 - 8
      · rw [if_pos h8, if_pos h8]
      · rw [if_neg h8, if_neg h8, if_pos hj]
private theorem pad_getElem_eq_specBlock (msg : Vector ℕ inputBufferLen) (len : ℕ)
    (h : len ≤ inputBufferLen) (b : ℕ) (hb : b < numBlocksForLen len) :
    (Specs.SHA256.pad (Specs.SHA256.truncate msg len h))[b]'(by
      show b < numBlocksForLen len; exact hb) = specBlock msg len b := by
  unfold Specs.SHA256.pad specBlock
  rw [Vector.getElem_map]
  -- equality of the underlying 64-byte vectors implies equality of the blocks
  have hbytes :
      (Vector.toChunks ⟨64, Specs.SHA256.pad._proof_1⟩
          (Vector.mapFinRange ((len + (55 + 64 - len % 64) % 64 + 9) / 64 * 64) fun i =>
            if h_1 : i.val < len then (Specs.SHA256.truncate msg len h)[i.val]'h_1
            else if i.val = len then (0x80 : ℕ)
            else if i.val < (len + (55 + 64 - len % 64) % 64 + 9) / 64 * 64 - 8 then 0
            else len * 8 / 2 ^ (8 * ((len + (55 + 64 - len % 64) % 64 + 9) / 64 * 64 - 1 - i.val)) % 256))[b]'hb
        = Vector.ofFn fun (i : Fin 64) => specPaddedByte msg len (b * 64 + i.val) := by
    apply Vector.ext
    intro i hi
    have hi64 : i < 64 := hi
    have hbound : b * 64 + i < numBlocksForLen len * 64 := by
      have := numBlocksForLen_pos len; nlinarith [hb, hi64]
    rw [getElem_toChunks64 (n := (len + (55 + 64 - len % 64) % 64 + 9) / 64)
          _ b i hb hi64 (by exact hbound)]
    rw [Vector.getElem_mapFinRange]
    -- (raw pad byte at b*64+i) = specPaddedByte msg len (b*64+i) = RHS ofFn entry
    have hpe := pad_byte_eq msg len h (b * 64 + i) hbound
    simp only [numBlocksForLen] at hpe
    have hofn : (Vector.ofFn fun (k : Fin 64) => specPaddedByte msg len (b * 64 + k.val))[i]'hi64
        = specPaddedByte msg len (b * 64 + i) := Vector.getElem_ofFn hi64
    exact hpe.trans hofn.symm
  exact congrArg Specs.SHA256.bytesToBlock hbytes

/-- Folding `compressBlock` over a block vector whose entries match `specBlock`
yields the chain state. -/
private theorem foldl_eq_chainState (msg : Vector ℕ inputBufferLen) (len : ℕ) :
    ∀ {n : ℕ} (v : Vector (Vector ℕ 16) n),
      (∀ b (hb : b < n), v[b]'hb = specBlock msg len b) →
      v.foldl Specs.SHA256.compressBlock Specs.SHA256.H0 = chainState msg len n := by
  intro n v
  induction v using Vector.inductPush with
  | nil =>
    intro _
    rfl
  | @push m as a ih =>
    intro hmatch
    rw [Vector.foldl_push]
    -- the last block equals specBlock at index m
    have hlast : a = specBlock msg len m := by
      have := hmatch m (by omega)
      rw [Vector.getElem_push (by omega)] at this
      rw [dif_neg (by omega)] at this
      exact this
    -- the prefix matches specBlock on its range
    have hpre : ∀ b (hb : b < m), as[b]'hb = specBlock msg len b := by
      intro b hb
      have := hmatch b (by omega)
      rw [Vector.getElem_push (by omega)] at this
      rw [dif_pos hb] at this
      exact this
    rw [ih hpre]
    show Specs.SHA256.compressBlock (chainState msg len m) a
      = chainState msg len (m + 1)
    rw [hlast]
    rfl

/-- The SHA-256 of the truncated message is the chain state after `numBlocksForLen len` blocks. -/
theorem sha256_eq_chainState (msg : Vector ℕ inputBufferLen) (len : ℕ) (h : len ≤ inputBufferLen) :
    Specs.SHA256.sha256 (Specs.SHA256.truncate msg len h) = chainState msg len (numBlocksForLen len) := by
  unfold Specs.SHA256.sha256
  apply foldl_eq_chainState msg len
  intro b hb
  exact pad_getElem_eq_specBlock msg len h b hb

/-- `stateForLen` selects the entry at index `numBlocksForLen len - 1`. -/
theorem stateForLen_eq {α : Type} (states : Vector α paddedBlocksLen) (len : ℕ)
    (h : len ≤ inputBufferLen) :
    stateForLen states len = states[numBlocksForLen len - 1]'(by
      have := numBlocksForLen_pos len; have := numBlocksForLen_le h; omega) := by
  have hpos := numBlocksForLen_pos len
  have hle := numBlocksForLen_le h
  simp only [paddedBlocksLen] at hle
  unfold stateForLen
  -- numBlocksForLen len ∈ {1,2,3,4,5}
  have hcase : numBlocksForLen len = 1 ∨ numBlocksForLen len = 2 ∨
      numBlocksForLen len = 3 ∨ numBlocksForLen len = 4 ∨ numBlocksForLen len = 5 := by omega
  rcases hcase with hc | hc | hc | hc | hc <;> simp only [hc]

omit h_large in
/-- eval commutes with additive Fin.foldl accumulation. -/
lemma eval_finFoldl_add (env : Environment (F p)) (n : ℕ) (g : Fin n → Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) (0 : Expression (F p))) =
      Finset.univ.sum fun i => Expression.eval env (g i) := by
  induction n with
  | zero => simp [Fin.foldl_zero, Expression.eval]
  | succ m ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    simp only [Expression.eval]
    rw [show Fin.foldl m
          (fun (acc : Expression (F p)) (i : Fin m) => acc + g i.castSucc)
          (0 : Expression (F p)) =
        Fin.foldl m
          (fun (acc : Expression (F p)) (i : Fin m) => acc + (fun j => g j.castSucc) i)
          (0 : Expression (F p)) from rfl]
    rw [ih (fun j => g j.castSucc)]

omit h_large in
/-- A one-hot-weighted sum collapses to the selected entry. -/
lemma oneHot_mul_sum {flags : Vector (F p) inputBufferLen} {ℓ : ℕ}
    (h : OneHotAt flags ℓ) (hℓ : ℓ < inputBufferLen) (x : Fin inputBufferLen → F p) :
    (Finset.univ.sum fun i : Fin inputBufferLen => flags[i] * x i) = x ⟨ℓ, hℓ⟩ := by
  have hsum : (Finset.univ.sum fun i : Fin inputBufferLen => flags[i] * x i) =
      Finset.univ.sum fun i : Fin inputBufferLen =>
        (if i.val = ℓ then 1 else 0) * x i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h i]
  rw [hsum]
  rw [Finset.sum_congr rfl (g := fun i : Fin inputBufferLen =>
        if i = (⟨ℓ, hℓ⟩ : Fin inputBufferLen) then x i else 0)
        (fun i _ => by
          by_cases hi : i = (⟨ℓ, hℓ⟩ : Fin inputBufferLen)
          · simp [hi]
          · have : i.val ≠ ℓ := by
              intro hc; exact hi (Fin.ext hc)
            simp [this, hi])]
  rw [Finset.sum_ite_eq' Finset.univ (⟨ℓ, hℓ⟩ : Fin inputBufferLen)
        (fun i : Fin inputBufferLen => x i)]
  simp

omit h_large in
lemma specPaddedByteConst_lt (len j : ℕ) : specPaddedByteConst len j < 256 := by
  unfold specPaddedByteConst
  simp only
  split_ifs
  · norm_num
  · norm_num
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

omit h_large in
lemma specPaddedByte_lt (msg : Vector ℕ inputBufferLen)
    (hbytes : ∀ i : Fin inputBufferLen, msg[i] < 256)
    (len j : ℕ) : specPaddedByte msg len j < 256 := by
  unfold specPaddedByte
  split
  · next h => exact hbytes ⟨j, h.2⟩
  · exact specPaddedByteConst_lt len j

omit h_large in
/-- A byte assembled from boolean bits is < 256. -/
lemma wordByteVal_lt (w : Vector (F p) 32) (b : Fin 4) (h : ∀ t : Fin 32, IsBool w[t]) :
    wordByteVal w b < 256 := by
  unfold wordByteVal
  have hle : ∀ t : Fin 8, (w[8 * (3 - b.val) + t.val]'(by omega)).val ≤ 1 := by
    intro t
    have ht : 8 * (3 - b.val) + t.val < 32 := by omega
    have hb : IsBool (w[8 * (3 - b.val) + t.val]'(by omega)) := h ⟨8 * (3 - b.val) + t.val, ht⟩
    rcases hb with hw | hw <;> rw [hw]
    · simp [ZMod.val_zero]
    · simp [ZMod.val_one]
  have := sum_bool_lt_two_pow 8
    (fun t : Fin 8 => (w[8 * (3 - b.val) + t.val]'(by omega)).val) hle
  simpa using this

omit h_large [Fact p.Prime] in
/-- valueBits of a word equals the big-endian assembly of its four bytes. -/
lemma valueBits_eq_bytesToWord32BE (w : Vector (F p) 32) :
    valueBits w = Specs.SHA256.bytesToWord32BE (wordByteVal w 0) (wordByteVal w 1)
      (wordByteVal w 2) (wordByteVal w 3) := by
  simp only [valueBits, wordByteVal, Specs.SHA256.bytesToWord32BE, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  norm_num
  ring

omit h_large in
/-- The padded-bit witness consists of boolean field elements. -/
lemma paddedBitsValue_isBool (msg : Vector ℕ inputBufferLen) (len : ℕ) (i : Fin paddedBitsLen) :
    IsBool (paddedBitsValue (p := p) msg len)[i] := by
  have hget : (paddedBitsValue (p := p) msg len)[i] =
      ((specPaddedByte msg len
        (i.val / 512 * 64 + i.val % 512 / 32 * 4 + (3 - i.val % 32 / 8))
        / 2 ^ (i.val % 8) % 2 : ℕ) : F p) := by
    unfold paddedBitsValue
    apply Vector.getElem_ofFn
  rw [hget]
  set byteIdx := i.val / 512 * 64 + i.val % 512 / 32 * 4 + (3 - i.val % 32 / 8) with hbi
  have hmod : (specPaddedByte msg len byteIdx / 2 ^ (i.val % 8) % 2 : ℕ) = 0 ∨
      (specPaddedByte msg len byteIdx / 2 ^ (i.val % 8) % 2 : ℕ) = 1 := by omega
  rcases hmod with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

omit h_large in
/-- The length-flag witness is one-hot at `len`. -/
lemma lenFlagsValue_oneHotAt (len : ℕ) : OneHotAt (lenFlagsValue (p := p) len) len := by
  intro k
  unfold lenFlagsValue
  apply Vector.getElem_ofFn

/-- Recomposition of a byte (< 256) from its 8 bits. -/
private lemma bit_recompose (byte : ℕ) (h : byte < 256) :
    (Finset.univ.sum fun t : Fin 8 => (byte / 2 ^ t.val % 2) * 2 ^ t.val) = byte := by
  have key : ∀ m : ℕ, (Finset.univ.sum fun t : Fin m => (byte / 2 ^ t.val % 2) * 2 ^ t.val)
      = byte % 2 ^ m := by
    intro m
    induction m with
    | zero => simp [Nat.mod_one]
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ih, Nat.mod_pow_succ]
      ring
  rw [key 8]
  exact Nat.mod_eq_of_lt (by omega)

omit h_large in
private lemma byteIdx_paddedBitIndex {j t : ℕ} (ht : t < 8) :
    (paddedBitIndex j t) / 512 * 64 + (paddedBitIndex j t) % 512 / 32 * 4 +
      (3 - (paddedBitIndex j t) % 32 / 8) = j := by
  unfold paddedBitIndex
  omega

omit h_large in
private lemma paddedBitIndex_mod_eight {j t : ℕ} (ht : t < 8) :
    (paddedBitIndex j t) % 8 = t := by
  unfold paddedBitIndex
  omega

/-- Value of an entry of `paddedBitsValue` at a `paddedBitIndex`. -/
private lemma paddedBitsValue_at_paddedBitIndex (msg : Vector ℕ inputBufferLen) (len : ℕ)
    {j t : ℕ} (hj : j < paddedBytesLen) (ht : t < 8) :
    ((paddedBitsValue (p := p) msg len)[paddedBitIndex j t]'(paddedBitIndex_lt hj ht)).val =
      specPaddedByte msg len j / 2 ^ t % 2 := by
  have hget : (paddedBitsValue (p := p) msg len)[paddedBitIndex j t]'(paddedBitIndex_lt hj ht) =
      ((specPaddedByte msg len
        ((paddedBitIndex j t) / 512 * 64 + (paddedBitIndex j t) % 512 / 32 * 4 +
          (3 - (paddedBitIndex j t) % 32 / 8))
        / 2 ^ ((paddedBitIndex j t) % 8) % 2 : ℕ) : F p) := by
    unfold paddedBitsValue
    apply Vector.getElem_ofFn
  rw [hget, byteIdx_paddedBitIndex ht, paddedBitIndex_mod_eight ht]
  have hlt : (specPaddedByte msg len j / 2 ^ t % 2 : ℕ) < p := by
    have h2 : (specPaddedByte msg len j / 2 ^ t % 2 : ℕ) < 2 := Nat.mod_lt _ (by norm_num)
    have hp : (2 : ℕ) < p := (Fact.out (p := p > 2))
    omega
  exact ZMod.val_natCast_of_lt hlt

/-- Byte `j` of the padded-bit witness has exactly the spec value. -/
lemma paddedByteVal_paddedBitsValue (msg : Vector ℕ inputBufferLen)
    (hbytes : ∀ i : Fin inputBufferLen, msg[i] < 256) (len : ℕ) (j : Fin paddedBytesLen) :
    paddedByteVal (paddedBitsValue (p := p) msg len) j = specPaddedByte msg len j.val := by
  unfold paddedByteVal
  have hsum : (Finset.univ.sum fun t : Fin 8 =>
        ((paddedBitsValue (p := p) msg len)[paddedBitIndex j.val t.val]'
          (paddedBitIndex_lt j.isLt t.isLt)).val * 2 ^ t.val)
      = Finset.univ.sum fun t : Fin 8 =>
        (specPaddedByte msg len j.val / 2 ^ t.val % 2) * 2 ^ t.val := by
    apply Finset.sum_congr rfl
    intro t _
    rw [paddedBitsValue_at_paddedBitIndex msg len j.isLt t.isLt]
  rw [hsum]
  exact bit_recompose _ (specPaddedByte_lt msg hbytes len j.val)

private lemma getElem_index_eq {α : Type*} {n : ℕ} (v : Vector α n) (i j : ℕ)
    (hi : i < n) (hj : j < n) (h : i = j) : v[i]'hi = v[j]'hj := by
  subst h; rfl

omit h_large in
/-- The bit `8*(3 - j%4) + t` of `paddedWord padded j` is the flat bit at `paddedBitIndex`. -/
private lemma paddedWord_getElem (env : Environment (F p)) (padded : Var SHA256PaddedBits (F p))
    (j : Fin paddedBytesLen) {t : ℕ} (ht : t < 8) :
    (Vector.map (Expression.eval env) (paddedWord padded j))[8 * (3 - j.val % 4) + t]'(by omega) =
      (Vector.map (Expression.eval env) padded)[paddedBitIndex j.val t]'
        (paddedBitIndex_lt j.isLt ht) := by
  rw [Vector.getElem_map, Vector.getElem_map]
  unfold paddedWord
  rw [Vector.getElem_ofFn]
  have hidx : j.val / 64 * 512 + j.val % 64 / 4 * 32 +
      (⟨8 * (3 - j.val % 4) + t, by omega⟩ : Fin 32).val = paddedBitIndex j.val t := by
    show j.val / 64 * 512 + j.val % 64 / 4 * 32 + (8 * (3 - j.val % 4) + t) = paddedBitIndex j.val t
    unfold paddedBitIndex
    omega
  apply congrArg (Expression.eval env)
  exact getElem_index_eq padded _ _ _ _ hidx

omit h_large in
/-- Evaluating the `paddedWord` slice and taking byte `j % 4` gives `paddedByteVal`. -/
lemma wordByteVal_paddedWord (env : Environment (F p)) (padded : Var SHA256PaddedBits (F p))
    (j : Fin paddedBytesLen) :
    wordByteVal (Vector.map (Expression.eval env) (paddedWord padded j)) ⟨j.val % 4, by omega⟩ =
      paddedByteVal (Vector.map (Expression.eval env) padded) j := by
  unfold wordByteVal paddedByteVal
  apply Finset.sum_congr rfl
  intro t _
  have hstep :
      (Vector.map (Expression.eval env) (paddedWord padded j))[
        8 * (3 - (⟨j.val % 4, by omega⟩ : Fin 4).val) + t.val]'(by omega) =
      (Vector.map (Expression.eval env) padded)[paddedBitIndex j.val t.val]'
        (paddedBitIndex_lt j.isLt t.isLt) := by
    rw [getElem_index_eq (Vector.map (Expression.eval env) (paddedWord padded j))
          (8 * (3 - (⟨j.val % 4, by omega⟩ : Fin 4).val) + t.val)
          (8 * (3 - j.val % 4) + t.val) (by omega) (by omega) rfl]
    exact paddedWord_getElem env padded j t.isLt
  rw [hstep]

omit h_large in
/-- Booleanity transfers from the flat padded bits to a `paddedWord` slice. -/
lemma paddedWord_isBool (env : Environment (F p)) (padded : Var SHA256PaddedBits (F p))
    (j : Fin paddedBytesLen)
    (h : ∀ i : Fin paddedBitsLen, IsBool (Vector.map (Expression.eval env) padded)[i]) :
    ∀ t : Fin 32, IsBool (Vector.map (Expression.eval env) (paddedWord padded j))[t] := by
  intro t
  have hidx : j.val / 64 * 512 + j.val % 64 / 4 * 32 + t.val < paddedBitsLen := by
    have hj := j.isLt
    simp only [paddedBytesLen, paddedBlocksLen] at hj
    simp only [paddedBitsLen, paddedBlocksLen]
    omega
  have hget : (Vector.map (Expression.eval env) (paddedWord padded j))[t] =
      (Vector.map (Expression.eval env) padded)[
        j.val / 64 * 512 + j.val % 64 / 4 * 32 + t.val]'hidx := by
    rw [Fin.getElem_fin, Vector.getElem_map]
    unfold paddedWord
    rw [Vector.getElem_ofFn, Vector.getElem_map]
  rw [hget]
  exact h ⟨_, hidx⟩

end Solution.SHA256
end
