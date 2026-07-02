import Solution.SHA256.PaddingTheorems
import Solution.SHA256.Theorems

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256
namespace SelectDigest

/-!
# Helper lemmas for `SelectDigest`

Gadget-private lemmas for the digest-selection gadget. Shared lemmas live in
`Theorems`.
-/

/-- `stateForLen` commutes with a `Vector.map` over the candidate states. -/
lemma stateForLen_map {α β : Type} (f : α → β)
    (v : Vector α paddedBlocksLen) (len : ℕ) :
    stateForLen (v.map f) len = f (stateForLen v len) := by
  unfold stateForLen
  split <;> simp [Vector.getElem_map]

/-- `stateForLen` always returns one of the candidate states. -/
lemma stateForLen_mem {α : Type} (v : Vector α paddedBlocksLen) (len : ℕ) :
    ∃ k : Fin paddedBlocksLen, stateForLen v len = v[k] := by
  unfold stateForLen
  split
  · exact ⟨⟨0, by norm_num⟩, rfl⟩
  · exact ⟨⟨1, by norm_num⟩, rfl⟩
  · exact ⟨⟨2, by norm_num⟩, rfl⟩
  · exact ⟨⟨3, by norm_num⟩, rfl⟩
  · exact ⟨⟨4, by norm_num⟩, rfl⟩

omit h_large in
/-- A 32-bit value assembled from boolean field elements is `< 2^32`. -/
lemma valueBits_lt (w : Vector (F p) 32) (h : Normalized w) :
    valueBits w < 2^32 := by
  unfold valueBits
  have hle : ∀ i : Fin 32, w[i].val ≤ 1 := by
    intro i
    rcases h i with hw | hw <;> rw [hw]
    · simp [ZMod.val_zero]
    · simp [ZMod.val_one]
  have := sum_bool_lt_two_pow 32 (fun i : Fin 32 => w[i].val) hle
  simpa using this

/-- For a normalized 32-bit word, `fieldFromBitsExpr` evaluates to the field cast of
`valueBits`, and its `.val` is exactly `valueBits`. -/
lemma val_fieldFromBits (w : Vector (F p) 32) (h : Normalized w) :
    (Utils.Bits.fieldFromBits w).val = valueBits w := by
  have hsum : Utils.Bits.fromBits (w.map ZMod.val) = valueBits w := by
    unfold Utils.Bits.fromBits valueBits
    rw [Fin.foldl_to_sum 32 (fun i : Fin 32 => (w.map ZMod.val)[i.val] * 2 ^ i.val)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Vector.getElem_map]
    rfl
  have hcast : Utils.Bits.fieldFromBits w = ((valueBits w : ℕ) : F p) := by
    unfold Utils.Bits.fieldFromBits
    rw [hsum]
  rw [hcast]
  have hlt : valueBits w < p := by
    have h32 : (2:ℕ)^32 < 2^33 := by norm_num
    exact lt_trans (lt_trans (valueBits_lt w h) h32) h_large.out
  exact ZMod.val_natCast_of_lt hlt

end SelectDigest
end Solution.SHA256
end
