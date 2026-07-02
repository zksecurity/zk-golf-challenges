import Solution.SHA256.Common

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256

instance : Fact (p > 2) := .mk (by
  have h : (2 : ℕ) < 2^33 := by norm_num
  exact h.trans h_large.out)

namespace CheckLenFlags

open Challenge.Instances.SHA256.Interface (inputBufferLen)

/-!
# Helper lemmas for `CheckLenFlags`

Gadget-private lemmas for the one-hot length-flag assertion.
-/

omit h_large in
/-- `Expression.eval` distributes over a `Fin.foldl` summation. -/
lemma eval_foldl_sum {n : ℕ} (env : Environment (F p))
    (g : Fin n → Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0) =
      ∑ i : Fin n, Expression.eval env (g i) := by
  induction n with
  | zero => simp only [Fin.foldl_zero, Finset.univ_eq_empty, Finset.sum_empty]; rfl
  | succ m ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    simp only [Expression.eval]
    rw [show (Fin.foldl m (fun (x1 : Expression (F p)) (x2 : Fin m) =>
        x1 + g x2.castSucc) 0) =
        Fin.foldl m (fun acc i => acc + (g ∘ Fin.castSucc) i) 0 from rfl]
    rw [ih (g ∘ Fin.castSucc)]
    rfl

omit h_large in
/-- A boolean field element equals the cast of its `val`, which is `0` or `1`. -/
lemma isBool_val (x : F p) (h : IsBool x) : x.val = 0 ∨ x.val = 1 := by
  rcases h with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]

omit h_large in
/-- If a small nat casts to `1` in `F p`, it is `1`. -/
lemma natCast_eq_one_of_lt {m : ℕ} (hm : m < p) (h : ((m : ℕ) : F p) = 1) : m = 1 := by
  have hval := ZMod.val_natCast_of_lt hm
  rw [h, ZMod.val_one] at hval
  exact hval.symm

/-- If a nat sum of `0/1` indicators over `Fin n` equals `1`, then there is a
unique index where the indicator is `1`. -/
lemma exists_unique_of_sum_eq_one {n : ℕ} (v : Fin n → ℕ)
    (hb : ∀ i, v i = 0 ∨ v i = 1) (hsum : ∑ i : Fin n, v i = 1) :
    ∃ ℓ : Fin n, v ℓ = 1 ∧ ∀ k : Fin n, k ≠ ℓ → v k = 0 := by
  have hne : ∃ ℓ : Fin n, v ℓ = 1 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ i : Fin n, v i = 0 := by
      intro i; rcases hb i with h | h
      · exact h
      · exact absurd h (hcon i)
    rw [Finset.sum_congr rfl (fun i _ => hall i)] at hsum
    simp at hsum
  obtain ⟨ℓ, hℓ⟩ := hne
  refine ⟨ℓ, hℓ, ?_⟩
  intro k hk
  rcases hb k with h | h
  · exact h
  · exfalso
    have hle : v ℓ + v k ≤ ∑ i : Fin n, v i := by
      have : ({ℓ, k} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
      calc v ℓ + v k = ∑ i ∈ ({ℓ, k} : Finset (Fin n)), v i := by
              rw [Finset.sum_pair hk.symm]
        _ ≤ ∑ i : Fin n, v i := Finset.sum_le_sum_of_subset this
    rw [hsum, hℓ, h] at hle
    omega

omit [Fact p.Prime] in
/-- `inputBufferLen < p`. -/
lemma inputBufferLen_lt : inputBufferLen < p := by
  have h256 : (inputBufferLen : ℕ) = 256 := rfl
  have h2 : (256 : ℕ) < 2 ^ 33 := by norm_num
  have hp := h_large.out
  omega

/-- A nat sum of `0/1` indicators over `Fin inputBufferLen` whose `F p`-cast is
`1` is itself `1` (the sum is small because there are only `inputBufferLen` terms
and `p` is large). -/
lemma natSum_eq_one_of_cast (g : Fin inputBufferLen → ℕ)
    (hb : ∀ i, g i = 0 ∨ g i = 1) (h : ((∑ i : Fin inputBufferLen, g i : ℕ) : F p) = 1) :
    (∑ i : Fin inputBufferLen, g i) = 1 := by
  have h_small : (∑ i : Fin inputBufferLen, g i) < p := by
    have hle : (∑ i : Fin inputBufferLen, g i) ≤ ∑ _i : Fin inputBufferLen, 1 := by
      apply Finset.sum_le_sum
      intro i _; rcases hb i with hi | hi <;> omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hle
    have := inputBufferLen_lt (p := p)
    omega
  exact natCast_eq_one_of_lt h_small h

/-- The soundness math, isolated from the circuit context: boolean flags summing
to one, whose index-weighted sum is `msg`, form the one-hot indicator of
`msg.val < inputBufferLen`. -/
lemma onehot_from_constraints
    (flags : Vector (F p) inputBufferLen) (msg : F p)
    (h_bool : ∀ i : Fin inputBufferLen, IsBool flags[i.val])
    (h_sum : (∑ i : Fin inputBufferLen, flags[i.val]) = 1)
    (h_wt : msg = ∑ i : Fin inputBufferLen, flags[i.val] * ((i.val : ℕ) : F p)) :
    msg.val < inputBufferLen ∧ OneHotAt flags msg.val := by
  -- pass to nat values
  have hv_bool : ∀ i : Fin inputBufferLen,
      (flags[i.val]).val = 0 ∨ (flags[i.val]).val = 1 := fun i => isBool_val _ (h_bool i)
  -- the field sum is the cast of the nat sum
  have h_cast_sum : ((∑ i : Fin inputBufferLen, (flags[i.val]).val : ℕ) : F p) = 1 := by
    rw [Nat.cast_sum, ← h_sum]
    apply Finset.sum_congr rfl
    intro i _
    rcases h_bool i with h | h <;>
      simp only [h, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one]
  -- so the nat sum is 1
  have h_nat_sum : (∑ i : Fin inputBufferLen, (flags[i.val]).val) = 1 :=
    natSum_eq_one_of_cast (fun i => (flags[i.val]).val) hv_bool h_cast_sum
  -- get the unique one-hot index
  obtain ⟨ℓ, hℓ_one, hℓ_zero⟩ :=
    exists_unique_of_sum_eq_one (fun i => (flags[i.val]).val) hv_bool h_nat_sum
  -- flags is the indicator of ℓ
  have h_indicator : ∀ k : Fin inputBufferLen,
      flags[k] = if k.val = ℓ.val then (1 : F p) else 0 := by
    intro k
    rcases eq_or_ne k.val ℓ.val with hk | hk
    · have hkeq : k = ℓ := Fin.ext hk
      subst hkeq
      rw [if_pos hk]
      rcases h_bool k with h | h
      · rw [h, ZMod.val_zero] at hℓ_one; exact absurd hℓ_one (by norm_num)
      · exact h
    · have hkne : k ≠ ℓ := fun heq => hk (by rw [heq])
      have hk0 : (flags[k.val]).val = 0 := hℓ_zero k hkne
      rcases h_bool k with h | h
      · rw [if_neg hk]; exact h
      · rw [h, ZMod.val_one] at hk0; exact absurd hk0 (by norm_num)
  -- messageLen = (ℓ : F p)
  have h_term : ∀ i : Fin inputBufferLen,
      flags[i.val] * ((i.val : ℕ) : F p)
        = (if i.val = ℓ.val then (1 : F p) else 0) * ((i.val : ℕ) : F p) := by
    intro i
    have := h_indicator i
    rw [show flags[i.val] = flags[i] from rfl, this]
  have h_msg : msg = ((ℓ.val : ℕ) : F p) := by
    rw [h_wt, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h_term i)]
    rw [Finset.sum_eq_single ℓ]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ ℓ) h
  -- conclude the spec
  have hℓ_lt : ℓ.val < inputBufferLen := ℓ.isLt
  have hℓ_lt_p : ℓ.val < p := lt_trans hℓ_lt (inputBufferLen_lt (p := p))
  have h_msg_val : msg.val = ℓ.val := by
    rw [h_msg, ZMod.val_natCast_of_lt hℓ_lt_p]
  refine ⟨?_, ?_⟩
  · rw [h_msg_val]; exact hℓ_lt
  · intro k
    rw [h_msg_val]
    exact h_indicator k

end CheckLenFlags
end Solution.SHA256
end
