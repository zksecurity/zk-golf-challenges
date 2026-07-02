import Solution.SHA256.PaddingTheorems

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256

instance : Fact (p > 2) := .mk (by
  have h : (2 : ℕ) < 2^33 := by norm_num
  exact h.trans h_large.out)

namespace CheckPaddedByte

open Challenge.Instances.SHA256.Interface (inputBufferLen)

/-!
# Helper lemmas for `CheckPaddedByte`

Gadget-private lemmas for the padding-byte assertion family.
-/

omit [Fact p.Prime] in
lemma inputBufferLen_lt : inputBufferLen < p := by
  have h256 : (inputBufferLen : ℕ) = 256 := rfl
  have h2 : (256 : ℕ) < 2 ^ 33 := by norm_num
  have hp := h_large.out
  omega

omit h_large in
/-- LHS of the constraint, evaluated, equals the cast of `wordByteVal`. -/
lemma eval_byteFromWord (env : Environment (F p))
    (word_var : Var (fields 32) (F p)) (b : Fin 4) :
    Expression.eval env (byteFromWord word_var b) =
      ((wordByteVal (Vector.map (Expression.eval env) word_var) b : ℕ) : F p) := by
  unfold byteFromWord wordByteVal
  rw [eval_finFoldl_add]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Vector.getElem_map]
  congr 1
  rw [ZMod.natCast_val, ZMod.cast_id]

omit h_large in
/-- RHS of the constraint, evaluated, collapses (via one-hot) to a single term.

The factored `expectedPaddedByte` evaluates as `constPart + msgTerm · coefSum`.
The one-hot `lenFlags` collapses `constPart` to `if j<ℓ then 0 else const` and
`coefSum` to `if j<ℓ then 1 else 0`, recovering exactly the single selected
term. -/
lemma eval_expectedPaddedByte (env : Environment (F p))
    (message_var lenFlags_var : Var (fields inputBufferLen) (F p))
    (j : Fin paddedBytesLen) (ℓ : ℕ) (hℓ : ℓ < inputBufferLen)
    (h_onehot : OneHotAt (Vector.map (Expression.eval env) lenFlags_var) ℓ) :
    Expression.eval env (expectedPaddedByte message_var lenFlags_var j) =
      (if h : j.val < ℓ then
        (Vector.map (Expression.eval env) message_var)[j.val]'(Nat.lt_trans h hℓ)
      else ((specPaddedByteConst ℓ j.val : ℕ) : F p)) := by
  unfold expectedPaddedByte
  -- The constant part collapses via one-hot to `if j<ℓ then 0 else const`.
  have hconst : Expression.eval env
      (Fin.foldl inputBufferLen
        (fun acc len => acc + lenFlags_var[len] *
          (if j.val < len.val then 0 else ((specPaddedByteConst len.val j.val : ℕ) : F p)))
        0)
      = (if j.val < ℓ then (0 : F p) else ((specPaddedByteConst ℓ j.val : ℕ) : F p)) := by
    rw [eval_finFoldl_add,
      Finset.sum_congr rfl (g := fun len : Fin inputBufferLen =>
        (Vector.map (Expression.eval env) lenFlags_var)[len] *
          (if j.val < len.val then (0 : F p)
            else ((specPaddedByteConst len.val j.val : ℕ) : F p)))
        (fun len _ => by simp [Expression.eval]),
      oneHot_mul_sum h_onehot hℓ (fun len : Fin inputBufferLen =>
        if j.val < len.val then (0 : F p)
          else ((specPaddedByteConst len.val j.val : ℕ) : F p))]
  -- The coefficient mass collapses to `if j<ℓ then 1 else 0`.
  have hcoef : Expression.eval env
      (Fin.foldl inputBufferLen
        (fun acc len => acc + (if j.val < len.val then lenFlags_var[len] else 0)) 0)
      = (if j.val < ℓ then (1 : F p) else 0) := by
    rw [eval_finFoldl_add,
      Finset.sum_congr rfl (g := fun len : Fin inputBufferLen =>
        (Vector.map (Expression.eval env) lenFlags_var)[len] *
          (if j.val < len.val then (1 : F p) else 0))
        (fun len _ => by
          by_cases hc : j.val < len.val <;>
            simp [hc, Expression.eval, Vector.getElem_map]),
      oneHot_mul_sum h_onehot hℓ (fun len : Fin inputBufferLen =>
        if j.val < len.val then (1 : F p) else 0)]
  simp only [Expression.eval]
  rw [hconst, hcoef]
  by_cases h : j.val < ℓ
  · have hji : j.val < inputBufferLen := Nat.lt_trans h hℓ
    rw [dif_pos h, dif_pos hji]
    simp only [if_pos h, Vector.getElem_map]
    ring
  · rw [dif_neg h]
    simp [h]

/-- Both sides are casts of naturals `< 256`; conclude the nat equation from the field equation. -/
lemma natCast_inj_lt_256 {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (h : ((a : ℕ) : F p) = ((b : ℕ) : F p)) : a = b := by
  have hp : (256 : ℕ) < p := by
    have h2 : (256 : ℕ) < 2 ^ 33 := by norm_num
    have := h_large.out
    omega
  have hva : ((a : ℕ) : F p).val = a := ZMod.val_natCast_of_lt (by omega)
  have hvb : ((b : ℕ) : F p).val = b := ZMod.val_natCast_of_lt (by omega)
  rw [← hva, ← hvb, h]

/-- The collapsed RHS term equals the spec value (as a natural). -/
lemma rhs_term_eq_specPaddedByte
    (msg : Vector ℕ inputBufferLen) (ℓ : ℕ) (hℓ : ℓ < inputBufferLen) (j : Fin paddedBytesLen) :
    (if h : j.val < ℓ then msg[j.val]'(Nat.lt_trans h hℓ)
      else specPaddedByteConst ℓ j.val) =
    specPaddedByte msg ℓ j.val := by
  unfold specPaddedByte
  by_cases h : j.val < ℓ
  · have hj2 : j.val < inputBufferLen := Nat.lt_trans h hℓ
    rw [dif_pos h, dif_pos ⟨h, hj2⟩]
  · rw [dif_neg h, dif_neg (by intro hc; exact h hc.1)]

end CheckPaddedByte
end Solution.SHA256
end
