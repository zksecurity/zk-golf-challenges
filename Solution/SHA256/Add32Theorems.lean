import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256

/-!
# Helper lemmas for `Add32`

Gadget-private lemmas (and the `evalBitsNat` helper used by the `add32`
circuit) for the 32-bit modular addition gadget. Shared lemmas live in
`Theorems`.
-/

def evalBitsNat (env : ProverEnvironment (F p)) (a : Var (fields 32) (F p)) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) => (env a[i]).val * 2^i.val

namespace Add32

omit [Fact (Nat.Prime p)] h_large in
/-- The natural-number sum from fromBits equals valueBits -/
lemma fromBits_map_val_eq_valueBits (bits : Vector (F p) 32) :
    Utils.Bits.fromBits (bits.map ZMod.val) = valueBits bits := by
  simp only [Utils.Bits.fromBits, valueBits, Fin.foldl_to_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Vector.getElem_map]
  rfl

omit h_large in
/-- fieldFromBits bits = (valueBits bits : F p) -/
lemma fieldFromBits_eq_valueBits (bits : Vector (F p) 32) :
    Utils.Bits.fieldFromBits bits = (valueBits bits : F p) := by
  unfold Utils.Bits.fieldFromBits
  rw [fromBits_map_val_eq_valueBits]

omit h_large in
/-- fromBitsExpr evaluated at concrete inputs = (valueBits bits : F p) -/
lemma fromBitsExpr_eval_normalized (env : Environment (F p))
    (bits_var : Var (fields 32) (F p)) (bits : Vector (F p) 32)
    (h_eval : Vector.map (Expression.eval env) bits_var = bits) :
    Expression.eval env (fromBitsExpr bits_var) = (valueBits bits : F p) := by
  show Expression.eval env (Utils.Bits.fieldFromBitsExpr bits_var) = _
  simp only [Utils.Bits.fieldFromBits_eval]
  rw [h_eval, fieldFromBits_eq_valueBits]

omit h_large in
/-- For normalized bits with p > 2^32, (fromBitsExpr bits_var).val = valueBits bits -/
lemma fromBitsExpr_val_eq (env : Environment (F p))
    (bits_var : Var (fields 32) (F p)) (bits : Vector (F p) 32)
    (h_eval : Vector.map (Expression.eval env) bits_var = bits)
    (h_norm : Normalized bits) (hp : 2^32 < p) :
    (Expression.eval env (fromBitsExpr bits_var)).val = valueBits bits := by
  rw [fromBitsExpr_eval_normalized env bits_var bits h_eval]
  exact ZMod.val_natCast_of_lt (by linarith [valueBits_lt_two_pow bits h_norm])

omit h_large in
/-- The z output variable vector evaluates to env.get at the witness offsets -/
lemma z_var_eval (env : Environment (F p)) (i₀ : ℕ) :
    Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))
    = Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := by
  ext i; simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]

omit h_large in
/-- IsBool from boolean constraint x * (x + -1) = 0 -/
lemma isbool_of_bool_constraint {x : F p} (h : x * (x + -1) = 0) : IsBool x := by
  rwa [show x + -1 = x - 1 by ring, ← IsBool.iff_mul_sub_one] at h

omit h_large in
/-- Normalized z from boolean constraints -/
lemma normalized_of_bool_holds (env : Environment (F p)) (i₀ : ℕ)
    (h : ∀ i : Fin 32, env.get (i₀ + i.val) * (env.get (i₀ + i.val) + -1) = 0) :
    Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) := by
  intro i
  have hi := h i
  have h_get : (Vector.ofFn fun j : Fin 32 => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) := by
    simp [Vector.getElem_ofFn]
  rw [h_get]
  exact isbool_of_bool_constraint hi

omit h_large in
/-- evalBitsNat env a = valueBits a when the variables evaluate to a -/
lemma evalBitsNat_eq_valueBits (env : ProverEnvironment (F p))
    (a_var : Var (fields 32) (F p)) (a : fields 32 (F p))
    (h : Vector.map (Expression.eval env.toEnvironment) a_var = a) :
    evalBitsNat env a_var = valueBits a := by
  subst h
  unfold evalBitsNat valueBits
  apply Finset.sum_congr rfl
  intro i _
  simp [Vector.getElem_map]

/-- testBit equals div/mod expression -/
lemma testBit_ite_eq (n i : ℕ) : (if n.testBit i = true then 1 else 0 : ℕ) = n / 2^i % 2 := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (n / 2^i) with h | h <;> rw [h] <;> rfl

/-- Bit decomposition: ∑ i, (n / 2^i % 2) * 2^i = n for n < 2^32 -/
lemma bit_decomp_sum (n : ℕ) (h_n_lt : n < 2^32) :
    ∑ i : Fin 32, n / 2^i.val % 2 * 2^i.val = n := by
  conv_rhs => rw [← Utils.Bits.fromBits_toBits h_n_lt]
  unfold Utils.Bits.fromBits Utils.Bits.toBits
  rw [Fin.foldl_to_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_mapRange, testBit_ite_eq]

omit h_large in
/-- For n < 2^32 and 2^32 < p, fieldFromBits of the bit decomposition vector equals (n : F p) -/
lemma fieldFromBits_bit_decomp (n : ℕ) (h_n_lt : n < 2^32) (hp32 : (2:ℕ)^32 < p) :
    Utils.Bits.fieldFromBits (Vector.ofFn fun i : Fin 32 => ((n / 2^i.val % 2 : ℕ) : F p)) =
    ((n : ℕ) : F p) := by
  simp only [Utils.Bits.fieldFromBits, Utils.Bits.fromBits, Fin.foldl_to_sum]
  have h_val_eq : ∀ i : Fin 32, ((Vector.ofFn fun j : Fin 32 =>
      ((n / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] = n / 2^i.val % 2 := by
    intro i
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hbit_lt : n / 2^i.val % 2 < p := by
      have : n / 2^i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      linarith
    exact ZMod.val_natCast_of_lt hbit_lt
  have h_sum_eq : ∑ i : Fin 32, ((Vector.ofFn fun j : Fin 32 =>
      ((n / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] * 2^i.val = n := by
    calc ∑ i : Fin 32, ((Vector.ofFn fun j : Fin 32 =>
            ((n / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] * 2^i.val
        = ∑ i : Fin 32, n / 2^i.val % 2 * 2^i.val := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h_val_eq i]
      _ = n := bit_decomp_sum n h_n_lt
  rw [h_sum_eq]

end Add32
end Solution.SHA256
end
