import Solution.SHA256.BitwiseOps
import Challenge.Specs.SHA256
import Clean.Utils.Rotation
import Clean.Utils.Bits
import Clean.Utils.Fin

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# Shared theorems for the SHA-256 gadgets

Lemmas reused by more than one gadget (`Xor32`, `And32`, `Ch32`, `Maj32`,
`Add32`, `LowerSigma0/1`, `UpperSigma0/1`, `SelectDigest`, `PaddingTheorems`, ...).

These are about `valueBits` of boolean bit-vectors and the `rotr32` / `shr32`
pure combinators, expressed at the natural-number level.
-/

/-- A boolean-weighted finite sum is bounded by `2^n`. -/
lemma sum_bool_lt_two_pow (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i ≤ 1) :
    ∑ i : Fin n, f i * 2^i.val < 2^n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
    have ihm : ∑ i : Fin m, f (Fin.castSucc i) * 2 ^ i.val < 2 ^ m :=
      ih (f ∘ Fin.castSucc) (fun i => hf _)
    have hfm : f (Fin.last m) ≤ 1 := hf _
    have hfm_bound : f (Fin.last m) * 2 ^ m ≤ 2 ^ m := by nlinarith [Nat.two_pow_pos m]
    have h2 : 2^m + 2^m = 2^(m+1) := by ring
    omega

/-- The `k`-th bit of a boolean-weighted sum is the `k`-th boolean coefficient. -/
lemma testBit_binary_sum (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1) (k : Fin n) :
    Nat.testBit (∑ i : Fin n, f i * 2^i.val) k.val = decide (f k = 1) := by
  induction n with
  | zero => exact k.elim0
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
    set S := ∑ i : Fin m, f (Fin.castSucc i) * 2 ^ i.val
    set fm := f (Fin.last m)
    have hS : S < 2 ^ m := sum_bool_lt_two_pow m (f ∘ Fin.castSucc) (fun i => by
      rcases hf (Fin.castSucc i) with h | h <;> simp [h])
    rw [show S + fm * 2^m = 2^m * fm + S from by ring, Nat.testBit_two_pow_mul_add _ hS]
    by_cases hk : k.val < m
    · simp only [hk, ite_true]
      have ih' := ih (f ∘ Fin.castSucc) (fun i => hf _) ⟨k.val, hk⟩
      simp only [Function.comp] at ih'; rw [ih']; congr 1
    · push_neg at hk
      have hkeq : k.val = m := Nat.le_antisymm (Nat.lt_succ_iff.mp k.isLt) hk
      simp only [hkeq, lt_irrefl, ite_false, Nat.sub_self]
      have hklast : k = Fin.last m := Fin.ext hkeq; subst hklast
      rcases hf (Fin.last m) with h | h <;> simp [h, fm]

omit [Fact (Nat.Prime p)] in
/-- For normalized bit vectors, `valueBits` has exactly the vector's bits. -/
lemma valueBits_testBit (x : fields 32 (F p))
    (hx_bool : ∀ i : Fin 32, (x[i] : F p).val = 0 ∨ (x[i] : F p).val = 1)
    (i : Fin 32) :
    (valueBits x).testBit i.val = decide ((x[i] : F p).val = 1) := by
  rw [show valueBits x = ∑ i : Fin 32, (x[i] : F p).val * 2^i.val from rfl]
  exact testBit_binary_sum 32 _ hx_bool i

/-- The xor of two boolean-weighted sums is the boolean-weighted sum of the xors. -/
lemma bool_finsum_xor_eq (n : ℕ) (f g : Fin n → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = 0 ∨ g i = 1) :
    ∑ i : Fin n, (f i ^^^ g i) * 2^i.val
    = (∑ i : Fin n, f i * 2^i.val) ^^^ (∑ i : Fin n, g i * 2^i.val) := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < n
  · have hfg : ∀ i : Fin n, (f i ^^^ g i) = 0 ∨ (f i ^^^ g i) = 1 := by
      intro i; rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
    rw [testBit_binary_sum n _ hfg ⟨j, hj⟩, Nat.testBit_xor,
        testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩]
    rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;> simp [hfi, hgi]
  · push_neg at hj
    have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hfS := sum_bool_lt_two_pow n f (fun i => by rcases hf i with h|h <;> simp [h])
    have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with h|h <;> simp [h])
    have hfgS := sum_bool_lt_two_pow n (fun i => f i ^^^ g i) (fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi])
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hfgS pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow hfS hgS) pow_le)]

/-- valueBits of a normalized vector is < 2^32 -/
lemma valueBits_lt_two_pow (x : fields 32 (F p)) (hx : Normalized x) :
    valueBits x < 2^32 :=
  sum_bool_lt_two_pow 32 (fun i => (x[i] : F p).val) (fun i => by
    show (x[i] : F p).val ≤ 1
    rcases hx i with h | h
    · rw [h, ZMod.val_zero]; exact Nat.zero_le _
    · rw [h, ZMod.val_one])

/-! ## valueBits identities for rotr32 / shr32 (at the natural-number level) -/

lemma rotRight32_fin_testBit (x : ℕ) (k : Fin 32) (h : x < 2^32) (i : ℕ) :
    (rotRight32 x k.val).testBit i =
      if i < 32 - k.val then
        x.testBit (k.val + i)
      else
        decide (i < 32) && x.testBit (i - (32 - k.val)) := by
  rw [Utils.Rotation.rotRight32_fin]
  have hhigh : x / 2 ^ k.val < 2 ^ (32 - k.val) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [← Nat.pow_add]
    have hk : k.val ≤ 32 := Nat.le_of_lt k.isLt
    rw [Nat.sub_add_cancel hk]
    exact h
  rw [show x % 2 ^ k.val * 2 ^ (32 - k.val) + x / 2 ^ k.val =
      2 ^ (32 - k.val) * (x % 2 ^ k.val) + x / 2 ^ k.val by ring]
  rw [Nat.testBit_two_pow_mul_add _ hhigh]
  by_cases hi : i < 32 - k.val
  · simp only [hi, ↓reduceIte]
    rw [Nat.testBit_div_two_pow]
    congr 1
    omega
  · simp only [hi, ↓reduceIte]
    by_cases hi32 : i < 32
    · simp only [hi32, decide_true]
      rw [Nat.testBit_mod_two_pow]
      have : i - (32 - k.val) < k.val := by omega
      simp [this]
    · simp only [hi32, decide_false]
      rw [Nat.testBit_mod_two_pow]
      have : ¬ i - (32 - k.val) < k.val := by omega
      simp [this]

omit [Fact (Nat.Prime p)] in
lemma valueBits_rotr32_sum (k : Fin 32) (x : fields 32 (F p)) :
    (∑ i : Fin 32, (x[(i + k).val] : F p).val * 2^i.val) =
      valueBits (x.rotate k.val) := by
  simp only [valueBits]
  apply Finset.sum_congr rfl
  intro i _
  simp [Vector.getElem_rotate, Fin.val_add]

lemma valueBits_rotr32_testBit_ge (k : Fin 32) (x : fields 32 (F p))
    (hx : Normalized (x.rotate k.val)) (j : ℕ) (hj : 32 ≤ j) :
    (∑ i : Fin 32, (x[(i + k).val] : F p).val * 2^i.val).testBit j = false := by
  rw [valueBits_rotr32_sum]
  exact Nat.testBit_eq_false_of_lt
    (Nat.lt_of_lt_of_le (valueBits_lt_two_pow _ hx) (Nat.pow_le_pow_right (by norm_num) hj))

/-- Sum form: `∑ x[(i+k).val].val * 2^i = rotRight32 (valueBits x) k.val`. -/
lemma valueBits_rotr32_eq (k : Fin 32) (x : fields 32 (F p)) (hx : Normalized x) :
    ∑ i : Fin 32, (x[(i + k).val] : F p).val * 2^i.val = rotRight32 (valueBits x) k.val := by
  have hx_bool : ∀ i : Fin 32, (x[i] : F p).val = 0 ∨ (x[i] : F p).val = 1 := by
    intro i
    rcases hx i with h | h
    · left; simp [h, ZMod.val_zero]
    · right; simp [h, ZMod.val_one]
  have hrot_bool : ∀ i : Fin 32,
      (x[(i + k).val] : F p).val = 0 ∨ (x[(i + k).val] : F p).val = 1 := by
    intro i
    exact hx_bool (i + k)
  have hx_lt : valueBits x < 2^32 := valueBits_lt_two_pow x hx
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 32
  · rw [testBit_binary_sum 32 _ hrot_bool ⟨j, hj⟩,
        rotRight32_fin_testBit _ k hx_lt j]
    by_cases hlow : j < 32 - k.val
    · simp only [hlow, ↓reduceIte]
      have hjk_lt : k.val + j < 32 := by omega
      let jk : Fin 32 := ⟨k.val + j, hjk_lt⟩
      rw [valueBits_testBit x hx_bool jk]
      simp only [decide_eq_decide]
      have hjk : jk = (⟨j, hj⟩ : Fin 32) + k := by
        apply Fin.ext
        simp only [jk, Fin.val_add]
        have hjk_lt' : j + k.val < 32 := by omega
        rw [Nat.mod_eq_of_lt hjk_lt']
        omega
      rw [hjk]
      rfl
    · simp only [hlow, ↓reduceIte, hj, decide_true]
      let jk : Fin 32 := ⟨j - (32 - k.val), by omega⟩
      rw [valueBits_testBit x hx_bool jk]
      have hsum_ge : 32 ≤ j + k.val := by omega
      have hsum_lt : j + k.val < 64 := by omega
      have hmod : (j + k.val) % 32 = j - (32 - k.val) := by
        rw [show j + k.val = 32 + (j - (32 - k.val)) by omega]
        rw [Nat.add_mod_left]
        rw [Nat.mod_eq_of_lt]
        omega
      have hjk : jk = (⟨j, hj⟩ : Fin 32) + k := by
        apply Fin.ext
        simp only [jk, Fin.val_add]
        exact hmod.symm
      rw [hjk]
      simp
  · push_neg at hj
    have hrot_norm : Normalized (x.rotate k.val) := by
      intro i
      simpa [Vector.getElem_rotate] using hx (i + k)
    have lhs_bit_false :=
      valueBits_rotr32_testBit_ge k x hrot_norm j hj
    rw [lhs_bit_false, rotRight32_fin_testBit _ k hx_lt j]
    have hjlow : ¬j < 32 - k.val := by omega
    simp [hjlow, hj]

/-! ## eval helpers for rotr32 / shr32 -/

lemma eval_rotr32 (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (k : Fin 32) (i : Fin 32) :
    Expression.eval env (rotr32 k input_var)[i.val] = input[(i + k).val] := by
  unfold rotr32
  rw [Vector.getElem_rotate]
  subst h_input
  rw [Vector.getElem_map]
  congr 1

lemma valueBits_shr32_eq (k : Fin 32) (x : fields 32 (F p)) (hx : Normalized x) :
    ∑ i : Fin 32,
      ((if h : i.val + k.val < 32 then (x[i.val + k.val]'h : F p) else 0) : F p).val * 2^i.val
    = valueBits x / 2^k.val := by
  have hbool : ∀ i : Fin 32, (x[i] : F p).val = 0 ∨ (x[i] : F p).val = 1 :=
    fun i => by rcases hx i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have f_bool : ∀ i : Fin 32,
      ((if h : i.val + k.val < 32 then (x[i.val + k.val]'h : F p) else 0) : F p).val = 0 ∨
      ((if h : i.val + k.val < 32 then (x[i.val + k.val]'h : F p) else 0) : F p).val = 1 := by
    intro i; split
    · next h => exact hbool ⟨i.val + k.val, h⟩
    · simp [ZMod.val_zero]
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < 32
  · rw [testBit_binary_sum 32 _ f_bool ⟨j, hj⟩, Nat.testBit_div_two_pow]
    by_cases hjk : j + k.val < 32
    · simp only [hjk, dite_true]
      rw [show valueBits x = ∑ i : Fin 32, (x[i] : F p).val * 2^i.val from rfl,
          testBit_binary_sum 32 _ hbool ⟨j + k.val, hjk⟩]
      simp only [decide_eq_decide]
      constructor <;> intro h <;> convert h using 2
    · simp only [hjk, dite_false, ZMod.val_zero]
      have hval_lt : valueBits x < 2^32 := valueBits_lt_two_pow x hx
      have : valueBits x < 2 ^ (j + k.val) :=
        lt_of_lt_of_le hval_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [Nat.testBit_eq_false_of_lt this]
  · push_neg at hj
    have pow_le : 2^32 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hval_lt : valueBits x < 2^32 := valueBits_lt_two_pow x hx
    have lhs_lt : ∑ i : Fin 32,
        ((if h : i.val + k.val < 32 then (x[i.val + k.val]'h : F p) else 0) : F p).val * 2^i.val
        < 2^32 := by
      apply sum_bool_lt_two_pow
      intro i; rcases f_bool i with h | h <;> simp [h]
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le lhs_lt pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hval_lt) pow_le)]

lemma eval_shr32 (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (k : Fin 32) (i : Fin 32) :
    Expression.eval env (shr32 k input_var)[i.val] =
      if h : i.val + k.val < 32 then input[i.val + k.val]'h else 0 := by
  unfold shr32; rw [Vector.getElem_ofFn]; subst h_input
  split
  · next h => rw [Vector.getElem_map]
  · rfl

lemma shr_isbool (k : ℕ) (input : fields 32 (F p)) (ha : Normalized input) (i : Fin 32) :
    (if h : i.val + k < 32 then input[i.val + k]'h else (0 : F p)) = 0 ∨
    (if h : i.val + k < 32 then input[i.val + k]'h else (0 : F p)) = 1 := by
  split
  · next h => exact ha ⟨i.val + k, h⟩
  · left; rfl

/-! ## `valueBits` / `Normalized` bridges for rotated/shifted vectors

`valueBits_rotate` expresses `valueBits` of a rotated bit-vector through
`rotRight32`; `Normalized_rotate` carries `Normalized` through a rotation. -/

/-- `valueBits` of a rotated bit-vector equals `rotRight32` of the original `valueBits`.
Proved through the `native_decide`-free `valueBits_rotr32_sum`/`valueBits_rotr32_eq`. -/
lemma valueBits_rotate (x : fields 32 (F p)) (hx : Normalized x) (k : Fin 32) :
    valueBits (x.rotate k.val) = rotRight32 (valueBits x) k.val := by
  rw [← valueBits_rotr32_sum k x, valueBits_rotr32_eq k x hx]

/-- A rotated normalized bit-vector is normalized. -/
lemma Normalized_rotate (x : fields 32 (F p)) (hx : Normalized x) (k : ℕ) :
    Normalized (x.rotate k) := by
  intro i
  rw [Fin.getElem_fin, Vector.getElem_rotate]
  exact hx ⟨(i.val + k) % 32, Nat.mod_lt _ (by norm_num)⟩

/-! ## Evaluated-`rotr32`/`shr32` bridges (vector + `valueBits` + `Normalized`)

These let a gadget that composes `Xor32.circuit` over `rotr32`/`shr32` of its
input discharge the subcircuit `Normalized` assumptions and rewrite the
subcircuit `valueBits` spec to `rotRight32` / division on `valueBits input`,
without ever touching witness indices. Shared by `LowerSigma0/1`, `UpperSigma0/1`. -/

/-- Evaluating `rotr32 k input_var` rotates the evaluated input vector. -/
lemma eval_rotr32_vec (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (k : Fin 32) :
    Vector.map (Expression.eval env) (rotr32 k input_var) = input.rotate k.val := by
  ext i hi
  rw [Vector.getElem_map, eval_rotr32 env input_var input h_input k ⟨i, hi⟩, Vector.getElem_rotate]
  congr 1

/-- `valueBits` of an evaluated `rotr32` is `rotRight32` of the input's `valueBits`. -/
lemma valueBits_eval_rotr32 (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (hx : Normalized input) (k : Fin 32) :
    valueBits (Vector.map (Expression.eval env) (rotr32 k input_var)) =
      rotRight32 (valueBits input) k.val := by
  rw [eval_rotr32_vec env input_var input h_input k, valueBits_rotate input hx k]

/-- An evaluated `rotr32` of a normalized input is normalized. -/
lemma Normalized_eval_rotr32 (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (hx : Normalized input) (k : Fin 32) :
    Normalized (Vector.map (Expression.eval env) (rotr32 k input_var)) := by
  rw [eval_rotr32_vec env input_var input h_input k]
  exact Normalized_rotate input hx k.val

/-- `valueBits` of an evaluated `shr32` is the input's `valueBits` shifted right. -/
lemma valueBits_eval_shr32 (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (hx : Normalized input) (k : Fin 32) :
    valueBits (Vector.map (Expression.eval env) (shr32 k input_var)) =
      valueBits input / 2^k.val := by
  rw [← valueBits_shr32_eq k input hx]
  simp only [valueBits]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.getElem_fin, Vector.getElem_map, eval_shr32 env input_var input h_input k i]

/-- An evaluated `shr32` of a normalized input is normalized. -/
lemma Normalized_eval_shr32 (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (hx : Normalized input) (k : Fin 32) :
    Normalized (Vector.map (Expression.eval env) (shr32 k input_var)) := by
  intro i
  rw [Fin.getElem_fin, Vector.getElem_map, eval_shr32 env input_var input h_input k i]
  exact shr_isbool k.val input hx i

end Solution.SHA256
end
