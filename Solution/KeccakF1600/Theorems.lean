import Solution.KeccakF1600.BitwiseOps

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

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
lemma valueBits_testBit (x : fields 64 (F p))
    (hx_bool : ∀ i : Fin 64, (x[i] : F p).val = 0 ∨ (x[i] : F p).val = 1)
    (i : Fin 64) :
    (valueBits x).testBit i.val = decide ((x[i] : F p).val = 1) := by
  rw [show valueBits x = ∑ i : Fin 64, (x[i] : F p).val * 2^i.val from rfl]
  exact testBit_binary_sum 64 _ hx_bool i

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

/-- The and of two boolean-weighted sums is the boolean-weighted sum of the ands. -/
lemma bool_finsum_and (n : ℕ) (f g : Fin n → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = 0 ∨ g i = 1) :
    (∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, g i * 2^i.val)
    = ∑ i : Fin n, (f i &&& g i) * 2^i.val := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < n
  · have hfg : ∀ i : Fin n, (f i &&& g i) = 0 ∨ (f i &&& g i) = 1 := by
      intro i; rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
    rw [Nat.testBit_and, testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩,
        testBit_binary_sum n _ hfg ⟨j, hj⟩]
    rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;> simp [hfi, hgi]
  · push_neg at hj
    have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with h|h <;> simp [h])
    have hfgS := sum_bool_lt_two_pow n (fun i => f i &&& g i) (fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi])
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ hgS) pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hfgS pow_le)]

/-- valueBits of a normalized vector is < 2^64. -/
lemma valueBits_lt_two_pow (x : fields 64 (F p)) (hx : Normalized x) :
    valueBits x < 2^64 :=
  sum_bool_lt_two_pow 64 (fun i => (x[i] : F p).val) (fun i => by
    show (x[i] : F p).val ≤ 1
    rcases hx i with h | h
    · rw [h, ZMod.val_zero]; exact Nat.zero_le _
    · rw [h, ZMod.val_one])

/-- Bits of a normalized vector, as naturals, are boolean. -/
lemma Normalized.val_bool {x : fields 64 (F p)} (hx : Normalized x) (i : Fin 64) :
    (x[i] : F p).val = 0 ∨ (x[i] : F p).val = 1 := by
  rcases hx i with h | h
  · left; simp [h, ZMod.val_zero]
  · right; simp [h, ZMod.val_one]

/-- Bits of `Specs.Keccak.rotLeft 64 x k`: bit `j` comes from bit
`(j + (64 − k mod 64)) mod 64` of `x`. -/
lemma rotLeft_testBit (x : ℕ) (k : ℕ) (h : x < 2^64) (j : ℕ) :
    (Specs.Keccak.rotLeft 64 x k).testBit j =
      (decide (j < 64) && x.testBit ((j + (64 - k % 64)) % 64)) := by
  have hunfold : Specs.Keccak.rotLeft 64 x k
      = (x * 2 ^ (k % 64) + x / 2 ^ (64 - k % 64)) % 2 ^ 64 := rfl
  rw [hunfold]
  set r := k % 64 with hr
  have hr64 : r < 64 := Nat.mod_lt _ (by norm_num)
  have hdiv : x / 2 ^ (64 - r) < 2 ^ r := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rw [show r + (64 - r) = 64 from by omega]
    exact h
  by_cases hj : j < 64
  · rw [show x * 2 ^ r + x / 2 ^ (64 - r) = 2 ^ r * x + x / 2 ^ (64 - r) from by ring]
    rw [Nat.testBit_mod_two_pow]
    simp only [hj, decide_true, Bool.true_and]
    rw [Nat.testBit_two_pow_mul_add _ hdiv]
    by_cases hjr : j < r
    · simp only [hjr, ite_true]
      rw [Nat.testBit_div_two_pow]
      congr 1
      omega
    · simp only [hjr, ite_false]
      congr 1
      omega
  · simp only [hj, decide_false, Bool.false_and]
    exact Nat.testBit_eq_false_of_lt
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 64))
        (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- `valueBits` of a left-rotated lane is `Specs.Keccak.rotLeft` of its value. -/
lemma valueBits_rotl (k : ℕ) (x : fields 64 (F p)) (hx : Normalized x) :
    valueBits (rotl k x) = Specs.Keccak.rotLeft 64 (valueBits x) k := by
  have hx_bool := hx.val_bool
  have hrot_bool : ∀ i : Fin 64,
      ((rotl k x)[i] : F p).val = 0 ∨ ((rotl k x)[i] : F p).val = 1 := by
    intro i
    simp only [rotl, Fin.getElem_fin, Vector.getElem_rotate]
    exact hx_bool ⟨(i.val + (64 - k % 64)) % 64, Nat.mod_lt _ (by norm_num)⟩
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · rw [show valueBits (rotl k x) = ∑ i : Fin 64, ((rotl k x)[i] : F p).val * 2^i.val from rfl,
        testBit_binary_sum 64 _ hrot_bool ⟨j, hj⟩,
        rotLeft_testBit _ k (valueBits_lt_two_pow x hx) j]
    simp only [hj, decide_true, Bool.true_and]
    rw [valueBits_testBit x hx_bool ⟨(j + (64 - k % 64)) % 64, Nat.mod_lt _ (by norm_num)⟩]
    simp only [rotl, Fin.getElem_fin, Vector.getElem_rotate]
  · rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
    · exact Nat.lt_of_lt_of_le
        (by unfold Specs.Keccak.rotLeft
            exact Nat.mod_lt _ (Nat.two_pow_pos 64))
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    · exact Nat.lt_of_lt_of_le
        (sum_bool_lt_two_pow 64 _ (fun i => by
          rcases hrot_bool i with h | h <;> rw [Fin.getElem_fin] at h <;> simp [h]))
        (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- A left-rotated normalized lane is normalized. -/
lemma Normalized_rotl (k : ℕ) (x : fields 64 (F p)) (hx : Normalized x) :
    Normalized (rotl k x) := by
  intro i
  simp only [rotl, Fin.getElem_fin, Vector.getElem_rotate]
  exact hx ⟨(i.val + (64 - k % 64)) % 64, Nat.mod_lt _ (by norm_num)⟩

/-- `valueBits` of `xorConst c x` is `c ^^^ valueBits x`, for a 64-bit `c`. -/
lemma valueBits_xorConst (c : ℕ) (hc : c < 2^64) (x : fields 64 (F p)) (hx : Normalized x) :
    valueBits (xorConst c x) = c ^^^ valueBits x := by
  have hx_bool := hx.val_bool
  have hf_bool : ∀ i : Fin 64,
      ((xorConst c x)[i] : F p).val = 0 ∨ ((xorConst c x)[i] : F p).val = 1 := by
    intro i
    simp only [xorConst, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · rcases hx i with h | h <;> rw [Fin.getElem_fin] at h <;>
        simp [h, ZMod.val_one, ZMod.val_zero]
    · exact hx_bool i
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · rw [show valueBits (xorConst c x) =
        ∑ i : Fin 64, ((xorConst c x)[i] : F p).val * 2^i.val from rfl,
        testBit_binary_sum 64 _ hf_bool ⟨j, hj⟩, Nat.testBit_xor,
        valueBits_testBit x hx_bool ⟨j, hj⟩]
    simp only [xorConst, Fin.getElem_fin, Vector.getElem_ofFn]
    by_cases hcj : c.testBit j
    · simp only [hcj, ite_true, Bool.true_xor]
      rcases hx ⟨j, hj⟩ with h | h <;> rw [Fin.getElem_fin] at h <;>
        simp [h, ZMod.val_one, ZMod.val_zero]
    · simp [hcj]
  · have hval : valueBits x < 2^64 := valueBits_lt_two_pow x hx
    rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
    · exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow hc hval)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    · exact Nat.lt_of_lt_of_le
        (sum_bool_lt_two_pow 64 _ (fun i => by
          rcases hf_bool i with h | h <;> rw [Fin.getElem_fin] at h <;> simp [h]))
        (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `xorConst c x` of a normalized lane is normalized. -/
lemma Normalized_xorConst (c : ℕ) (x : fields 64 (F p)) (hx : Normalized x) :
    Normalized (xorConst c x) := by
  intro i
  simp only [xorConst, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · rcases hx i with h | h <;> rw [Fin.getElem_fin] at h
    · right; rw [h]; ring
    · left; rw [h]; ring
  · exact hx i

/-- `notBits` is `xorConst` with the all-ones constant. -/
lemma notBits_eq_xorConst (x : fields 64 (F p)) :
    notBits x = xorConst (2^64 - 1) x := by
  ext i hi
  have hbit : (2^64 - 1 : ℕ).testBit i = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  simp only [notBits, xorConst, Vector.getElem_map, Vector.getElem_ofFn, hbit, if_true,
    Fin.getElem_fin]

/-- `valueBits` of `notBits x` is `Specs.Keccak.notLane 64` of its value. -/
lemma valueBits_notBits (x : fields 64 (F p)) (hx : Normalized x) :
    valueBits (notBits x) = Specs.Keccak.notLane 64 (valueBits x) := by
  rw [notBits_eq_xorConst, valueBits_xorConst _ (by norm_num) x hx]
  unfold Specs.Keccak.notLane
  exact Nat.xor_comm _ _

/-- `notBits` of a normalized lane is normalized. -/
lemma Normalized_notBits (x : fields 64 (F p)) (hx : Normalized x) :
    Normalized (notBits x) := by
  rw [notBits_eq_xorConst]
  exact Normalized_xorConst _ x hx

/-- Evaluating `rotl k` of an expression lane rotates the evaluated lane. -/
lemma eval_rotl_vec (env : Environment (F p)) (v : Var (fields 64) (F p)) (k : ℕ) :
    Vector.map (Expression.eval env) (rotl k v) = rotl k (Vector.map (Expression.eval env) v) := by
  ext i hi
  simp only [rotl, Vector.getElem_map, Vector.getElem_rotate]

/-- Evaluating `notBits` of an expression lane complements the evaluated lane. -/
lemma eval_notBits_vec (env : Environment (F p)) (v : Var (fields 64) (F p)) :
    Vector.map (Expression.eval env) (notBits v) = notBits (Vector.map (Expression.eval env) v) := by
  ext i hi
  simp only [notBits, Vector.getElem_map]
  simp only [circuit_norm]
  ring

/-- Evaluating `xorConst c` of an expression lane applies `xorConst c` to the
evaluated lane. -/
lemma eval_xorConst_vec (env : Environment (F p)) (v : Var (fields 64) (F p)) (c : ℕ) :
    Vector.map (Expression.eval env) (xorConst c v) =
      xorConst c (Vector.map (Expression.eval env) v) := by
  ext i hi
  simp only [xorConst, Vector.getElem_map, Vector.getElem_ofFn]
  split
  · simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map]
    ring
  · simp only [Fin.getElem_fin, Vector.getElem_map]

lemma valueBits_eval_rotl (env : Environment (F p)) (v : Var (fields 64) (F p))
    (x : fields 64 (F p)) (h : Vector.map (Expression.eval env) v = x)
    (hx : Normalized x) (k : ℕ) :
    valueBits (Vector.map (Expression.eval env) (rotl k v)) =
      Specs.Keccak.rotLeft 64 (valueBits x) k := by
  rw [eval_rotl_vec, h, valueBits_rotl k x hx]

lemma Normalized_eval_rotl (env : Environment (F p)) (v : Var (fields 64) (F p))
    (x : fields 64 (F p)) (h : Vector.map (Expression.eval env) v = x)
    (hx : Normalized x) (k : ℕ) :
    Normalized (Vector.map (Expression.eval env) (rotl k v)) := by
  rw [eval_rotl_vec, h]
  exact Normalized_rotl k x hx

lemma valueBits_eval_notBits (env : Environment (F p)) (v : Var (fields 64) (F p))
    (x : fields 64 (F p)) (h : Vector.map (Expression.eval env) v = x)
    (hx : Normalized x) :
    valueBits (Vector.map (Expression.eval env) (notBits v)) =
      Specs.Keccak.notLane 64 (valueBits x) := by
  rw [eval_notBits_vec, h, valueBits_notBits x hx]

lemma Normalized_eval_notBits (env : Environment (F p)) (v : Var (fields 64) (F p))
    (x : fields 64 (F p)) (h : Vector.map (Expression.eval env) v = x)
    (hx : Normalized x) :
    Normalized (Vector.map (Expression.eval env) (notBits v)) := by
  rw [eval_notBits_vec, h]
  exact Normalized_notBits x hx

lemma valueBits_eval_xorConst (env : Environment (F p)) (v : Var (fields 64) (F p))
    (x : fields 64 (F p)) (h : Vector.map (Expression.eval env) v = x)
    (hx : Normalized x) (c : ℕ) (hc : c < 2^64) :
    valueBits (Vector.map (Expression.eval env) (xorConst c v)) = c ^^^ valueBits x := by
  rw [eval_xorConst_vec, h, valueBits_xorConst c hc x hx]

lemma Normalized_eval_xorConst (env : Environment (F p)) (v : Var (fields 64) (F p))
    (x : fields 64 (F p)) (h : Vector.map (Expression.eval env) v = x)
    (hx : Normalized x) (c : ℕ) :
    Normalized (Vector.map (Expression.eval env) (xorConst c v)) := by
  rw [eval_xorConst_vec, h]
  exact Normalized_xorConst c x hx

/-- Specs of the form `Normalized ∧ value = rhs`, assembled lane by lane. -/
lemma stateNormalized_value_ext (s : KeccakBitState (F p)) (rhs : Vector ℕ 25)
    (h : ∀ i : Fin 25, Normalized s[i.val] ∧ valueBits s[i.val] = rhs[i.val]) :
    StateNormalized s ∧ stateValue s = rhs := by
  constructor
  · intro i
    exact (h i).left
  · apply Vector.ext
    intro i hi
    rw [show (stateValue s)[i] = valueBits s[i] from Vector.getElem_map ..]
    exact (h ⟨i, hi⟩).right

/-- Row version of `stateNormalized_value_ext`. -/
lemma rowNormalized_value_ext (s : KeccakBitRow (F p)) (rhs : Vector ℕ 5)
    (h : ∀ i : Fin 5, Normalized s[i.val] ∧ valueBits s[i.val] = rhs[i.val]) :
    RowNormalized s ∧ rowValue s = rhs := by
  constructor
  · intro i
    exact (h i).left
  · apply Vector.ext
    intro i hi
    rw [show (rowValue s)[i] = valueBits s[i] from Vector.getElem_map ..]
    exact (h ⟨i, hi⟩).right

end Solution.KeccakF1600
end
