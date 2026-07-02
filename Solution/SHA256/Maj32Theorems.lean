import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256
namespace Maj32

/-!
# Helper lemmas for `Maj32`

Gadget-private lemmas for the majority function `Maj(a, b, c)`. Shared lemmas
(`sum_bool_lt_two_pow`, `testBit_binary_sum`, ...) live in `Theorems`.
-/

/-- For boolean field elements a, b, c: the field expression t + c*(a+b-2t) where t=a*b
    has val equal to the bitwise Nat majority of a.val, b.val, c.val -/
lemma maj_eq_val_maj {p : ℕ} [Fact p.Prime]
    {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    (a * b + c * (a + b - 2 * (a * b))).val = (a.val &&& b.val) ^^^ (a.val &&& c.val) ^^^ (b.val &&& c.val) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    norm_num [ha, hb, hc, ZMod.val_zero, ZMod.val_one]

/-- For boolean field elements a, b, c: the field expression t + c*(a+b-2t) where t=a*b
    is boolean -/
lemma maj_is_bool {α : Type*} [Ring α] {a b c : α} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    IsBool (a * b + c * (a + b - 2 * (a * b))) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    simp [ha, hb, hc] <;> norm_num <;> first | exact IsBool.zero | exact IsBool.one

lemma bool_finsum_maj (n : ℕ) (f g k : Fin n → ℕ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) (hg : ∀ i, g i = 0 ∨ g i = 1) (hk : ∀ i, k i = 0 ∨ k i = 1) :
    ((∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, g i * 2^i.val)) ^^^
    ((∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val)) ^^^
    ((∑ i : Fin n, g i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val))
    = ∑ i : Fin n, ((f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i)) * 2^i.val := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < n
  · have hfg : ∀ i : Fin n, (f i &&& g i) = 0 ∨ (f i &&& g i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
    have hfk : ∀ i : Fin n, (f i &&& k i) = 0 ∨ (f i &&& k i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hk i with hki | hki <;> simp [hfi, hki]
    have hgk : ∀ i : Fin n, (g i &&& k i) = 0 ∨ (g i &&& k i) = 1 := fun i => by
      rcases hg i with hgi | hgi <;> rcases hk i with hki | hki <;> simp [hgi, hki]
    have hmaj : ∀ i : Fin n, (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i) = 0 ∨
        (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> rcases hk i with hki | hki <;>
        simp [hfi, hgi, hki]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and,
        testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩,
        testBit_binary_sum n k hk ⟨j, hj⟩,
        testBit_binary_sum n _ hmaj ⟨j, hj⟩]
    rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;>
      rcases hk ⟨j, hj⟩ with hki | hki <;> simp [hfi, hgi, hki]
  · push_neg at hj
    have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hfS := sum_bool_lt_two_pow n f (fun i => by rcases hf i with hx | hx <;> simp [hx])
    have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with hx | hx <;> simp [hx])
    have hkS := sum_bool_lt_two_pow n k (fun i => by rcases hk i with hx | hx <;> simp [hx])
    have hmajS := sum_bool_lt_two_pow n (fun i => (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i))
        (fun i => by
          have hfi := hf i; have hgi := hg i; have hki := hk i
          rcases hfi with hfi | hfi <;> rcases hgi with hgi | hgi <;> rcases hki with hki | hki <;>
            simp [hfi, hgi, hki])
    have hand1 : (∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, g i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hfS
    have hand2 : (∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hfS
    have hand3 : (∑ i : Fin n, g i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hgS
    have hxor12 := Nat.xor_lt_two_pow hand1 hand2
    have hxor_all := Nat.xor_lt_two_pow hxor12 hand3
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hxor_all pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hmajS pow_le)]

/-- Spec holds for any vector `z` whose bits satisfy the per-bit constraint. -/
lemma spec_of_constraint
    (input_a input_b input_c z : fields 32 (F p))
    (ha : Normalized input_a) (hb : Normalized input_b) (hc : Normalized input_c)
    (h_eq : ∀ i : Fin 32, z[i] =
      input_a[i] * input_b[i] + input_c[i] * (input_a[i] + input_b[i] - 2 * (input_a[i] * input_b[i]))) :
    valueBits z = Specs.SHA256.Maj (valueBits input_a) (valueBits input_b) (valueBits input_c) ∧
    Normalized z := by
  have ha_b : ∀ i : Fin 32, IsBool input_a[i] := fun i => ha i
  have hb_b : ∀ i : Fin 32, IsBool input_b[i] := fun i => hb i
  have hc_b : ∀ i : Fin 32, IsBool input_c[i] := fun i => hc i
  have h_norm : ∀ i : Fin 32, z[i] = 0 ∨ z[i] = 1 := by
    intro i; rw [h_eq i]; exact maj_is_bool (ha_b i) (hb_b i) (hc_b i)
  have ha_val : ∀ i : Fin 32, (input_a[i] : F p).val = 0 ∨ (input_a[i] : F p).val = 1 :=
    fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hb_val : ∀ i : Fin 32, (input_b[i] : F p).val = 0 ∨ (input_b[i] : F p).val = 1 :=
    fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc_val : ∀ i : Fin 32, (input_c[i] : F p).val = 0 ∨ (input_c[i] : F p).val = 1 :=
    fun i => by rcases hc i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_bit_eq : ∀ i : Fin 32, (z[i] : F p).val =
      ((input_a[i] : F p).val &&& (input_b[i] : F p).val) ^^^
      ((input_a[i] : F p).val &&& (input_c[i] : F p).val) ^^^
      ((input_b[i] : F p).val &&& (input_c[i] : F p).val) := by
    intro i; rw [h_eq i]; exact maj_eq_val_maj (ha_b i) (hb_b i) (hc_b i)
  have key' : ((∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val)) ^^^
      ((∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val)) ^^^
      ((∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val)) =
      ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := by
    rw [bool_finsum_maj 32 _ _ _ ha_val hb_val hc_val]
    apply Finset.sum_congr rfl
    intro i _
    rw [h_bit_eq i]
  have Maj_def : ∀ a b c : ℕ, Specs.SHA256.Maj a b c = (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) :=
    fun _ _ _ => rfl
  have h_z_eq : valueBits z = ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := rfl
  have ha_eq : valueBits input_a = ∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val := rfl
  have hb_eq : valueBits input_b = ∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val := rfl
  have hc_eq : valueBits input_c = ∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val := rfl
  refine ⟨?_, h_norm⟩
  rw [Maj_def, ha_eq, hb_eq, hc_eq, h_z_eq]
  exact key'.symm

end Maj32
end Solution.SHA256
end
