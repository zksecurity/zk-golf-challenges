import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256
namespace And32

/-!
# Helper lemmas for `And32`

Gadget-private lemmas for the 32-bit bitwise AND gadget. Shared lemmas
(`sum_bool_lt_two_pow`, `testBit_binary_sum`, ...) live in `Theorems`.
-/

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

end And32
end Solution.SHA256
end
