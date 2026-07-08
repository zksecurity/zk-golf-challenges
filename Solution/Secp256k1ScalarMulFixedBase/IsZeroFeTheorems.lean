import Solution.Secp256k1ScalarMulFixedBase.Params

/-!
# Emulated field zero test — supporting lemmas for `IsZeroFe`

Pure facts bridging the per-limb zero flags of `IsZeroFe` to the decoded
value: a big integer denotes `0` iff every limb is `0` (positional
uniqueness), and a canonical (`< P256`) emulated element decodes to `0` iff
every one of its four limbs is `0`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

section
variable {p : ℕ} [Fact p.Prime] {m : ℕ}

omit [Fact (Nat.Prime p)] in
/-- A big integer denotes `0` iff every limb is `0`: the denotation is the
positional sum `Σ x[i].val · 2^(B·i)` of non-negative terms. -/
theorem BigInt.value_eq_zero_iff {B : ℕ} (x : BigInt m (F p)) :
    BigInt.value B x = 0 ↔ ∀ i : Fin m, x[i] = 0 := by
  rw [BigInt.value_eq_sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have hterm := h i (Finset.mem_univ i)
    have hval : (x[i]).val = 0 := by
      have hpow : 0 < 2 ^ (B * i.val) := Nat.two_pow_pos _
      rcases Nat.mul_eq_zero.mp hterm with h0 | h0
      · exact h0
      · omega
    exact (ZMod.val_eq_zero _).mp hval
  · intro h i _
    rw [h i, ZMod.val_zero, Nat.zero_mul]

end

/-- A canonical emulated field element decodes to `0` iff all four limbs are
`0`: `decodeFe x = 0` forces `P256 ∣ x.value`, and a canonical value
(`< P256`) that is divisible by `P256` is `0`; positional uniqueness then
zeroes every limb. -/
theorem decodeFe_eq_zero_iff {x : Emu (F circomPrime)} (hx : Fe.Valid x) :
    decodeFe x = 0 ↔ (x[0] = 0 ∧ x[1] = 0 ∧ x[2] = 0 ∧ x[3] = 0) := by
  have hvalue : decodeFe x = 0 ↔ BigInt.value limbBits x = 0 := by
    simp only [decodeFe]
    constructor
    · intro h
      exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp h) hx.2
    · intro h
      rw [h, Nat.cast_zero]
  rw [hvalue, BigInt.value_eq_zero_iff]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ ⟨i, hi⟩
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3

end Solution.Secp256k1ScalarMulFixedBase
