import Solution.Secp256k1ScalarMulFixedBase.AddModTheorems

/-!
# `SubMod` — bridge lemmas and arithmetic cores

The pure arithmetic content underpinning the emulated-field `SubMod` gadget,
factored out of the gadget file so its `soundness`/`completeness` proofs only
wire these lemmas together. Builds on the shared `emuOfNat`/`pConst`/padded
`polyValue` machinery in `AddModTheorems`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

namespace SubMod

/-- The borrow-form witness identity: for canonical `a`, `b`, the reduced
difference `r = (a + P256 − b) % P256` satisfies `r + b = a + q·P256` with the
borrow bit `q = [a < b]`. -/
lemma sub_witness_identity {va vb : ℕ} (hva : va < P256) (hvb : vb < P256) :
    (va + P256 - vb) % P256 + vb = va + (if va < vb then 1 else 0) * P256 := by
  by_cases h : va < vb
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega : va + P256 - vb < P256)]
    omega
  · rw [if_neg h, show va + P256 - vb = (va - vb) + P256 from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : va - vb < P256)]
    omega

/-- `EqViaCarries` coefficient bound for the `SubMod` `lhs` vector `r_k + b_k`. -/
lemma lhs_bounds (env : Environment (F circomPrime)) (i₀ : ℕ)
    (b_var : Var Emu (F circomPrime)) (b : Emu (F circomPrime))
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (hb_norm : b.Normalized limbBits)
    (hr : ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits) :
    ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env
          (if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h else 0)).val
        < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  intro k
  by_cases hk : k.val < numLimbs
  · rw [dif_pos hk,
      show Expression.eval env (var { index := i₀ + k.val } + b_var[k.val]'hk)
        = env.get (i₀ + k.val) + Expression.eval env (b_var[k.val]'hk) from rfl,
      show Expression.eval env (b_var[k.val]'hk) = b[k.val]'hk from by
        rw [← h_input_b, Vector.getElem_map]]
    exact bound_add_limb (hr k.val hk) (hb_norm ⟨k.val, hk⟩)
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

/-- `EqViaCarries` coefficient bound for the `SubMod` `rhs` vector
`a_k + q · p_k` (with `q` boolean). -/
lemma rhs_bounds (env : Environment (F circomPrime)) (i₀ : ℕ)
    (a_var : Var Emu (F circomPrime)) (a : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (ha_norm : a.Normalized limbBits) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 1) :
    ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env
          (if h : k.val < numLimbs
            then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
            else 0)).val
        < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  intro k
  by_cases hk : k.val < numLimbs
  · rw [dif_pos hk,
      show Expression.eval env
            (a_var[k.val]'hk + var { index := i₀ + numLimbs } * pConst[k.val]'hk)
          = Expression.eval env (a_var[k.val]'hk)
            + env.get (i₀ + numLimbs) * Expression.eval env (pConst[k.val]'hk) from rfl,
      show Expression.eval env (a_var[k.val]'hk) = a[k.val]'hk from by
        rw [← h_input_a, Vector.getElem_map],
      hq, eval_pConst_getElem env k.val hk]
    have h1 : (a[k.val]'hk).val < 2 ^ limbBits := ha_norm ⟨k.val, hk⟩
    have h2 := ZMod.val_add_le (a[k.val]'hk)
      (((qN : ℕ) : F circomPrime) * ((limbOfNat P256 k.val : ℕ) : F circomPrime))
    rw [val_q_mul_limb hqN k.val] at h2
    have h3 := limbOfNat_lt P256 k.val
    have h4 : qN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have := limb_add_le_bound
    omega
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

/-- **`polyValue` bridge (lhs).** The `SubMod` `lhs` coefficient vector denotes
`r.value + b.value`. -/
lemma polyValue_lhs (env : Environment (F circomPrime)) (i₀ : ℕ)
    (b_var : Var Emu (F circomPrime)) (b : Emu (F circomPrime))
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (hb_norm : b.Normalized limbBits)
    (hr : ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h else 0))
      = BigInt.value limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
        + BigInt.value limbBits b := by
  refine (polyValue_padded limbBits env
      (fun k h => var { index := i₀ + k.val } + b_var[k.val]'h)
      (fun k => (env.get (i₀ + k)).val
        + (if h : k < numLimbs then (b[k]'h).val else 0)) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env (var { index := i₀ + k.val } + b_var[k.val]'hk)
        = env.get (i₀ + k.val) + Expression.eval env (b_var[k.val]'hk) from rfl,
      show Expression.eval env (b_var[k.val]'hk) = b[k.val]'hk from by
        rw [← h_input_b, Vector.getElem_map],
      val_add_limb (u := env.get (i₀ + k.val)) (v := b[k.val]'hk)
        (hr k.val hk) (hb_norm ⟨k.val, hk⟩)]
    simp only [dif_pos hk]
  · rw [value_outVar limbBits env i₀, value_eq_range_sum limbBits b,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => add_mul _ _ _

/-- **`polyValue` bridge (rhs).** The `SubMod` `rhs` coefficient vector denotes
`a.value + q · P256` (with `q` boolean). -/
lemma polyValue_rhs (env : Environment (F circomPrime)) (i₀ : ℕ)
    (a_var : Var Emu (F circomPrime)) (a : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (ha_norm : a.Normalized limbBits) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 1) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs
          then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
          else 0))
      = BigInt.value limbBits a + qN * P256 := by
  refine (polyValue_padded limbBits env
      (fun k h => a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h)
      (fun k => (if h : k < numLimbs then (a[k]'h).val else 0)
        + qN * limbOfNat P256 k) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env
          (a_var[k.val]'hk + var { index := i₀ + numLimbs } * pConst[k.val]'hk)
        = Expression.eval env (a_var[k.val]'hk)
          + env.get (i₀ + numLimbs) * Expression.eval env (pConst[k.val]'hk) from rfl,
      show Expression.eval env (a_var[k.val]'hk) = a[k.val]'hk from by
        rw [← h_input_a, Vector.getElem_map],
      hq, eval_pConst_getElem env k.val hk,
      ZMod.val_add_of_lt, val_q_mul_limb hqN k.val]
    · simp only [dif_pos hk]
    · -- side goal: the coefficient does not wrap mod the circuit prime
      rw [val_q_mul_limb hqN k.val]
      have h1 : (a[k.val]'hk).val < 2 ^ limbBits := ha_norm ⟨k.val, hk⟩
      have h2 := limbOfNat_lt P256 k.val
      have h3 : qN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
        Nat.mul_le_mul_right _ hqN
      have := limb_add_lt
      omega
  · -- sum evaluation
    rw [value_eq_range_sum limbBits a]
    have hsplit : (∑ k ∈ Finset.range numLimbs,
          ((if h : k < numLimbs then (a[k]'h).val else 0) + qN * limbOfNat P256 k)
            * 2 ^ (limbBits * k))
        = (∑ k ∈ Finset.range numLimbs,
            (if h : k < numLimbs then (a[k]'h).val else 0) * 2 ^ (limbBits * k))
          + ∑ k ∈ Finset.range numLimbs, qN * (limbOfNat P256 k * 2 ^ (limbBits * k)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, ← Finset.mul_sum, limb_sum_P256]

/-- **Soundness core.** Given the per-subcircuit facts left by
`circuit_proof_start`, the witnessed output is canonical and decodes to the
base-field difference. -/
lemma soundness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha : Fe.Valid a) (hb : Fe.Valid b)
    (hq_bool : env.get (i₀ + numLimbs) * (env.get (i₀ + numLimbs) + -1) = 0)
    (hr_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i })))
    (h_lt_impl :
      BigInt.Normalized limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
        BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) →
        BigInt.value limbBits (Vector.map (Expression.eval env)
            (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) <
          BigInt.value limbBits (Vector.map (Expression.eval env) pConst))
    (h_eq_impl :
      ((∀ k : Fin (2 * numLimbs - 1),
          (Expression.eval env
              (if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h
                else 0)).val
            < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
        ∀ k : Fin (2 * numLimbs - 1),
          (Expression.eval env
              (if h : k.val < numLimbs
                then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
                else 0)).val
            < (numLimbs + 1) * 2 ^ (2 * limbBits)) →
        polyValue limbBits (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h
              else 0)) =
          polyValue limbBits (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs
              then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
              else 0))) :
    Fe.Valid (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
      decodeFe (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
        = decodeFe a - decodeFe b := by
  obtain ⟨ha_norm, ha_lt⟩ := ha
  obtain ⟨hb_norm, hb_lt⟩ := hb
  -- the borrow cell is boolean
  have hq01 : (env.get (i₀ + numLimbs)).val ≤ 1 := by
    rcases mul_eq_zero.mp hq_bool with h | h
    · rw [h, ZMod.val_zero]
      omega
    · rw [add_neg_eq_zero] at h
      rw [h, ZMod.val_one]
  have hq_cast : env.get (i₀ + numLimbs)
      = (((env.get (i₀ + numLimbs)).val : ℕ) : F circomPrime) :=
    (ZMod.natCast_zmod_val _).symm
  -- discharge the EqViaCarries assumptions and evaluate both polyValues
  have h_polyeq := h_eq_impl
    ⟨lhs_bounds env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hr_norm),
      rhs_bounds env i₀ a_var a h_input_a ha_norm _ hq_cast hq01⟩
  rw [polyValue_lhs env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hr_norm),
    polyValue_rhs env i₀ a_var a h_input_a ha_norm _ hq_cast hq01] at h_polyeq
  -- canonicity from LessThan
  have hr_lt : BigInt.value limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) < P256 := by
    have h := h_lt_impl ⟨hr_norm, pConst_normalized env⟩
    rwa [pConst_value env] at h
  refine ⟨⟨hr_norm, hr_lt⟩, ?_⟩
  -- push the ℕ identity `r + b = a + q·P256` into the emulated field
  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) h_polyeq
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _,
    mul_zero, add_zero] at hcast
  simp only [decodeFe]
  exact eq_sub_of_add_eq hcast

/-- **Completeness core.** The honest witnesses (`r = (a + P256 − b) % P256`
limbs, borrow bit `q = [a < b]`) satisfy every constraint of `SubMod.main`. -/
lemma completeness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h_wit_r : ∀ i : Fin numLimbs,
      env.get (i₀ + i.val)
        = (emuOfNat ((BigInt.value limbBits a + P256 - BigInt.value limbBits b) % P256))[i.val])
    (h_wit_q : env.get (i₀ + numLimbs)
      = (((if BigInt.value limbBits a < BigInt.value limbBits b then 1 else 0 : ℕ))
          : F circomPrime)) :
    env.get (i₀ + numLimbs) * (env.get (i₀ + numLimbs) + -1) = 0 ∧
      BigInt.Normalized limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
        ((BigInt.Normalized limbBits (Vector.map (Expression.eval env)
              (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
            BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst)) ∧
          BigInt.value limbBits (Vector.map (Expression.eval env)
              (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) <
            BigInt.value limbBits (Vector.map (Expression.eval env) pConst)) ∧
        ((∀ k : Fin (2 * numLimbs - 1),
            (Expression.eval env
                (if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h
                  else 0)).val
              < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
          ∀ k : Fin (2 * numLimbs - 1),
            (Expression.eval env
                (if h : k.val < numLimbs
                  then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
                  else 0)).val
              < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
          polyValue limbBits (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
                if h : k.val < numLimbs then var { index := i₀ + k.val } + b_var[k.val]'h
                else 0)) =
            polyValue limbBits (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
                if h : k.val < numLimbs
                then a_var[k.val]'h + var { index := i₀ + numLimbs } * pConst[k.val]'h
                else 0)) := by
  obtain ⟨ha_norm, ha_lt⟩ := ha
  obtain ⟨hb_norm, hb_lt⟩ := hb
  set va := BigInt.value limbBits a with hva
  set vb := BigInt.value limbBits b with hvb
  set qNat : ℕ := if va < vb then 1 else 0 with hqNat
  set rN := (va + P256 - vb) % P256 with hrN
  have hqNat_le : qNat ≤ 1 := by
    rw [hqNat]
    split <;> omega
  have hrN_lt : rN < P256 := Nat.mod_lt _ P256_pos
  have hrN_pow : rN < 2 ^ (limbBits * numLimbs) := lt_trans hrN_lt P256_lt
  -- the borrow-form witness identity
  have hkey : rN + vb = va + qNat * P256 := by
    rw [hrN, hqNat]
    exact sub_witness_identity ha_lt hb_lt
  -- the witnessed output limbs are the canonical digits of (a + P256 − b) % P256
  have hwit : ∀ i : Fin numLimbs, env.get (i₀ + i.val)
      = ((rN / 2 ^ (limbBits * i.val) % 2 ^ limbBits : ℕ) : F circomPrime) := by
    intro i
    rw [h_wit_r i, emuOfNat_getElem _ i.val i.isLt]
    rfl
  have hrv_norm : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) :=
    MulMod.normalized_mapRange i₀ rN env two_pow_limb_lt hwit
  have hrv_val : BigInt.value limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) = rN :=
    BigInt.value_mapRange i₀ rN env two_pow_limb_lt hrN_pow hwit
  refine ⟨?_, hrv_norm, ⟨⟨hrv_norm, pConst_normalized env⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · -- the boolean assert
    rw [h_wit_q]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqNat_le with h | h <;> rw [h] <;> norm_num
  · -- LessThan: r < p
    rw [hrv_val, pConst_value env]
    exact hrN_lt
  · exact lhs_bounds env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hrv_norm)
  · exact rhs_bounds env i₀ a_var a h_input_a ha_norm qNat h_wit_q hqNat_le
  · -- the EqViaCarries identity: r + b = a + q·P256 over ℕ
    rw [polyValue_lhs env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hrv_norm),
      polyValue_rhs env i₀ a_var a h_input_a ha_norm qNat h_wit_q hqNat_le,
      hrv_val]
    exact hkey

end SubMod

end Solution.Secp256k1ScalarMulFixedBase
