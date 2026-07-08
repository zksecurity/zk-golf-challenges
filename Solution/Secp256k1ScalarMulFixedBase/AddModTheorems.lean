import Solution.Secp256k1ScalarMulFixedBase.Params

/-!
# `AddMod`/`SubMod` — bridge lemmas and arithmetic cores

The pure arithmetic content underpinning the emulated-field `AddMod` gadget,
factored out of the gadget file (per the style guide) so the gadget's
`soundness`/`completeness` proofs only wire these lemmas together.

The first sections (`emuOfNat`/`pConst` facts, padded-coefficient `polyValue`
machinery) are shared with `SubMod`, whose own cores live in
`SubModTheorems.lean` (which imports this file).
-/

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

/-! ## Numeric facts about the emulated prime and the limb parameters -/

lemma P256_pos : 0 < P256 := by decide

/-- The emulated prime fits in the `numLimbs · limbBits = 256` available bits. -/
lemma P256_lt : P256 < 2 ^ (limbBits * numLimbs) := by decide

/-- A limb value fits in the circuit field. -/
lemma two_pow_limb_lt : 2 ^ limbBits < circomPrime := by decide

/-- The sum of two limb values fits in the circuit field. -/
lemma limb_add_lt : 2 ^ limbBits + 2 ^ limbBits < circomPrime := by decide

/-- The sum of two limb values is within the `EqViaCarries` coefficient bound. -/
lemma limb_add_le_bound :
    2 ^ limbBits + 2 ^ limbBits ≤ (numLimbs + 1) * 2 ^ (2 * limbBits) := by decide

/-! ## `limbOfNat` and `emuOfNat` facts -/

lemma limbOfNat_lt (v k : ℕ) : limbOfNat v k < 2 ^ limbBits :=
  Nat.mod_lt _ (Nat.two_pow_pos limbBits)

lemma val_limbOfNat (v k : ℕ) :
    ((limbOfNat v k : ℕ) : F circomPrime).val = limbOfNat v k :=
  ZMod.val_natCast_of_lt (lt_trans (limbOfNat_lt v k) two_pow_limb_lt)

lemma emuOfNat_getElem (v k : ℕ) (hk : k < numLimbs) :
    (emuOfNat v)[k]'hk = ((limbOfNat v k : ℕ) : F circomPrime) := by
  simp only [emuOfNat, Vector.getElem_ofFn]

/-- `emuOfNat` produces normalized limbs. -/
lemma emuOfNat_normalized (v : ℕ) : (emuOfNat v).Normalized limbBits := by
  intro i
  rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
  exact limbOfNat_lt v i.val

/-- `emuOfNat` denotes its argument (for values that fit in 256 bits). -/
lemma value_emuOfNat {v : ℕ} (hv : v < 2 ^ (limbBits * numLimbs)) :
    BigInt.value limbBits (emuOfNat v) = v := by
  rw [BigInt.value_eq_sum]
  have hsum : (∑ k : Fin numLimbs, ((emuOfNat v)[k]).val * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range numLimbs,
          (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (v / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.getElem_fin, emuOfNat_getElem v i.val i.isLt, val_limbOfNat]
    rfl
  rw [hsum, limb_decomp_mod, Nat.mod_eq_of_lt hv]

/-- The little-endian limb recomposition of the emulated prime. -/
lemma limb_sum_P256 :
    (∑ k ∈ Finset.range numLimbs, limbOfNat P256 k * 2 ^ (limbBits * k)) = P256 := by
  have h : (∑ k ∈ Finset.range numLimbs, limbOfNat P256 k * 2 ^ (limbBits * k))
      = ∑ k ∈ Finset.range numLimbs,
          (P256 / 2 ^ (limbBits * k) % 2 ^ limbBits) * 2 ^ (limbBits * k) :=
    Finset.sum_congr rfl fun k _ => rfl
  rw [h, limb_decomp_mod, Nat.mod_eq_of_lt P256_lt]

/-! ## `pConst` evaluation facts -/

lemma eval_pConst_getElem (env : Environment (F circomPrime)) (k : ℕ) (hk : k < numLimbs) :
    Expression.eval env (pConst[k]'hk) = ((limbOfNat P256 k : ℕ) : F circomPrime) :=
  congrArg (Expression.eval env) (Vector.getElem_ofFn ..)

lemma eval_pConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) pConst = emuOfNat P256 := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, eval_pConst_getElem env k hk, emuOfNat_getElem P256 k hk]

lemma pConst_normalized (env : Environment (F circomPrime)) :
    BigInt.Normalized limbBits (Vector.map (Expression.eval env) pConst) := by
  rw [eval_pConst]
  exact emuOfNat_normalized P256

lemma pConst_value (env : Environment (F circomPrime)) :
    BigInt.value limbBits (Vector.map (Expression.eval env) pConst) = P256 := by
  rw [eval_pConst]
  exact value_emuOfNat P256_lt

/-! ## Witnessed-output (`var`-vector) evaluation facts -/

lemma eval_outVar_getElem (env : Environment (F circomPrime)) (i₀ k : ℕ) (hk : k < numLimbs) :
    (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var (F := F circomPrime) { index := i₀ + i }))[k]'hk
      = env.get (i₀ + k) := by
  simp [circuit_norm]

/-- Limb bound for the witnessed output cells, extracted from its
`Normalized` fact. -/
lemma outVar_val_lt (env : Environment (F circomPrime)) (i₀ : ℕ)
    (h : BigInt.Normalized limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))) :
    ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits := by
  intro k hk
  have hval := h ⟨k, hk⟩
  rwa [Fin.getElem_fin, eval_outVar_getElem env i₀ k hk] at hval

/-- `value` of the witnessed output vector as a `range` sum of cell values. -/
lemma value_outVar (B : ℕ) (env : Environment (F circomPrime)) (i₀ : ℕ) :
    BigInt.value B (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
      = ∑ k ∈ Finset.range numLimbs, (env.get (i₀ + k)).val * 2 ^ (B * k) := by
  rw [BigInt.value_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun k => (env.get (i₀ + k)).val * 2 ^ (B * k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.getElem_fin, eval_outVar_getElem env i₀ i.val i.isLt]

/-- `value` of an arbitrary emulated element as a `range` sum (guarded getElem). -/
lemma value_eq_range_sum (B : ℕ) (x : Emu (F circomPrime)) :
    BigInt.value B x
      = ∑ k ∈ Finset.range numLimbs,
          (if h : k < numLimbs then (x[k]'h).val else 0) * 2 ^ (B * k) := by
  rw [BigInt.value_eq_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < numLimbs then (x[k]'h).val else 0) * 2 ^ (B * k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.isLt, Fin.getElem_fin]

/-! ## Padded-coefficient `polyValue` machinery

`AddMod`/`SubMod` feed `EqViaCarries` coefficient vectors of length
`2·numLimbs − 1` whose upper coefficients are the constant `0`. `polyValue`
of such a vector collapses to a `range numLimbs` sum of the per-limb values. -/

/-- Master lemma: `polyValue` of a zero-padded coefficient vector, given the
per-limb coefficient values `c`. -/
lemma polyValue_padded (B : ℕ) (env : Environment (F circomPrime))
    (f : (k : Fin (2 * numLimbs - 1)) → k.val < numLimbs → Expression (F circomPrime))
    (c : ℕ → ℕ)
    (hval : ∀ (k : Fin (2 * numLimbs - 1)) (h : k.val < numLimbs),
      (Expression.eval env (f k h)).val = c k.val) :
    polyValue B (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then f k h else 0))
      = ∑ k ∈ Finset.range numLimbs, c k * 2 ^ (B * k) := by
  have hterm : ∀ k : Fin (2 * numLimbs - 1),
      ((Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then f k h else 0))[k.val]).val * 2 ^ (B * k.val)
      = (if k.val < numLimbs then c k.val else 0) * 2 ^ (B * k.val) := by
    intro k
    rw [Vector.getElem_map, Vector.getElem_mapFinRange]
    by_cases hk : k.val < numLimbs
    · rw [dif_pos hk, if_pos hk, hval ⟨k.val, k.isLt⟩ hk]
    · rw [dif_neg hk, if_neg hk]
      norm_num [circuit_norm]
  rw [polyValue, Finset.sum_congr rfl (fun k _ => hterm k),
    Fin.sum_univ_eq_sum_range (fun k => (if k < numLimbs then c k else 0) * 2 ^ (B * k))]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by decide : numLimbs ≤ 2 * numLimbs - 1))
    (f := fun k => (if k < numLimbs then c k else 0) * 2 ^ (B * k))]
  · exact Finset.sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.mp hk)]
  · intro k _ hk
    rw [Finset.mem_range] at hk
    rw [if_neg hk, Nat.zero_mul]

/-! ## Per-coefficient value/bound helpers -/

/-- Value of a sum of two limb-bounded field elements (no wraparound). -/
lemma val_add_limb {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val = u.val + v.val :=
  ZMod.val_add_of_lt (by have := limb_add_lt; omega)

/-- `EqViaCarries` coefficient bound for a sum of two limb-bounded elements. -/
lemma bound_add_limb {u v : F circomPrime}
    (hu : u.val < 2 ^ limbBits) (hv : v.val < 2 ^ limbBits) :
    (u + v).val < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  have h := ZMod.val_add_le u v
  have := limb_add_le_bound
  omega

/-- Value of a boolean multiple of a prime limb (no wraparound). -/
lemma val_q_mul_limb {qN : ℕ} (hqN : qN ≤ 1) (k : ℕ) :
    (((qN : ℕ) : F circomPrime) * ((limbOfNat P256 k : ℕ) : F circomPrime)).val
      = qN * limbOfNat P256 k := by
  have hq_lt : qN < circomPrime := by
    have := two_pow_limb_lt
    have := Nat.two_pow_pos limbBits
    omega
  rw [ZMod.val_mul_of_lt, ZMod.val_natCast_of_lt hq_lt, val_limbOfNat]
  rw [ZMod.val_natCast_of_lt hq_lt, val_limbOfNat]
  have h1 := limbOfNat_lt P256 k
  have h2 : qN * limbOfNat P256 k ≤ 1 * limbOfNat P256 k :=
    Nat.mul_le_mul_right _ hqN
  have := two_pow_limb_lt
  omega

/-! ## `AddMod`: coefficient bounds, `polyValue` bridges, and arithmetic cores -/

namespace AddMod

/-- `EqViaCarries` coefficient bound for the `AddMod` `lhs` vector `a_k + b_k`. -/
lemma lhs_bounds (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha_norm : a.Normalized limbBits) (hb_norm : b.Normalized limbBits) :
    ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env
          (if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)).val
        < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  intro k
  by_cases hk : k.val < numLimbs
  · rw [dif_pos hk,
      show Expression.eval env (a_var[k.val]'hk + b_var[k.val]'hk)
        = Expression.eval env (a_var[k.val]'hk) + Expression.eval env (b_var[k.val]'hk) from rfl,
      show Expression.eval env (a_var[k.val]'hk) = a[k.val]'hk from by
        rw [← h_input_a, Vector.getElem_map],
      show Expression.eval env (b_var[k.val]'hk) = b[k.val]'hk from by
        rw [← h_input_b, Vector.getElem_map]]
    exact bound_add_limb (ha_norm ⟨k.val, hk⟩) (hb_norm ⟨k.val, hk⟩)
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

/-- `EqViaCarries` coefficient bound for the `AddMod` `rhs` vector
`q · p_k + r_k` (with `q` boolean). -/
lemma rhs_bounds (env : Environment (F circomPrime)) (i₀ : ℕ) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 1)
    (hr : ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits) :
    ∀ k : Fin (2 * numLimbs - 1),
      (Expression.eval env
          (if h : k.val < numLimbs
            then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
            else 0)).val
        < (numLimbs + 1) * 2 ^ (2 * limbBits) := by
  intro k
  by_cases hk : k.val < numLimbs
  · rw [dif_pos hk,
      show Expression.eval env
            (var { index := i₀ + numLimbs } * pConst[k.val]'hk + var { index := i₀ + k.val })
          = env.get (i₀ + numLimbs) * Expression.eval env (pConst[k.val]'hk)
            + env.get (i₀ + k.val) from rfl,
      hq, eval_pConst_getElem env k.val hk]
    have h1 := ZMod.val_add_le
      (((qN : ℕ) : F circomPrime) * ((limbOfNat P256 k.val : ℕ) : F circomPrime))
      (env.get (i₀ + k.val))
    rw [val_q_mul_limb hqN k.val] at h1
    have h2 := limbOfNat_lt P256 k.val
    have h3 : qN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have h4 := hr k.val hk
    have := limb_add_le_bound
    omega
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

/-- **`polyValue` bridge (lhs).** The `AddMod` `lhs` coefficient vector denotes
`a.value + b.value`. -/
lemma polyValue_lhs (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha_norm : a.Normalized limbBits) (hb_norm : b.Normalized limbBits) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0))
      = BigInt.value limbBits a + BigInt.value limbBits b := by
  refine (polyValue_padded limbBits env
      (fun k h => a_var[k.val]'h + b_var[k.val]'h)
      (fun k => (if h : k < numLimbs then (a[k]'h).val else 0)
        + (if h : k < numLimbs then (b[k]'h).val else 0)) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env (a_var[k.val]'hk + b_var[k.val]'hk)
        = Expression.eval env (a_var[k.val]'hk) + Expression.eval env (b_var[k.val]'hk) from rfl,
      show Expression.eval env (a_var[k.val]'hk) = a[k.val]'hk from by
        rw [← h_input_a, Vector.getElem_map],
      show Expression.eval env (b_var[k.val]'hk) = b[k.val]'hk from by
        rw [← h_input_b, Vector.getElem_map],
      val_add_limb (u := a[k.val]'hk) (v := b[k.val]'hk)
        (ha_norm ⟨k.val, hk⟩) (hb_norm ⟨k.val, hk⟩)]
    simp only [dif_pos hk]
  · rw [value_eq_range_sum limbBits a, value_eq_range_sum limbBits b,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => add_mul _ _ _

/-- **`polyValue` bridge (rhs).** The `AddMod` `rhs` coefficient vector denotes
`q · P256 + r.value` (with `q` boolean). -/
lemma polyValue_rhs (env : Environment (F circomPrime)) (i₀ : ℕ) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 1)
    (hr : ∀ k : ℕ, k < numLimbs → (env.get (i₀ + k)).val < 2 ^ limbBits) :
    polyValue limbBits (Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
          if h : k.val < numLimbs
          then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
          else 0))
      = qN * P256 + BigInt.value limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) := by
  refine (polyValue_padded limbBits env
      (fun k h => var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val })
      (fun k => qN * limbOfNat P256 k + (env.get (i₀ + k)).val) ?_).trans ?_
  · intro k hk
    rw [show Expression.eval env
          (var { index := i₀ + numLimbs } * pConst[k.val]'hk + var { index := i₀ + k.val })
        = env.get (i₀ + numLimbs) * Expression.eval env (pConst[k.val]'hk)
          + env.get (i₀ + k.val) from rfl,
      hq, eval_pConst_getElem env k.val hk,
      ZMod.val_add_of_lt, val_q_mul_limb hqN k.val]
    -- side goal: the coefficient does not wrap mod the circuit prime
    rw [val_q_mul_limb hqN k.val]
    have h2 := limbOfNat_lt P256 k.val
    have h3 : qN * limbOfNat P256 k.val ≤ 1 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have h4 := hr k.val hk
    have := limb_add_lt
    omega
  · rw [value_outVar limbBits env i₀]
    have hsplit : (∑ k ∈ Finset.range numLimbs,
          (qN * limbOfNat P256 k + (env.get (i₀ + k)).val) * 2 ^ (limbBits * k))
        = (∑ k ∈ Finset.range numLimbs, qN * (limbOfNat P256 k * 2 ^ (limbBits * k)))
          + ∑ k ∈ Finset.range numLimbs, (env.get (i₀ + k)).val * 2 ^ (limbBits * k) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, ← Finset.mul_sum, limb_sum_P256]

/-- **Soundness core.** Given the per-subcircuit facts left by
`circuit_proof_start` — the boolean quotient assert, `Normalize`, `LessThan`
and `EqViaCarries` — the witnessed output is canonical and decodes to the
base-field sum. -/
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
              (if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)).val
            < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
        ∀ k : Fin (2 * numLimbs - 1),
          (Expression.eval env
              (if h : k.val < numLimbs
                then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
                else 0)).val
            < (numLimbs + 1) * 2 ^ (2 * limbBits)) →
        polyValue limbBits (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)) =
          polyValue limbBits (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
              if h : k.val < numLimbs
              then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
              else 0))) :
    Fe.Valid (Vector.map (Expression.eval env)
        (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
      decodeFe (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i }))
        = decodeFe a + decodeFe b := by
  obtain ⟨ha_norm, ha_lt⟩ := ha
  obtain ⟨hb_norm, hb_lt⟩ := hb
  -- the quotient cell is boolean
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
    ⟨lhs_bounds env a_var b_var a b h_input_a h_input_b ha_norm hb_norm,
      rhs_bounds env i₀ _ hq_cast hq01 (outVar_val_lt env i₀ hr_norm)⟩
  rw [polyValue_lhs env a_var b_var a b h_input_a h_input_b ha_norm hb_norm,
    polyValue_rhs env i₀ _ hq_cast hq01 (outVar_val_lt env i₀ hr_norm)] at h_polyeq
  -- canonicity from LessThan
  have hr_lt : BigInt.value limbBits (Vector.map (Expression.eval env)
      (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) < P256 := by
    have h := h_lt_impl ⟨hr_norm, pConst_normalized env⟩
    rwa [pConst_value env] at h
  refine ⟨⟨hr_norm, hr_lt⟩, ?_⟩
  -- push the ℕ identity `a + b = q·P256 + r` into the emulated field
  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) h_polyeq
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _,
    mul_zero, zero_add] at hcast
  simp only [decodeFe]
  exact hcast.symm

/-- **Completeness core.** The honest witnesses (`r = (a + b) % P256` limbs,
`q = (a + b) / P256`) satisfy every constraint of `AddMod.main`. -/
lemma completeness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha : Fe.Valid a) (hb : Fe.Valid b)
    (h_wit_r : ∀ i : Fin numLimbs,
      env.get (i₀ + i.val)
        = (emuOfNat ((BigInt.value limbBits a + BigInt.value limbBits b) % P256))[i.val])
    (h_wit_q : env.get (i₀ + numLimbs)
      = (((BigInt.value limbBits a + BigInt.value limbBits b) / P256 : ℕ) : F circomPrime)) :
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
                (if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)).val
              < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
          ∀ k : Fin (2 * numLimbs - 1),
            (Expression.eval env
                (if h : k.val < numLimbs
                  then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
                  else 0)).val
              < (numLimbs + 1) * 2 ^ (2 * limbBits)) ∧
          polyValue limbBits (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
                if h : k.val < numLimbs then a_var[k.val]'h + b_var[k.val]'h else 0)) =
            polyValue limbBits (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * numLimbs - 1) fun k =>
                if h : k.val < numLimbs
                then var { index := i₀ + numLimbs } * pConst[k.val]'h + var { index := i₀ + k.val }
                else 0)) := by
  obtain ⟨ha_norm, ha_lt⟩ := ha
  obtain ⟨hb_norm, hb_lt⟩ := hb
  set va := BigInt.value limbBits a with hva
  set vb := BigInt.value limbBits b with hvb
  -- the quotient is boolean since a + b < 2·P256
  have hq2 : (va + vb) / P256 ≤ 1 := by
    have h := (Nat.div_lt_iff_lt_mul P256_pos).mpr (by omega : va + vb < 2 * P256)
    omega
  set qNat := (va + vb) / P256 with hqNat
  set rN := (va + vb) % P256 with hrN
  have hrN_lt : rN < P256 := Nat.mod_lt _ P256_pos
  have hrN_pow : rN < 2 ^ (limbBits * numLimbs) := lt_trans hrN_lt P256_lt
  -- the witnessed output limbs are the canonical digits of (a + b) % P256
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
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq2 with h | h <;> rw [h] <;> norm_num
  · -- LessThan: r < p
    rw [hrv_val, pConst_value env]
    exact hrN_lt
  · exact lhs_bounds env a_var b_var a b h_input_a h_input_b ha_norm hb_norm
  · exact rhs_bounds env i₀ qNat h_wit_q hq2 (outVar_val_lt env i₀ hrv_norm)
  · -- the EqViaCarries identity: a + b = q·P256 + r over ℕ
    rw [polyValue_lhs env a_var b_var a b h_input_a h_input_b ha_norm hb_norm,
      polyValue_rhs env i₀ qNat h_wit_q hq2 (outVar_val_lt env i₀ hrv_norm),
      hrv_val]
    calc va + vb = P256 * qNat + rN := by
          rw [hqNat, hrN]
          exact (Nat.div_add_mod (va + vb) P256).symm
      _ = qNat * P256 + rN := by ring

end AddMod

end Solution.Secp256k1ScalarMulFixedBase
