import Solution.Secp256k1ScalarMul.MulModTheorems

/-!
# `MulModL` — loose (non-canonical) multiplication cores

Arithmetic cores for the lazy multiplication gadget `MulModL`, which computes
`c ≡ a · b (mod n)` but omits the `LessThan` canonical check: the output is
normalized-only and the spec is at the `Fp` level.

These mirror the canonical cores in `MulModTheorems` but:
- *soundness* stops at the integer identity `a·b = q·n + r` (no `remainder_eq`,
  so no `r < n` needed);
- *completeness* bounds the honest quotient `q = a·b/n < 2^(B·m)` from
  `a < n` and `b < 2^(B·m)` (one canonical + one merely-normalized operand),
  rather than from `a < n ∧ b < n`, and omits the `LessThan` obligation.

The `b` operand is only required normalized (`< 2^(B·m)`), so a `MulModL` may
consume a loose (possibly `≥ n`) second operand — the enabler for lazy chains.
-/

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

namespace MulMod

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-- **Loose soundness core.** Same hypotheses as `mulMod_soundness_core` minus
`h_lt_impl`; concludes the raw integer identity `a·b = q·n + r` (with `r`
normalized), which suffices for the `decodeFe`-level spec. -/
lemma mulMod_soundness_core_loose {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1),
          (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                var { index := i₀ + m + k.val }
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
          polyValue B
            (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * m - 1) fun k ↦
                if h : k.val < m then
                  (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                    var { index := i₀ + m + k.val }
                else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B input.1 * BigInt.value B input.2.1
        = BigInt.value B (Vector.map (Expression.eval env)
              (Vector.mapRange m fun i ↦ var { index := i₀ + i })) * BigInt.value B input.2.2
          + BigInt.value B (Vector.map (Expression.eval env)
              (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set rVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }) with hrVar
  set qv := (Vector.map (Expression.eval env) qVar : BigInt m (F p)) with hqv
  set rv := (Vector.map (Expression.eval env) rVar : BigInt m (F p)) with hrv
  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [hqv, Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hr_norm ⟨j, hj⟩
    rwa [hrv, Fin.getElem_fin, Vector.getElem_map, hrVar,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar input_var.2.2)[k.val] + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce qVar input_var.2.2)[k.val])
      = sVec qVar input_var.2.2 (i₀ + m) := by
    rfl
  have h_polyeq := h_eq_impl ⟨fun k => coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield,
    fun k => by
      have hb := coeff_S_bound env qVar input_var.2.2 (i₀ + m) k hqd_lt hn_lt hrd_lt hfield
      rw [sVec, Vector.getElem_mapFinRange] at hb
      exact hb⟩
  rw [hS_eq] at h_polyeq
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = BigInt.value B input.1 * BigInt.value B input.2.1 := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, ← h_input]
  have hSplit := polyValue_sVec_split (B := B) env qVar input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar input_var.2.2 k hqd_lt hn_lt hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar input_var.2.2))
      = BigInt.value B qv * BigInt.value B input.2.2 := by
    rw [polyValue_Sqn_eq env qVar input_var.2.2 hqd_lt hn_lt hfield, ← h_input]
  have hrval : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) = BigInt.value B rv := by
    rw [hrv, hrVar]
  rw [hP] at h_polyeq
  rw [hSplit, hSqn, hrval] at h_polyeq
  exact ⟨hr_norm, h_polyeq⟩

/-- **Loose witnessed-product soundness core.** Bridges `witnessedMul` outputs to
`mulMod_soundness_core_loose`. -/
lemma mulMod_soundness_core_wm_loose {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val]))) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B input.1 * BigInt.value B input.2.1
        = BigInt.value B (Vector.map (Expression.eval env)
              (Vector.mapRange m fun i ↦ var { index := i₀ + i })) * BigInt.value B input.2.2
          + BigInt.value B (Vector.map (Expression.eval env)
              (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) := by
  have h_eq_impl' := eqImpl_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b)
    Qv (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
    heqAB_get heqQN_get h_eq_impl
  exact mulMod_soundness_core_loose (B := B) hp i₀ env (a, b, n) input h_input
    ha_norm hb_norm hn_norm hq_norm hr_norm h_eq_impl'

/-- **Loose completeness core.** Like `mulMod_completeness_core` but drops the
`b < n` requirement (bounding the honest quotient `q = a·b/n < 2^(B·m)` from
`a < n` and `b < 2^(B·m)`) and omits the `LessThan` obligation. -/
lemma mulMod_completeness_core_loose {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_lt : BigInt.value B input.1 < BigInt.value B input.2.2)
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        ((∀ k : Fin (2 * m - 1),
                (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
              ∀ k : Fin (2 * m - 1),
                (Expression.eval env
                  (if h : k.val < m then
                    (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                      var { index := i₀ + m + k.val }
                  else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
            polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
              polyValue B
                (Vector.map (Expression.eval env)
                  (Vector.mapFinRange (2 * m - 1) fun k ↦
                    if h : k.val < m then
                      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                        var { index := i₀ + m + k.val }
                    else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])) := by
  set a := BigInt.value B input.1 with ha_def
  set b := BigInt.value B input.2.1 with hb_def
  set n := BigInt.value B input.2.2 with hn_def
  set qval := a * b / n with hqval_def
  set rval := a * b % n with hrval_def
  have hmap_a : BigInt.value B (Vector.map (Expression.eval env) input_var.1) = a := by
    rw [ha_def, ← h_input]
  have hmap_b : BigInt.value B (Vector.map (Expression.eval env) input_var.2.1) = b := by
    rw [hb_def, ← h_input]
  have hmap_n : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = n := by
    rw [hn_def, ← h_input]
  -- n and b are bounded by 2^(B*m)
  have hn_lt : n < 2 ^ (B * m) := BigInt.value_lt hn_norm
  have hb_lt_M : b < 2 ^ (B * m) := BigInt.value_lt hb_norm
  -- q = a*b/n < 2^(B*m)  (from a < n and b < 2^(B*m))
  have hqval_lt : qval < 2 ^ (B * m) := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · rw [hb0, Nat.mul_zero]; exact Nat.mul_pos hn_pos (Nat.two_pow_pos (B * m))
    · calc a * b < n * b := (Nat.mul_lt_mul_right hb0).mpr hab_lt
        _ ≤ n * 2 ^ (B * m) := by apply Nat.mul_le_mul_left; omega
  have hrval_lt : rval < 2 ^ (B * m) := lt_trans (Nat.mod_lt _ hn_pos) hn_lt
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hrv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) = rval :=
    BigInt.value_mapRange (i₀ + m) rval env hB hrval_lt (by intro i; rw [hrwit i])
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  have hrv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) :=
    normalized_mapRange (i₀ + m) rval env hB (by intro i; rw [hrwit i])
  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt' : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env (Vector.mapRange m fun j ↦ var (F := F p) { index := i₀ + j })[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hrv_norm ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])
      = sVec (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) := rfl
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = a * b := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, hmap_a, hmap_b]
  have hSplit := polyValue_sVec_split (B := B) env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
    input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
        input_var.2.2 k hqd_lt hn_lt' hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env)
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2))
      = qval * n := by
    rw [polyValue_Sqn_eq env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 hqd_lt hn_lt' hfield,
      hqv_val, hmap_n]
  have hpolyS : polyValue B (Vector.map (Expression.eval env)
      (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))
      = a * b := by
    rw [hS_eq, hSplit, hSqn, hrv_val, hqval_def, hrval_def, Nat.div_add_mod']
  refine ⟨hqv_norm, hrv_norm, ⟨?_, ?_⟩, ?_⟩
  · intro k; exact coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield
  · intro k
    have hb := coeff_S_bound env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) k
      hqd_lt hn_lt' hrd_lt hfield
    rw [sVec, Vector.getElem_mapFinRange] at hb
    exact hb
  · rw [hP, hpolyS]

/-- **Loose witnessed-product completeness core.** Bridges `witnessedMul` outputs to
`mulMod_completeness_core_loose`. -/
lemma mulMod_completeness_core_wm_loose {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_lt : BigInt.value B input.1 < BigInt.value B input.2.2)
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        (((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
            (∀ k : Fin (2 * m - 1),
              (Expression.eval env
                (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
                < (m + 1) * 2 ^ (2 * B))) ∧
            polyValue B (Vector.map (Expression.eval env) Pv) =
              polyValue B (Vector.map (Expression.eval env)
                (Vector.mapFinRange (2 * m - 1) fun k ↦
                  if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val]))) := by
  obtain ⟨hqn, hrn, hconj⟩ :=
    mulMod_completeness_core_loose (B := B) hB hp i₀ env (a, b, n) input h_input
      ha_norm hb_norm hn_norm hab_lt hn_pos hqwit hrwit
  exact ⟨hqn, hrn,
    eqConj_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b) Qv
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
      heqAB_get heqQN_get hconj⟩

end

end MulMod

end Solution.Secp256k1ScalarMul
