import Solution.Secp256k1ScalarMulFixedBase.Normalize
import Solution.Secp256k1ScalarMulFixedBase.Equal

/-!
# RSA big-integer comparison (gadget G2)

This file defines `LessThan` (gadget **G2**): a `FormalAssertion` over a
pair of *normalized* big integers `(lhs, rhs)` asserting `lhs.value B < rhs.value B`.

## Strategy (borrow / carry chain)

We witness a `BigInt m` value `d` that should equal `rhs − 1 − lhs`, range-check it
to be normalized, and then certify the big-integer identity

```
lhs + d + 1 = rhs
```

limb-wise with a per-limb carry recurrence and a forced-zero top carry. Together
with `d` being normalized this yields `lhs ≤ rhs − 1 < rhs`, i.e.
`lhs.value B < rhs.value B`.

The "`+ 1`" is folded into the constant term of limb `0` so that every per-limb
constraint stays a degree-≤1 (linear) `assertZero`.

Soundness and completeness are fully proved.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-! ## G2 — `LessThan` -/

namespace LessThan

/-- Inputs of `LessThan`: `lhs` and `rhs`, asserting `lhs.value < rhs.value`. -/
structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

/-- Natural-number value of a witnessed limb vector under a prover environment,
little-endian base `2^B`. Used only inside witness generators. -/
private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMulFixedBase.Limbs.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

/-- The `main` circuit of `LessThan`: assert two normalized big integers satisfy
`lhs.value B < rhs.value B`.

We witness `d = rhs − 1 − lhs` (its limbs), range-check `d` to be normalized,
witness one carry bit per limb, and assert the limb-wise identity
`lhs + d + 1 = rhs` with the top carry forced to `0`. -/
def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let a := input.lhs
  let b := input.rhs

  -- 1. witness the limbs of `d = b − 1 − a`
  let d ← ProvableType.witness (α := BigInt m) fun env =>
    let dval : ℕ := evalValue P.B env b - 1 - evalValue P.B env a
    Vector.ofFn fun k : Fin m => ((dval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  -- 2. range-check `d` to be normalized (subcircuit call)
  Normalize.circuit P d

  -- 3. witness one carry (borrow) bit per limb. The carry *out* of limb `k`
  -- for the base-`2^B` addition `a + d + 1` is the running carry, which can be
  -- read off as `⌊P_k / 2^(B·(k+1))⌋` where `P_k = 1 + Σ_{j≤k} (a[j]+d[j])·2^(B·j)`
  -- is the partial sum through limb `k`.
  let carry ← witnessVector m fun env =>
    let av : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env.toEnvironment a[j]).val else 0
    let dv : ℕ → ℕ := fun j => if h : j < m then (Expression.eval env.toEnvironment d[j]).val else 0
    Vector.ofFn fun k : Fin m =>
      (((1 + ∑ j ∈ Finset.range (k.val + 1), (av j + dv j) * 2 ^ (P.B * j))
          / 2 ^ (P.B * (k.val + 1)) : ℕ) : F p)

  -- boolean-constrain each carry bit
  Circuit.forEach carry (fun c => assertZero (c * (c - 1)))

  -- 4. per-limb recurrence `a[k] + d[k] + carry_in + [k=0] = b[k] + carry[k]·2^B`
  -- where `carry_in = carry[k-1]` (0 for `k = 0`), and the `+1` is folded into
  -- limb 0's constant term. We build the per-limb constraint expressions purely,
  -- then assert each is zero.
  let constraints : Vector (Expression (F p)) m := Vector.mapFinRange m fun k =>
    let carryIn : Expression (F p) :=
      if h : k.val = 0 then 0 else carry[k.val - 1]'(by omega)
    let one : Expression (F p) := if k.val = 0 then 1 else 0
    a[k.val] + d[k.val] + carryIn + one - b[k.val] - carry[k.val] * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

  -- 5. force the top carry to zero
  if h : m = 0 then pure () else
    assertZero (carry[m - 1]'(by omega))

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P) where
  -- d : m witnesses; Normalize : m*B; carry bits : m
  localLength _ := m + m * P.B + m
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]

/-- Preconditions: both big integers are normalized. -/
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B

/-- Postcondition: `lhs.value B < rhs.value B`. -/
def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B < input.rhs.value B

/-- The `LessThan` formal assertion (gadget **G2**): two normalized big integers
satisfy `lhs.value B < rhs.value B`. -/
def circuit (P : BigIntParams p m) [Fact (p > 2)] :
    FormalAssertion (F p) (Inputs m) where
    main := main P
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
        Gadgets.ToBits.rangeCheck] at h_holds ⊢
      obtain ⟨h_dnorm, h_cbool, h_lin, h_top⟩ := h_holds
      obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
      refine ⟨?_, by split <;> simp [circuit_norm]⟩
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- m = 0 is excluded by `[NeZero m]` (the gadget is only meaningful, and only
        -- sound, for at least one limb).
        exact absurd hm (NeZero.ne m)
      -- m ≥ 1: borrow/carry chain argument.
      -- Nat-indexed digit/carry functions.
      set An : ℕ → ℕ := fun k => if h : k < m then (input.lhs[k]'h).val else 0 with hAn
      set Dn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hDn
      set Bn : ℕ → ℕ := fun k => if h : k < m then (input.rhs[k]'h).val else 0 with hBn
      set Cn : ℕ → ℕ := fun k => (env.get (i₀ + m + m * B + k)).val with hCn
      -- digit bounds
      have hAn_lt : ∀ k, k < m → An k < 2 ^ B := by
        intro k hk; simp only [hAn, dif_pos hk]; exact ha_norm ⟨k, hk⟩
      have hBn_lt : ∀ k, k < m → Bn k < 2 ^ B := by
        intro k hk; simp only [hBn, dif_pos hk]; exact hb_norm ⟨k, hk⟩
      have hDn_lt : ∀ k, k < m → Dn k < 2 ^ B := by
        intro k hk
        have hspec := h_dnorm trivial ⟨k, hk⟩
        have heq : (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i => var { index := i₀ + i }))[(⟨k, hk⟩ : Fin m)]
            = env.get (i₀ + k) := by simp [circuit_norm]
        rw [heq] at hspec
        simpa [hDn] using hspec
      -- carry bits
      have hCn_le : ∀ k, k < m → Cn k ≤ 1 := by
        intro k hk
        have hb := h_cbool ⟨k, hk⟩
        have : IsBool (env.get (i₀ + m + m * B + k)) := by
          rw [IsBool.iff_mul_sub_one]; rw [show env.get (i₀ + m + m * B + k) - 1
            = env.get (i₀ + m + m * B + k) + -1 by ring]; exact hb
        have := IsBool.val_lt_two this
        simp only [hCn]; omega
      -- 2^(B+1) < p
      have hPB1 : 2 ^ (B + 1) < p := by
        have h1 : 2 ^ (B + 1) ≤ 2 ^ (2 * B + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ (2 * B + 2) = 2 ^ (2 * B) * 4 := by rw [pow_add]; ring
        have h3 : 2 ^ (2 * B) * 4 ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
          have : 1 ≤ m + 1 := by omega
          nlinarith [Nat.two_pow_pos (2 * B)]
        omega
      -- per-limb nat equation: An k + Dn k + cin k + one k = Bn k + Cn k * 2^B
      have h_limb : ∀ k : ℕ, (hk : k < m) →
          An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)
            = Bn k + Cn k * 2 ^ B := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩
        -- evaluate the three "eval" subterms
        have ha_e : Expression.eval env input_var.lhs[(⟨k, hk⟩ : Fin m).val] = input.lhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var.rhs[(⟨k, hk⟩ : Fin m).val] = input.rhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin m).val = 0 then 0
              else var { index := i₀ + m + m * B + ((⟨k, hk⟩ : Fin m).val - 1) })
            = if k = 0 then 0 else env.get (i₀ + m + m * B + (k - 1)) := by
          simp only []
          split <;> simp [circuit_norm]
        have hone_e : Expression.eval env (if (⟨k, hk⟩ : Fin m).val = 0 then 1 else 0)
            = if k = 0 then (1 : F p) else 0 := by
          simp only []; split <;> simp [circuit_norm]
        simp only [ha_e, hb_e, hcin_e, hone_e] at hlin
        -- bounds for the lift lemma
        have h3 : (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val ≤ 1 := by
          split
          · simp [ZMod.val_zero]
          · rename_i h
            have hkm : k - 1 < m := by omega
            have := hCn_le (k - 1) hkm
            simp only [hCn] at this; exact this
        have h4 : (if k = 0 then (1 : F p) else 0).val ≤ 1 := by
          split
          · simp [ZMod.val_one]
          · simp [ZMod.val_zero]
        have hpw : 2 ^ B + 2 ^ B = 2 ^ (B + 1) := by rw [pow_succ]; ring
        have hsum_lt : (input.lhs[k]'hk).val + (env.get (i₀ + k)).val
            + (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val
            + (if k = 0 then (1 : F p) else 0).val < p := by
          have h1 := hAn_lt k hk; have h2 := hDn_lt k hk
          simp only [hAn, hDn, dif_pos hk] at h1 h2
          omega
        have hrhs_lt : (input.rhs[k]'hk).val
            + (env.get (i₀ + m + m * B + k)).val * 2 ^ B < p := by
          have h1 := hBn_lt k hk; have h2 := hCn_le k hk
          simp only [hBn, hCn, dif_pos hk] at h1 h2
          nlinarith [Nat.two_pow_pos B]
        have hlin' : (input.lhs[k]'hk) + env.get (i₀ + k)
            + (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1)))
            + (if k = 0 then (1 : F p) else 0) - (input.rhs[k]'hk)
            - env.get (i₀ + m + m * B + k) * (2 ^ B : F p) = 0 := by
          rw [sub_eq_add_neg, sub_eq_add_neg]; exact hlin
        have hlift := per_limb_lift (B := B) (input.lhs[k]'hk) (env.get (i₀ + k))
          (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1)))
          (if k = 0 then (1 : F p) else 0) (input.rhs[k]'hk)
          (env.get (i₀ + m + m * B + k)) hB hsum_lt hrhs_lt hlin'
        -- rewrite the `.val`s of the carry/one terms
        have hcin_val : (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val
            = if k = 0 then 0 else Cn (k - 1) := by
          split <;> simp [hCn]
        have hone_val : (if k = 0 then (1 : F p) else 0).val = if k = 0 then 1 else 0 := by
          split
          · simp [ZMod.val_one]
          · simp [ZMod.val_zero]
        rw [hcin_val, hone_val] at hlift
        simp only [hAn, hDn, hBn, hCn, dif_pos hk]
        omega
      -- top carry is zero
      have htop0 : Cn (m - 1) = 0 := by
        have hne : ¬ (m = 0) := by omega
        simp only [dif_neg hne, circuit_norm] at h_top
        simp only [hCn, h_top, ZMod.val_zero]
      -- value as range sums of the digit functions
      have hval_a : BigInt.value B input.lhs = ∑ k ∈ Finset.range m, An k * 2 ^ (B * k) := by
        rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => An k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
      have hval_b : BigInt.value B input.rhs = ∑ k ∈ Finset.range m, Bn k * 2 ^ (B * k) := by
        rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => Bn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
      -- sum the per-limb equations over range m
      have hsum_eq : (∑ k ∈ Finset.range m,
            ((An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)) * 2 ^ (B * k)))
          = ∑ k ∈ Finset.range m, ((Bn k + Cn k * 2 ^ B) * 2 ^ (B * k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [h_limb k hk]
      -- distribute LHS
      have hLHS : (∑ k ∈ Finset.range m,
            (An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)) * 2 ^ (B * k))
          = (∑ k ∈ Finset.range m, An k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, Dn k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, (if k = 0 then 1 else 0) * 2 ^ (B * k)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring
      have hRHS : (∑ k ∈ Finset.range m, (Bn k + Cn k * 2 ^ B) * 2 ^ (B * k))
          = (∑ k ∈ Finset.range m, Bn k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, Cn k * 2 ^ (B * (k + 1))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]; ring
      -- the "one" sum equals 1 (only k=0 contributes)
      have hone_sum : (∑ k ∈ Finset.range m, (if k = 0 then 1 else 0) * 2 ^ (B * k)) = 1 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro k _ hk0; simp [hk0]
        · intro h; exact absurd (Finset.mem_range.mpr hm) h
      -- carry telescoping
      have htel := carry_telescope B Cn m
      rw [if_neg (by omega : ¬ (m = 0)), htop0, Nat.zero_mul, Nat.add_zero] at htel
      -- combine
      rw [hLHS, hRHS, hone_sum, htel] at hsum_eq
      -- now hsum_eq : value_a-sum + value_d-sum + carry-sum + 1 = value_b-sum + carry-sum
      rw [hval_a, hval_b]
      -- value_d-sum ≥ 0, cancel the carry sums
      have hd_nonneg : 0 ≤ ∑ k ∈ Finset.range m, Dn k * 2 ^ (B * k) := Nat.zero_le _
      omega
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
        Gadgets.ToBits.rangeCheck] at h_env ⊢
      obtain ⟨h_dwit, h_cwit, _, _⟩ := h_env
      obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
      -- nat-indexed digit functions
      set An : ℕ → ℕ := fun k => if h : k < m then (input.lhs[k]'h).val else 0 with hAn
      set Bn : ℕ → ℕ := fun k => if h : k < m then (input.rhs[k]'h).val else 0 with hBn
      -- the witnessed d-limb value at index i
      have hd_val : ∀ i : Fin m, (env.get (i₀ + i.val)).val
          = (evalValue B env input_var.rhs - 1 - evalValue B env input_var.lhs)
              / 2 ^ (B * i.val) % 2 ^ B := by
        intro i
        rw [h_dwit i]
        simp only [Vector.getElem_ofFn]
        rw [ZMod.val_natCast_of_lt]
        exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB)
      -- evalValue equals the denotation of the inputs
      have heva : evalValue B env input_var.lhs = BigInt.value B input.lhs := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.rhs = BigInt.value B input.rhs := by
        rw [evalValue, BigInt.value, ← h_input]
      -- abbreviations for the two denotations
      set va := BigInt.value B input.lhs with hva
      set vb := BigInt.value B input.rhs with hvb
      -- the witnessed d value (as a natural number, before per-limb split)
      set dtot : ℕ := vb - 1 - va with hdtot
      -- bounds: va, vb < 2^(B*m)
      have hva_lt : va < 2 ^ (B * m) := BigInt.value_lt ha_norm
      have hvb_lt : vb < 2 ^ (B * m) := BigInt.value_lt hb_norm
      -- d limb value
      have hd_val' : ∀ i : Fin m, (env.get (i₀ + i.val)).val = dtot / 2 ^ (B * i.val) % 2 ^ B := by
        intro i; rw [hd_val i, heva, hevb]
      -- nat-indexed d digits
      set Dn : ℕ → ℕ := fun k => if h : k < m then (env.get (i₀ + k)).val else 0 with hDn
      have hDn_eq : ∀ k, k < m → Dn k = dtot / 2 ^ (B * k) % 2 ^ B := by
        intro k hk; simp only [hDn, dif_pos hk]; exact hd_val' ⟨k, hk⟩
      have hDn_lt : ∀ k, k < m → Dn k < 2 ^ B := by
        intro k hk; rw [hDn_eq k hk]; exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_refl _)
      have hAn_lt : ∀ k, k < m → An k < 2 ^ B := fun k hk => by
        simp only [hAn, dif_pos hk]; exact ha_norm ⟨k, hk⟩
      have hBn_lt : ∀ k, k < m → Bn k < 2 ^ B := fun k hk => by
        simp only [hBn, dif_pos hk]; exact hb_norm ⟨k, hk⟩
      -- digit sum function and partial sums
      set gfun : ℕ → ℕ := fun k => An k + Dn k with hgfun
      have hgfun_le : ∀ j, gfun j ≤ 2 * (2 ^ B - 1) := by
        intro j
        rcases Nat.lt_or_ge j m with hj | hj
        · have := hAn_lt j hj; have := hDn_lt j hj; simp only [hgfun]; omega
        · simp only [hgfun, hAn, hDn, dif_neg (by omega : ¬ j < m)]; omega
      set P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), gfun j * 2 ^ (B * j) with hP
      -- dtot < 2^(B*m), value of d, and the additive identity
      have hdtot_lt : dtot < 2 ^ (B * m) := by rw [hdtot]; omega
      have hadd : va + dtot + 1 = vb := by rw [hdtot]; omega
      -- value of witnessed d equals dtot
      have hvd : BigInt.value B (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange m fun i => var { index := i₀ + i })) = dtot := by
        rw [BigInt.value_eq_sum]
        have hstep : (∑ k : Fin m, ((Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun i => var { index := i₀ + i }))[k]).val * 2 ^ (B * k.val))
            = ∑ k ∈ Finset.range m, (dtot / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k) := by
          rw [← Fin.sum_univ_eq_sum_range (fun k => (dtot / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _
          have : (Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
            simp [circuit_norm]
          rw [this, hd_val' i]
        rw [hstep, limb_decomp_mod, Nat.mod_eq_of_lt hdtot_lt]
      -- the carry witness equals the partial-sum carry P k / 2^(B*(k+1))
      have hCn_eq : ∀ k : ℕ, k < m →
          (env.get (i₀ + m + m * B + k)).val = P k / 2 ^ (B * (k + 1)) := by
        intro k hk
        -- the raw witness expression equals P k / 2^(B*(k+1))
        have hraw : (1 + ∑ x ∈ Finset.range (k + 1),
            ((if h : x < m then (Expression.eval env.toEnvironment input_var.lhs[x]).val else 0) +
              (if h : x < m then (env.get (i₀ + x)).val else 0)) * 2 ^ (B * x)) / 2 ^ (B * (k + 1))
            = P k / 2 ^ (B * (k + 1)) := by
          congr 1
          simp only [hP]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          have hjm : j < m := by omega
          congr 1
          simp only [hgfun, hAn, hDn, dif_pos hjm]
          congr 1
          rw [← h_input]; simp [Vector.getElem_map]
        rw [h_cwit ⟨k, hk⟩]
        simp only [Vector.getElem_ofFn]
        rw [ZMod.val_natCast_of_lt, hraw]
        rw [hraw]
        have hbit : P k / 2 ^ (B * (k + 1)) ≤ 1 := (ripple_carry B gfun hgfun_le k).2
        have := hB; have := Nat.two_pow_pos B; omega
      -- m > 0 (else va = vb = 0, contradicting h_spec)
      have hm : 0 < m := by
        by_contra h
        have hm0 : m = 0 := by omega
        have h1 : va < 2 ^ (B * m) := hva_lt
        have h2 : vb < 2 ^ (B * m) := hvb_lt
        rw [hm0, Nat.mul_zero, pow_zero] at h1 h2
        omega
      -- An, Dn digit sums
      have hsum_an : (∑ j ∈ Finset.range m, An j * 2 ^ (B * j)) = va := by
        rw [hva, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => An j * 2 ^ (B * j))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
      have hsum_dn : (∑ j ∈ Finset.range m, Dn j * 2 ^ (B * j)) = dtot := by
        rw [← hvd, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Dn j * 2 ^ (B * j))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hDn, dif_pos i.isLt]
        congr 1
        have : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
          simp [circuit_norm]
        rw [this]
      -- P (m-1) = vb
      have hPlast : P (m - 1) = vb := by
        simp only [hP]
        rw [show m - 1 + 1 = m by omega]
        simp only [hgfun]
        rw [show (∑ j ∈ Finset.range m, (An j + Dn j) * 2 ^ (B * j))
            = (∑ j ∈ Finset.range m, An j * 2 ^ (B * j))
              + (∑ j ∈ Finset.range m, Dn j * 2 ^ (B * j)) by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring]
        rw [hsum_an, hsum_dn]; omega
      -- Bn k = the k-th extracted digit of vb
      have hBn_eq : ∀ k, k < m → Bn k = vb / 2 ^ (B * k) % 2 ^ B := by
        intro k hk
        have hvb_sum : vb = ∑ j ∈ Finset.range m, Bn j * 2 ^ (B * j) := by
          rw [hvb, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Bn j * 2 ^ (B * j))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
        rw [hvb_sum]
        exact (digit_extract B Bn (fun j => by
          rcases Nat.lt_or_ge j m with hj | hj
          · exact hBn_lt j hj
          · simp only [hBn, dif_neg (by omega : ¬ j < m)]; exact Nat.two_pow_pos B) m k hk).symm
      -- carry field value is a bit (0 or 1)
      have hCn_bit : ∀ k : ℕ, k < m → IsBool (env.get (i₀ + m + m * B + k)) := by
        intro k hk
        have hle : (env.get (i₀ + m + m * B + k)).val ≤ 1 := by
          rw [hCn_eq k hk]; exact (ripple_carry B gfun hgfun_le k).2
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · left; exact (ZMod.val_eq_zero _).mp h0
        · right
          have : env.get (i₀ + m + m * B + k) = ((1 : ℕ) : F p) := by
            rw [← h1, ZMod.natCast_zmod_val]
          simpa using this
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- 1. d is normalized (Normalize subcircuit obligation)
        refine ⟨trivial, ?_⟩
        intro i
        have : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
          simp [circuit_norm]
        rw [this]
        have := hDn_lt i.val i.isLt
        simp only [hDn, dif_pos i.isLt] at this
        exact this
      · -- 2. carry booleans
        intro i
        have hbit := hCn_bit i.val i.isLt
        rw [show env.get (i₀ + m + m * B + i.val) + -1
          = env.get (i₀ + m + m * B + i.val) - 1 by ring]
        exact (IsBool.iff_mul_sub_one).mp hbit
      · -- 3. per-limb field equation
        set Cn : ℕ → ℕ := fun k => (env.get (i₀ + m + m * B + k)).val with hCn
        have hCnP : ∀ k, k < m → Cn k = P k / 2 ^ (B * (k + 1)) := fun k hk => hCn_eq k hk
        -- the ℕ-level per-limb recurrence
        have hnat : ∀ k, k < m →
            An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)
              = Bn k + Cn k * 2 ^ B := by
          intro k hk
          have hre : gfun k + (if k = 0 then 1 else P (k - 1) / 2 ^ (B * k))
              = (P k / 2 ^ (B * k)) % 2 ^ B + (P k / 2 ^ (B * (k + 1))) * 2 ^ B := ripple_eq B gfun k
          -- limb_stable: (P k / 2^(B*k)) % 2^B = (P (m-1) / 2^(B*k)) % 2^B = vb/2^(B*k)%2^B = Bn k
          have hlimb : (P k / 2 ^ (B * k)) % 2 ^ B = Bn k := by
            have h1 : P (m - 1) / 2 ^ (B * k) % 2 ^ B = P k / 2 ^ (B * k) % 2 ^ B :=
              limb_stable B gfun k (m - 1) (by omega)
            rw [hBn_eq k hk, ← hPlast, ← h1]
          -- carry-out and carry-in in terms of Cn
          have hco : P k / 2 ^ (B * (k + 1)) = Cn k := (hCnP k hk).symm
          rw [hlimb, hco] at hre
          simp only [hgfun] at hre
          -- handle the carry-in
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            simp only [↓reduceIte] at hre ⊢
            omega
          · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)]
            have hcin : P (k - 1) / 2 ^ (B * k) = Cn (k - 1) := by
              rw [hCnP (k - 1) (by omega), show k - 1 + 1 = k from by omega]
            rw [if_neg (by omega : ¬ k = 0), hcin] at hre
            omega
        -- cast each per-limb ℕ equation to F p
        intro i
        have hk := i.isLt
        have hnatk := hnat i.val hk
        -- evaluate the symbolic subterms
        have ha_e : Expression.eval env.toEnvironment input_var.lhs[i.val] = input.lhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var.rhs[i.val] = input.rhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0 else var { index := i₀ + m + m * B + (i.val - 1) })
            = if i.val = 0 then 0 else env.get (i₀ + m + m * B + (i.val - 1)) := by
          split <;> simp [circuit_norm]
        have hone_e : Expression.eval env.toEnvironment (if i.val = 0 then 1 else 0)
            = if i.val = 0 then (1 : F p) else 0 := by split <;> simp [circuit_norm]
        rw [ha_e, hb_e, hcin_e, hone_e]
        -- val-cast facts
        have hAk : ((An i.val : ℕ) : F p) = (input.lhs[i.val]'hk) := by
          simp only [hAn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hDk : ((Dn i.val : ℕ) : F p) = env.get (i₀ + i.val) := by
          simp only [hDn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Bn i.val : ℕ) : F p) = (input.rhs[i.val]'hk) := by
          simp only [hBn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hCk : ((Cn i.val : ℕ) : F p) = env.get (i₀ + m + m * B + i.val) := by
          simp only [hCn]; rw [ZMod.natCast_zmod_val]
        -- turn the goal into a cast of the ℕ equation
        have hcast_eq : (input.lhs[i.val]'hk) + env.get (i₀ + i.val)
            + (if i.val = 0 then (0:F p) else env.get (i₀ + m + m * B + (i.val - 1)))
            + (if i.val = 0 then (1 : F p) else 0)
            = (input.rhs[i.val]'hk) + env.get (i₀ + m + m * B + i.val) * (2 ^ B : F p) := by
          have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
          push_cast at hcast
          rw [hAk, hDk, hBk, hCk] at hcast
          -- rewrite the conditional casts
          rw [show ((if i.val = 0 then (0:F p) else env.get (i₀ + m + m * B + (i.val - 1))))
                = ((if i.val = 0 then (0:ℕ) else Cn (i.val - 1) : ℕ) : F p) by
              split
              · simp
              · simp only [hCn]; rw [ZMod.natCast_zmod_val],
            show ((if i.val = 0 then (1:F p) else 0))
                = ((if i.val = 0 then (1:ℕ) else 0 : ℕ) : F p) by split <;> simp]
          push_cast
          convert hcast using 2
        rw [hcast_eq]; ring
      · -- 4. top carry is zero
        have hne : ¬ (m = 0) := by omega
        simp only [dif_neg hne, circuit_norm]
        -- need env.get (i₀+m+m*B+(m-1)) = 0
        have hval0 : (env.get (i₀ + m + m * B + (m - 1))).val = 0 := by
          rw [hCn_eq (m - 1) (by omega)]
          have : P (m - 1) / 2 ^ (B * (m - 1 + 1)) = vb / 2 ^ (B * m) := by
            rw [hPlast, show m - 1 + 1 = m from by omega]
          rw [this, Nat.div_eq_of_lt hvb_lt]
        exact (ZMod.val_eq_zero _).mp hval0

end LessThan

end

end Solution.Secp256k1ScalarMulFixedBase
