import Solution.Secp256k1ScalarMul.Normalize
import Solution.Secp256k1ScalarMul.Equal

/-!
# RSA big-integer multiplication (gadget G4)

This file defines `EqViaCarries` (gadget **G4**): a `FormalAssertion` that,
given two coefficient sequences `lhs` and `rhs` (each `2m − 1` field expressions),
certifies that the natural numbers they encode in base `2^B` are equal, via a
witnessed carry chain (no division).

The pure helper `bigIntMulNoReduce` (gadget **G3**, the schoolbook convolution
`P_k = Σ_{i+j=k} a[i]·b[j]`), the base-`2^B` value `polyValue`, the carry-witness
helpers (`evalPartial`, `carryOffset`) and all supporting lemmas live in
`Circuits.RSA.Theorems`.

Soundness and completeness are fully proved.
-/

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-! ## G4 — `EqViaCarries`

Certify `Σ_k lhs[k]·X^k = Σ_k rhs[k]·X^k` with `X = 2^B`, by witnessing a carry
chain and asserting per-index linear equations.
-/

namespace EqViaCarries

/-- The coefficient-sequence type for `EqViaCarries`: `2m − 1` field elements.

A reducible alias for `fields (2 * m - 1)`. The `ProvableStruct` deriving handler
cannot parse the size expression `2 * m - 1` inline as a `Vector _ _` field, so we
wrap it in a single-atom `TypeMap`; being `@[reducible]` it still unfolds to
`fields` under `circuit_norm` so the usual `← h_input` reduction idiom applies. -/
@[reducible] def Coeffs (m : ℕ) : TypeMap := fields (2 * m - 1)

/-- Inputs of `EqViaCarries`: the two coefficient sequences `lhs` and `rhs`,
each `2m − 1` field elements. -/
structure Inputs (m : ℕ) (F : Type) where
  lhs : Coeffs m F
  rhs : Coeffs m F
deriving ProvableStruct

/-- The `main` circuit of `EqViaCarries`: certify that two coefficient sequences
`lhs := input.lhs` and `rhs := input.rhs` encode the same natural number in base
`2^B`.

We witness an offset running carry `carry[k]` per index (the signed carry *out* of
index `k`, shifted by `OFF = carryOffset B`), range-check each carry to `W` bits,
assert the per-index linear relation
`lhs[k] + (carry_in − OFF) − rhs[k] − (carry[k] − OFF)·2^B = 0` (with effective
`carry_in − OFF = 0` at `k = 0`, `carry_in = carry[k−1]` otherwise), and force the
top carry to `OFF` (signed top carry `0`).

`W` is the carry bit-width, passed with the field-size hypothesis `hW : 2^W < p`,
the offset-fits hypothesis `hWB : 2·OFF ≤ 2^W`, and the lift hypothesis
`hWp : 3·(m+1)·2^(2B) + 2^W·2^B + 2^W < p` (bounding all per-index sums). -/
def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs

  -- 1. witness the running (offset) carries c[0 .. 2m-2] (carry out of each index).
  let carry ← witnessVector (2 * m - 1) fun env =>
    Vector.ofFn fun k : Fin (2 * m - 1) =>
      -- offset running carry out of index k:
      --   OFF + (Σ_{j ≤ k} P[j]·2^(B·j) − Σ_{j ≤ k} S[j]·2^(B·j)) / 2^(B*(k+1))
      ((carryOffset (m := m) P.B + evalPartial P.B env Pc k.val / 2 ^ (P.B * (k.val + 1))
          - evalPartial P.B env Sc k.val / 2 ^ (P.B * (k.val + 1)) : ℕ) : F p)

  -- 2. range-check each carry to `W` bits (subcircuit call).
  Circuit.forEach carry (fun c => Gadgets.ToBits.rangeCheck P.W P.hW c)

  -- 3. per-index linear constraint (signed carries via the offset convention)
  --    `lhs[k] + (carry[k-1] − OFF) − rhs[k] − (carry[k] − OFF)·2^B = 0`,
  --    with effective `carry_in = 0` for `k = 0`. Built purely, then asserted.
  let constraints : Vector (Expression (F p)) (2 * m - 1) :=
    Vector.mapFinRange (2 * m - 1) fun k =>
      let carryIn : Expression (F p) :=
        if h : k.val = 0 then 0 else carry[k.val - 1]'(by omega) - (carryOffset (m := m) P.B : F p)
      Pc[k.val] + carryIn - Sc[k.val]
        - (carry[k.val] - (carryOffset (m := m) P.B : F p)) * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

  -- 4. force the top (offset) carry to OFF, i.e. signed top carry to zero.
  if h : 2 * m - 1 = 0 then pure () else
    assertZero (carry[2 * m - 1 - 1]'(by omega) - (carryOffset (m := m) P.B : F p))

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P) where
  -- carries: (2m-1) witnesses + (2m-1) * W range-check bits
  localLength _ := (2 * m - 1) * P.W + (2 * m - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]

/-- Preconditions: both coefficient sequences are bounded by `(m+1)·2^(2B)`. -/
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  (∀ k : Fin (2 * m - 1), (input.lhs[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
  (∀ k : Fin (2 * m - 1), (input.rhs[k.val]).val < (m + 1) * 2 ^ (2 * B))

/-- Postcondition: the two coefficient sequences encode the same base-`2^B` value. -/
def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  polyValue B input.lhs = polyValue B input.rhs

/-- The `EqViaCarries` formal assertion (gadget **G4**): two coefficient sequences
encode the same natural number in base `2^B`. -/
def circuit (P : BigIntParams p m) [Fact (p > 2)] : FormalAssertion (F p) (Inputs m) where
    main := main P
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_holds ⊢
      obtain ⟨h_range, h_lin, h_top⟩ := h_holds
      refine ⟨?_, by split <;> simp [circuit_norm]⟩
      -- m ≥ 1 from NeZero, so 2m-1 ≥ 1
      have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
      set OFFn := carryOffset (m := m) B with hOFFn
      -- nat-indexed coefficient / carry functions
      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.rhs[k]'h).val else 0 with hSn
      set Cn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hCn
      -- bound facts
      have hCn_lt : ∀ k, k < 2 * m - 1 → Cn k < 2 ^ W := by
        intro k hk; simpa [hCn] using h_range ⟨k, hk⟩
      have hPn_lt : ∀ k, k < 2 * m - 1 → Pn k < (m + 1) * 2 ^ (2 * B) := by
        intro k hk; simp only [hPn, dif_pos hk]; exact h_assumptions.1 ⟨k, hk⟩
      have hSn_lt : ∀ k, k < 2 * m - 1 → Sn k < (m + 1) * 2 ^ (2 * B) := by
        intro k hk; simp only [hSn, dif_pos hk]; exact h_assumptions.2 ⟨k, hk⟩
      -- standing bounds on OFFn and 2^B
      -- key algebraic facts about OFFn = (m+1)*2^(B+1)
      have hOFF_eq : OFFn = (m + 1) * 2 ^ (B + 1) := rfl
      have hOFFB_eq : OFFn * 2 ^ B = (m + 1) * 2 ^ (2 * B + 1) := by
        rw [hOFF_eq, Nat.mul_assoc, ← pow_add]; congr 2; ring
      -- (m+1)*2^(2*B+1) ≤ (m+1)*2^(2*B)*3  and  OFFn ≤ (m+1)*2^(2*B)*3
      have hpow_le : (m + 1) * 2 ^ (2 * B + 1) ≤ (m + 1) * 2 ^ (2 * B) * 3 := by
        rw [pow_succ]; nlinarith [Nat.two_pow_pos (2 * B)]
      have hOFF_le3 : OFFn ≤ (m + 1) * 2 ^ (2 * B) * 3 := by
        rw [hOFF_eq]
        have h1 : (m + 1) * 2 ^ (B + 1) ≤ (m + 1) * 2 ^ (2 * B + 1) := by
          apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_right (by norm_num); omega
        omega
      have hOFFB_lt : OFFn * 2 ^ B < p := by rw [hOFFB_eq]; omega
      have hpB : 2 ^ B < p := by
        have : 2 ^ B ≤ 2 ^ W * 2 ^ B := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos W)
        omega
      have hOFFn_lt : OFFn < p := by omega
      have hOFFn_cast : (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt
      -- X := (m+1)*2^(2*B) ≤ 2^W * 2^B  (from the offset-fits hypothesis hWB)
      have hOFFn_le_W : OFFn ≤ 2 ^ W := by
        have : OFFn ≤ OFFn * 2 := Nat.le_mul_of_pos_right _ (by norm_num); omega
      have hXW : (m + 1) * 2 ^ (2 * B) ≤ 2 ^ W * 2 ^ B := by
        have h1 : (m + 1) * 2 ^ (B + 2) ≤ 2 ^ W := by
          have : OFFn * 2 = (m + 1) * 2 ^ (B + 2) := by rw [hOFF_eq, pow_succ]; ring
          omega
        calc (m + 1) * 2 ^ (2 * B) ≤ (m + 1) * 2 ^ (B + 2) * 2 ^ B := by
                rw [Nat.mul_assoc, ← pow_add]
                apply Nat.mul_le_mul_left
                apply Nat.pow_le_pow_right (by norm_num); omega
          _ ≤ 2 ^ W * 2 ^ B := Nat.mul_le_mul_right _ h1
      -- top carry equals OFFn
      rw [dif_neg (by omega : ¬ (2 * m - 1 = 0))] at h_top
      simp only [circuit_norm] at h_top
      have hCtop : Cn (2 * m - 1 - 1) = OFFn := by
        have : env.get (i₀ + (2 * m - 1 - 1)) = (OFFn : F p) := by
          rw [← sub_eq_zero]; rw [show env.get (i₀ + (2 * m - 1 - 1)) - (OFFn : F p)
            = env.get (i₀ + (2 * m - 1 - 1)) + -(OFFn : F p) by ring]; exact h_top
        simp only [hCn, this, hOFFn_cast]
      -- per-index nat equation (unified, effective carry-in OFFn at k=0)
      have h_idx : ∀ k, (hk : k < 2 * m - 1) →
          Pn k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B
            = Sn k + Cn k * 2 ^ B + OFFn := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩
        -- evaluate symbolic subterms
        have ha_e : Expression.eval env input_var.lhs[(⟨k, hk⟩ : Fin (2*m-1)).val] = input.lhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var.rhs[(⟨k, hk⟩ : Fin (2*m-1)).val] = input.rhs[k]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin (2*m-1)).val = 0 then 0
              else var { index := i₀ + ((⟨k, hk⟩ : Fin (2*m-1)).val - 1) } - Expression.const (OFFn : F p))
            = if k = 0 then 0 else env.get (i₀ + (k - 1)) - (OFFn : F p) := by
          simp only []
          split <;> simp [circuit_norm, sub_eq_add_neg]
        simp only [ha_e, hb_e, hcin_e] at hlin
        -- the unified field equation
        have hfield : (input.lhs[k]'hk) + (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1)))
            + (OFFn : F p) * (2 ^ B : F p)
            = (input.rhs[k]'hk) + env.get (i₀ + k) * (2 ^ B : F p) + (OFFn : F p) := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            simp only [↓reduceIte] at hlin ⊢
            rw [← sub_eq_zero]
            rw [← hlin]; ring
          · rw [if_neg (by omega : ¬ k = 0)] at hlin ⊢
            rw [← sub_eq_zero]
            rw [← hlin]; ring
        -- lift to ℕ
        have hcin_val : (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1))).val
            = if k = 0 then OFFn else Cn (k - 1) := by
          split
          · exact hOFFn_cast
          · simp [hCn]
        have hcinN_lt : (if k = 0 then OFFn else Cn (k - 1)) < p := by
          split
          · exact hOFFn_lt
          · rename_i hkne
            have := hCn_lt (k - 1) (by omega); omega
        have hcin_le : (if k = 0 then OFFn else Cn (k - 1)) ≤ 2 ^ W := by
          split
          · exact hOFFn_le_W
          · rename_i hkne; have := hCn_lt (k - 1) (by omega); omega
        have hlhs : (input.lhs[k]'hk).val + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B < p := by
          have hp1 := hPn_lt k hk
          simp only [hPn, dif_pos hk] at hp1
          omega
        have hrhs : (input.rhs[k]'hk).val + (env.get (i₀ + k)).val * 2 ^ B + OFFn < p := by
          have hp2 := hSn_lt k hk
          simp only [hSn, dif_pos hk] at hp2
          have hc : (env.get (i₀ + k)).val < 2 ^ W := h_range ⟨k, hk⟩
          have hcB : (env.get (i₀ + k)).val * 2 ^ B ≤ 2 ^ W * 2 ^ B := by
            apply Nat.mul_le_mul_right; omega
          omega
        have hlift := per_index_lift (B := B) (input.lhs[k]'hk)
          (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1)))
          (input.rhs[k]'hk) (env.get (i₀ + k)) (OFFn : F p)
          (if k = 0 then OFFn else Cn (k - 1)) OFFn hpB hcin_val hOFFn_cast hlhs hrhs hfield
        simp only [hPn, hSn, hCn, dif_pos hk] at hlift ⊢
        convert hlift using 2
      -- express polyValue as range sums of Pn / Sn
      have hpv1 : polyValue B input.lhs = ∑ k ∈ Finset.range (2 * m - 1), Pn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hPn, dif_pos i.isLt]
      have hpv2 : polyValue B input.rhs = ∑ k ∈ Finset.range (2 * m - 1), Sn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Sn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hSn, dif_pos i.isLt]
      rw [hpv1, hpv2]
      -- sum the per-index equations weighted by 2^(B*k)
      have hsum : (∑ k ∈ Finset.range (2 * m - 1),
            ((Pn k + (if k = 0 then OFFn else Cn (k - 1))) + OFFn * 2 ^ B) * 2 ^ (B * k))
          = ∑ k ∈ Finset.range (2 * m - 1),
            (Sn k + Cn k * 2 ^ B + OFFn) * 2 ^ (B * k) := by
        apply Finset.sum_congr rfl
        intro k hk; rw [Finset.mem_range] at hk; rw [h_idx k hk]
      -- distribute both sides into named pieces
      set SP := ∑ k ∈ Finset.range (2 * m - 1), Pn k * 2 ^ (B * k) with hSP
      set SS := ∑ k ∈ Finset.range (2 * m - 1), Sn k * 2 ^ (B * k) with hSS
      set SC := ∑ k ∈ Finset.range (2 * m - 1), Cn k * 2 ^ (B * (k + 1)) with hSC
      -- SCin' : effective carry-in sum (OFFn at index 0)
      set SCin' := ∑ k ∈ Finset.range (2 * m - 1),
        (if k = 0 then OFFn else Cn (k - 1)) * 2 ^ (B * k) with hSCin'
      -- SCin : telescoping carry-in sum (0 at index 0)
      set SCin := ∑ k ∈ Finset.range (2 * m - 1),
        (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * k) with hSCin
      set G := ∑ k ∈ Finset.range (2 * m - 1), 2 ^ (B * k) with hG
      -- SCin' = SCin + OFFn  (the index-0 term differs by OFFn·2^0)
      have hSCin_rel : SCin' = SCin + OFFn := by
        rw [hSCin', hSCin, show 2 * m - 1 = (2 * m - 2) + 1 from by omega]
        rw [Finset.sum_range_succ' _ (2 * m - 2), Finset.sum_range_succ' _ (2 * m - 2)]
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
          Nat.mul_zero, pow_zero, Nat.mul_one]
        ring
      -- LHS distribution
      have hLHS : (∑ k ∈ Finset.range (2 * m - 1),
            ((Pn k + (if k = 0 then OFFn else Cn (k - 1))) + OFFn * 2 ^ B) * 2 ^ (B * k))
          = SP + SCin' + OFFn * 2 ^ B * G := by
        rw [hSP, hSCin', hG, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring
      -- RHS distribution
      have hRHS : (∑ k ∈ Finset.range (2 * m - 1), (Sn k + Cn k * 2 ^ B + OFFn) * 2 ^ (B * k))
          = SS + SC + OFFn * G := by
        rw [hSS, hSC, hG, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]; ring
      rw [hLHS, hRHS] at hsum
      -- telescoping: SCin + OFFn*2^(B*(2m-1)) = SC, using top carry = OFFn
      have htel := carry_telescope B Cn (2 * m - 1)
      rw [if_neg (by omega : ¬ (2 * m - 1 = 0)), hCtop] at htel
      rw [← hSCin, ← hSC] at htel
      -- geometric identity: 2^B * G = G + Gtop - 1
      have hgeo := geom_shift B (2 * m - 1)
      rw [← hG] at hgeo
      set Gtop := 2 ^ (B * (2 * m - 1)) with hGtop
      have hGtop_pos : 1 ≤ Gtop := Nat.one_le_two_pow
      have hG_pos : 1 ≤ G := by
        rw [hG]
        calc 1 = 2 ^ (B * 0) := by simp
          _ ≤ _ := Finset.single_le_sum (f := fun k => 2 ^ (B * k))
              (by intro i _; positivity) (Finset.mem_range.mpr hM)
      have hgeo' : 2 ^ B * G + 1 = G + Gtop := by omega
      have hoff_geo : OFFn * (2 ^ B * G) + OFFn = OFFn * G + OFFn * Gtop := by
        have hc := congrArg (OFFn * ·) hgeo'
        simp only [Nat.mul_add, Nat.mul_one] at hc
        omega
      have hsum' : SP + SCin' + OFFn * (2 ^ B * G) = SS + SC + OFFn * G := by
        rw [← Nat.mul_assoc]; exact hsum
      omega
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_env ⊢
      obtain ⟨h_wit, _, _⟩ := h_env
      have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
      set OFFn := carryOffset (m := m) B with hOFFn
      have hOFF_eq : OFFn = (m + 1) * 2 ^ (B + 1) := rfl
      -- nat digit functions
      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input.rhs[k]'h).val else 0 with hSn
      have hPn_lt : ∀ k, Pn k < (m + 1) * 2 ^ (2 * B) := by
        intro k; simp only [hPn]; split
        · rename_i h; exact h_assumptions.1 ⟨k, h⟩
        · positivity
      have hSn_lt : ∀ k, Sn k < (m + 1) * 2 ^ (2 * B) := by
        intro k; simp only [hSn]; split
        · rename_i h; exact h_assumptions.2 ⟨k, h⟩
        · positivity
      -- partial sums
      set PFn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) with hPFn
      set PSn : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) with hPSn
      -- evalPartial equals our partial sums
      have hPFn_eq : ∀ k, evalPartial B env input_var.lhs k = PFn k := by
        intro k; simp only [evalPartial, hPFn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hPn]; split
        · rename_i h; rw [← h_input]; simp [Vector.getElem_map]
        · rfl
      have hPSn_eq : ∀ k, evalPartial B env input_var.rhs k = PSn k := by
        intro k; simp only [evalPartial, hPSn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hSn]; split
        · rename_i h; rw [← h_input]; simp [Vector.getElem_map]
        · rfl
      -- carry value
      set Dk : ℕ → ℕ := fun k => 2 ^ (B * (k + 1)) with hDk
      set Cn : ℕ → ℕ := fun k => OFFn + PFn k / Dk k - PSn k / Dk k with hCn
      -- beta-reducing application lemmas (the `set`s above are functions)
      have hDk_app : ∀ k, Dk k = 2 ^ (B * (k + 1)) := fun k => rfl
      have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) := fun k => rfl
      have hPSn_app : ∀ k, PSn k = ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) := fun k => rfl
      have hCn_app : ∀ k, Cn k = OFFn + PFn k / Dk k - PSn k / Dk k := fun k => rfl
      -- the witnessed value equals Cn
      have hwit_eq : ∀ k, k < 2 * m - 1 → env.get (i₀ + k) = (Cn k : F p) := by
        intro k hk
        rw [h_wit ⟨k, hk⟩]
        simp only [Vector.getElem_ofFn, hCn_app, hDk_app, hPFn_eq, hPSn_eq]
      -- per-sequence div bounds (carry magnitude)
      have hPFdiv : ∀ k, PFn k / Dk k ≤ OFFn := by
        intro k; rw [hOFF_eq]; exact partial_div_bound B m hB1 Pn hPn_lt k
      have hPSdiv : ∀ k, PSn k / Dk k ≤ OFFn := by
        intro k; rw [hOFF_eq]; exact partial_div_bound B m hB1 Sn hSn_lt k
      -- range check: each carry < 2^W
      have hrange : ∀ k, Cn k < 2 ^ W := by
        intro k
        have h1 := hPFdiv k
        rw [hCn_app]
        calc OFFn + PFn k / Dk k - PSn k / Dk k ≤ OFFn + PFn k / Dk k := Nat.sub_le _ _
          _ ≤ OFFn + OFFn := by omega
          _ < 2 ^ W := by have := hWB; omega
      -- 2^B < p (handy)
      have hpB : 2 ^ B < p := by
        have hle : 2 ^ B ≤ 2 ^ W * 2 ^ B := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos W)
        omega
      have hOFFn_lt : OFFn < p := by
        have : OFFn ≤ OFFn * 2 := Nat.le_mul_of_pos_right _ (by norm_num); omega
      have hOFFn_cast : (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt
      -- mod-matching: low digits of PFn and PSn agree through each index
      have hPFn_top : PFn (2 * m - 2) = polyValue B input.lhs := by
        rw [hPFn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Pn j * 2 ^ (B * j)),
          show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hPn, dif_pos i.isLt]
      have hPSn_top : PSn (2 * m - 2) = polyValue B input.rhs := by
        rw [hPSn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Sn j * 2 ^ (B * j)),
          show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hSn, dif_pos i.isLt]
      have hPtop_eq : PFn (2 * m - 2) = PSn (2 * m - 2) := by
        rw [hPFn_top, hPSn_top]; exact h_spec
      have hmod : ∀ k, k < 2 * m - 1 → PFn k % Dk k = PSn k % Dk k := by
        intro k hk
        have e1 : PFn (2 * m - 2) % Dk k = PFn k % Dk k := by
          rw [hPFn_app, hPFn_app, hDk_app, show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
          exact partial_mod_stable B Pn (2 * m - 1) k hk
        have e2 : PSn (2 * m - 2) % Dk k = PSn k % Dk k := by
          rw [hPSn_app, hPSn_app, hDk_app, show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
          exact partial_mod_stable B Sn (2 * m - 1) k hk
        rw [← e1, ← e2, hPtop_eq]
      -- the per-index unified ℕ recurrence
      -- top carry equals OFFn (signed carry 0) since the two values are equal
      have hCtop : Cn (2 * m - 2) = OFFn := by
        rw [hCn_app, hPtop_eq]; omega
      have hidx : ∀ k, k < 2 * m - 1 →
          Pn k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B
            = Sn k + Cn k * 2 ^ B + OFFn := by
        intro k hk
        -- running quotients and digits
        set qP := PFn k / 2 ^ (B * k) with hqP_def
        set qS := PSn k / 2 ^ (B * k) with hqS_def
        set rP := PFn k / Dk k with hrP_def
        set rS := PSn k / Dk k with hrS_def
        -- rP = qP / 2^B (and similarly rS = qS / 2^B)
        have hrP_quot : rP = qP / 2 ^ B := by
          rw [hrP_def, hqP_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
            Nat.div_div_eq_div_mul]
        have hrS_quot : rS = qS / 2 ^ B := by
          rw [hrS_def, hqS_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
            Nat.div_div_eq_div_mul]
        -- qP = rP * 2^B + digit ; qS = rS * 2^B + digit
        have hsplitP : qP = rP * 2 ^ B + qP % 2 ^ B := by
          rw [hrP_quot]; exact (Nat.div_add_mod' qP (2 ^ B)).symm
        have hsplitS : qS = rS * 2 ^ B + qS % 2 ^ B := by
          rw [hrS_quot]; exact (Nat.div_add_mod' qS (2 ^ B)).symm
        -- digit matching: the k-th base-2^B digit of PFn and PSn agree
        have hdig : qP % 2 ^ B = qS % 2 ^ B := by
          have hP : qP % 2 ^ B = PFn k % Dk k / 2 ^ (B * k) := by
            rw [hqP_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
              Nat.mod_mul_right_div_self]
          have hS : qS % 2 ^ B = PSn k % Dk k / 2 ^ (B * k) := by
            rw [hqS_def, hDk_app, show B * (k + 1) = B * k + B by ring, pow_add,
              Nat.mod_mul_right_div_self]
          rw [hP, hS, hmod k hk]
        -- ripple step: qP = Pn k + (carry-in from prev)
        have hstepP : qP = Pn k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, Pn j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
          rw [hqP_def, hPFn_app]; exact quot_step B Pn k
        have hstepS : qS = Sn k + (if k = 0 then 0
            else (∑ j ∈ Finset.range k, Sn j * 2 ^ (B * j)) / 2 ^ (B * k)) := by
          rw [hqS_def, hPSn_app]; exact quot_step B Sn k
        -- relate prev quotient to Cn (k-1)
        have hCnk : Cn k = OFFn + rP - rS := by rw [hCn_app, ← hrP_def, ← hrS_def]
        have hrS_le : rS ≤ OFFn := by rw [hrS_def]; exact hPSdiv k
        -- digit equality as a single value
        rw [hdig] at hsplitP
        -- make the carry scalars plain variables so omega can reason with ℕ subtraction
        clear_value qP qS rP rS
        -- distribute the outgoing-carry product so omega only sees linear atoms
        have hmulCnk : Cn k * 2 ^ B = OFFn * 2 ^ B + rP * 2 ^ B - rS * 2 ^ B := by
          rw [hCnk, Nat.sub_mul, Nat.add_mul]
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          rw [hmulCnk]
          simp only [↓reduceIte] at hstepP hstepS ⊢
          rw [Nat.add_zero] at hstepP hstepS
          -- qP = Pn 0, qS = Sn 0, hsplitP: qP = rP*2^B + d, hsplitS: qS = rS*2^B + d
          have hrPmul : rS * 2 ^ B ≤ rP * 2 ^ B + OFFn * 2 ^ B := by
            have : rS ≤ rP + OFFn := by omega
            calc rS * 2 ^ B ≤ (rP + OFFn) * 2 ^ B := Nat.mul_le_mul_right _ this
              _ = rP * 2 ^ B + OFFn * 2 ^ B := by rw [Nat.add_mul]
          omega
        · rw [if_neg (by omega : ¬ k = 0), hmulCnk]
          -- ∑_{j<k} Pn = PFn(k-1) for k>0
          have hPFnprev : (∑ j ∈ Finset.range k, Pn j * 2 ^ (B * j)) = PFn (k - 1) := by
            rw [hPFn_app, show k - 1 + 1 = k from by omega]
          have hPSnprev : (∑ j ∈ Finset.range k, Sn j * 2 ^ (B * j)) = PSn (k - 1) := by
            rw [hPSn_app, show k - 1 + 1 = k from by omega]
          rw [if_neg (by omega : ¬ k = 0), hPFnprev] at hstepP
          rw [if_neg (by omega : ¬ k = 0), hPSnprev] at hstepS
          -- carry-in quotients equal the previous Cn's rP'/rS'
          set rP' := PFn (k - 1) / Dk (k - 1) with hrP'_def
          set rS' := PSn (k - 1) / Dk (k - 1) with hrS'_def
          have hprevP : PFn (k - 1) / 2 ^ (B * k) = rP' := by
            rw [hrP'_def, hDk_app, show k - 1 + 1 = k from by omega]
          have hprevS : PSn (k - 1) / 2 ^ (B * k) = rS' := by
            rw [hrS'_def, hDk_app, show k - 1 + 1 = k from by omega]
          rw [hprevP] at hstepP
          rw [hprevS] at hstepS
          have hCnprev : Cn (k - 1) = OFFn + rP' - rS' := hCn_app (k - 1)
          have hrSprev_le : rS' ≤ OFFn := hPSdiv (k - 1)
          rw [hCnprev]
          clear_value rP' rS'
          have hrPmul : rS * 2 ^ B ≤ rP * 2 ^ B + OFFn * 2 ^ B := by
            have : rS ≤ rP + OFFn := by omega
            calc rS * 2 ^ B ≤ (rP + OFFn) * 2 ^ B := Nat.mul_le_mul_right _ this
              _ = rP * 2 ^ B + OFFn * 2 ^ B := by rw [Nat.add_mul]
          omega
      -- carry val facts
      have hCn_val : ∀ k, k < 2 * m - 1 → (env.get (i₀ + k)).val = Cn k := by
        intro k hk
        rw [hwit_eq k hk, ZMod.val_natCast_of_lt (lt_of_lt_of_le (hrange k) (le_of_lt hW))]
      refine ⟨?_, ?_, ?_⟩
      · -- range check
        intro i
        rw [hCn_val i.val i.isLt]; exact hrange i.val
      · -- per-index field equation
        intro i
        have hk := i.isLt
        have hnatk := hidx i.val hk
        -- evaluate symbolic subterms
        have ha_e : Expression.eval env.toEnvironment input_var.lhs[i.val] = input.lhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var.rhs[i.val] = input.rhs[i.val]'hk := by
          rw [← h_input]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0 else var { index := i₀ + (i.val - 1) } - Expression.const (OFFn : F p))
            = if i.val = 0 then 0 else env.get (i₀ + (i.val - 1)) - (OFFn : F p) := by
          split <;> simp [circuit_norm, sub_eq_add_neg]
        rw [ha_e, hb_e, hcin_e]
        -- val-cast facts
        have hAk : ((Pn i.val : ℕ) : F p) = (input.lhs[i.val]'hk) := by
          simp only [hPn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Sn i.val : ℕ) : F p) = (input.rhs[i.val]'hk) := by
          simp only [hSn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hCk : ((Cn i.val : ℕ) : F p) = env.get (i₀ + i.val) := by
          rw [hwit_eq i.val hk]
        have hOFFcast : ((OFFn : ℕ) : F p) = (OFFn : F p) := rfl
        have hpow_cast : ((2 ^ B : ℕ) : F p) = (2 ^ B : F p) := by push_cast; ring
        -- cast hidx to F p
        have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
        push_cast [hpow_cast] at hcast
        rw [hAk, hBk, hCk] at hcast
        rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
        · simp only [hi0, ↓reduceIte, add_zero] at hcast ⊢
          rw [← sub_eq_zero] at hcast
          rw [← hcast]; ring
        · simp only [if_neg (by omega : ¬ i.val = 0)] at hcast ⊢
          have hCkprev : ((Cn (i.val - 1) : ℕ) : F p) = env.get (i₀ + (i.val - 1)) := by
            rw [hwit_eq (i.val - 1) (by omega)]
          rw [hCkprev, ← sub_eq_zero] at hcast
          rw [← hcast]; ring
      · -- top carry zero
        rw [dif_neg (by omega : ¬ (2 * m - 1 = 0))]
        simp only [circuit_norm]
        have : env.get (i₀ + (2 * m - 1 - 1)) = (OFFn : F p) := by
          rw [show 2 * m - 1 - 1 = 2 * m - 2 from by omega, hwit_eq (2 * m - 2) (by omega), hCtop]
        rw [this]; ring

end EqViaCarries

end

end Solution.Secp256k1ScalarMul
