import Solution.Secp256k1ScalarMulFixedBase.Normalize
import Solution.Secp256k1ScalarMulFixedBase.Equal
import Solution.Secp256k1ScalarMulFixedBase.WitgenLimbs
import Challenge.Utils.ComputableWitnessLemmas

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

namespace Solution.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

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

/-! ## Witness program for the carry chain

The carry out of index `k` is a quotient of the *prefix* value through `k`, which no
single loop body can fold. The program accumulates that prefix sum in one fixed-width
digit register (`IRLimbs.prefixP`) and reads the carry out of it with the free
`shiftDigits` window; `OFF + cP − cS` is then an offset addition and a wrapping
subtraction in the digit layer, both exact because the offset dominates both carries
(`partial_div_bound`).

`carryN` is that register arithmetic with every truncation spelled out, hence a total
function of the coefficient *values*: `eval_toIR_carryWitness_congr` therefore needs no
side condition at all, and `getElem_eval_carryWitness` reads the register back as the
intended offset carry under the gadget's `Assumptions`.
-/

section Generator
open Witgen WitgenNat WitgenBigNat IRLimbs

/-- Width of a coefficient: the `Assumptions` bound `(m+1)·2^(2B)` is below `2^(2B+m+1)`. -/
def coeffBits (m B : ℕ) : ℕ := 2 * B + m + 1

/-- Width of an offset carry: `2·OFF = (m+1)·2^(B+2)` is below `2^(B+m+3)`. -/
def carryBits (m B : ℕ) : ℕ := B + m + 3

/-- Digits of a carry register. -/
def carryLen (m B : ℕ) : ℕ := numChunks (carryBits m B)

/-- Digits of the prefix-sum register. -/
def prefLen (m B : ℕ) : ℕ :=
  numChunks (coeffBits m B + B * (2 * m - 1) + (2 * m - 1))

/-- The register arithmetic of one offset carry, every truncation spelled out, hence a
total function of the coefficient values. -/
def carryN (B nbits PL CL CB OFF : ℕ) (vP vS : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((OFF % base ^ CL + prefN B nbits PL vP (k + 1) / 2 ^ (B * (k + 1)) % base ^ CL) % base ^ CL
      + base ^ CL - prefN B nbits PL vS (k + 1) / 2 ^ (B * (k + 1)) % base ^ CL)
    % base ^ CL % 2 ^ CB

/-- The offset running carries out of indices `k, k+1, …, k+n-1`. -/
def carryL (B nbits PL CL CB OFF : ℕ) (Pc Sc : List (Expression (F p))) :
    ℕ → ℕ → M (F p) (List (FExpr (F p)))
  | 0, _ => Pure.pure []
  | n + 1, k => do
      let aP ← prefixP B nbits PL Pc (k + 1)
      let aS ← prefixP B nbits PL Sc (k + 1)
      let t ← addP (constDigits OFF CL) (shiftDigits aP (B * (k + 1)) CL) (uc 0)
      let d ← subP (resizeDigits t CL) (shiftDigits aS (B * (k + 1)) CL) (uc 0)
      let rest ← carryL B nbits PL CL CB OFF Pc Sc n (k + 1)
      Pure.pure (limbF d.1 0 CB :: rest)

theorem computesFL_carryL (B nbits PL CL CB OFF : ℕ) (Pc Sc : List (Expression (F p))) :
    ∀ (n k : ℕ) {S : Array (Step (F p))},
      ComputesFL S (carryL B nbits PL CL CB OFF Pc Sc n k)
        (fun env j => if j < n then
          ((carryN B nbits PL CL CB OFF (coeffVals Pc env) (coeffVals Sc env) (k + j) : ℕ) : F p)
          else 0) := by
  intro n
  induction n with
  | zero => intro k S; exact Computes.pure (EvalsFL.nil (by simp))
  | succ n ih =>
    intro k S
    refine Computes.bind (computesBig_prefixP B nbits PL Pc (k + 1)) ?_
    intro S1 aP _ haP
    refine Computes.bind (computesBig_prefixP B nbits PL Sc (k + 1)) ?_
    intro S2 aS hS2 haS
    have hcP : EvalsBig S2 (shiftDigits aP (B * (k + 1)) CL)
        (fun env => ofNat (prefN B nbits PL (coeffVals Pc env) (k + 1) / 2 ^ (B * (k + 1))) CL) :=
      (evalsBig_shiftDigits (haP.mono hS2) (B * (k + 1)) CL).congr fun env => by
        rw [lval_ofNat_of_lt (prefN_lt B nbits PL _ (k + 1))]
    have hcS : EvalsBig S2 (shiftDigits aS (B * (k + 1)) CL)
        (fun env => ofNat (prefN B nbits PL (coeffVals Sc env) (k + 1) / 2 ^ (B * (k + 1))) CL) :=
      (evalsBig_shiftDigits haS (B * (k + 1)) CL).congr fun env => by
        rw [lval_ofNat_of_lt (prefN_lt B nbits PL _ (k + 1))]
    refine Computes.bind (computesBig_addP _ _ (uc 0) (evalsBig_constDigits OFF CL) hcP
      (EvalsU.uc 0 (by norm_num)) (fun _ => base_pos)) ?_
    intro S3 t hS3 ht
    have hT : EvalsBig S3 (resizeDigits t CL)
        (fun env => ofNat ((OFF % base ^ CL
          + prefN B nbits PL (coeffVals Pc env) (k + 1) / 2 ^ (B * (k + 1)) % base ^ CL)
          % base ^ CL) CL) :=
      (evalsBig_resizeDigits ht CL).congr fun env => by
        rw [lval_addc, lval_ofNat, lval_ofNat, Nat.add_zero, ofNat_mod]
    refine Computes.bind (computesBigU_subP _ _ (uc 0) hT (hcS.mono hS3)
      (EvalsU.uc 0 (by norm_num)) (fun _ => by norm_num)) ?_
    intro S4 d hS4 hd
    have hd1 : EvalsBig S4 d.1 (fun env => subb
        (ofNat ((OFF % base ^ CL
          + prefN B nbits PL (coeffVals Pc env) (k + 1) / 2 ^ (B * (k + 1)) % base ^ CL)
          % base ^ CL) CL)
        (ofNat (prefN B nbits PL (coeffVals Sc env) (k + 1) / 2 ^ (B * (k + 1))) CL) 0) := hd.1
    refine Computes.bind (ih (k + 1)) ?_
    intro S5 rest hS5 hrest
    refine Computes.pure (EvalsFL.cons ?_ (hrest.congr fun env j => ?_))
    · refine (evalsF_limbF (hd1.mono hS5) 0 CB).congr fun env => ?_
      rw [if_pos (by omega), pow_zero, Nat.div_one, carryN,
        lval_subb_mod (bounded_ofNat _ _) (bounded_ofNat _ _) (by simp), length_ofNat,
        lval_ofNat_of_lt (Nat.mod_lt _ (Nat.pow_pos base_pos)), lval_ofNat, Nat.add_zero]
    · by_cases hj : j < n
      · rw [if_pos hj, if_pos (by omega), show k + 1 + j = k + (j + 1) by omega]
      · rw [if_neg hj, if_neg (by omega)]

/-- The whole carry vector as a witness program. -/
def carryProg (B nbits PL CL CB OFF n : ℕ) (Pc Sc : List (Expression (F p))) :
    M (F p) (VExpr (F p) n) := do
  let outs ← carryL B nbits PL CL CB OFF Pc Sc n 0
  Pure.pure (.lit (Vector.ofFn fun k : Fin n => outs.getD k.val (.const 0)))

theorem computesV_carryProg (B nbits PL CL CB OFF n : ℕ) (Pc Sc : List (Expression (F p))) :
    ComputesV #[] (carryProg B nbits PL CL CB OFF n Pc Sc)
      (fun env => Vector.ofFn fun k : Fin n =>
        ((carryN B nbits PL CL CB OFF (coeffVals Pc env) (coeffVals Sc env) k.val : ℕ) : F p)) := by
  refine Computes.bind (computesFL_carryL B nbits PL CL CB OFF Pc Sc n 0) ?_
  intro S outs _ houts
  refine Computes.pure ((EvalsV.ofFL houts).congr fun env => ?_)
  refine Vector.ext fun k hk => ?_
  simp only [Vector.getElem_ofFn, if_pos hk, Nat.zero_add]

/-- The carry witness program of `main`. -/
def carryWitness (P : BigIntParams p m) (Pc Sc : Var (Coeffs m) (F p)) :
    M (F p) (VExpr (F p) (2 * m - 1)) :=
  carryProg P.B (coeffBits m P.B) (prefLen m P.B) (carryLen m P.B) (carryBits m P.B)
    (carryOffset (m := m) P.B) (2 * m - 1) Pc.toList Sc.toList

omit [NeZero m] in
/-- `carryWitness` reads the coefficient sequences only through their limb values. -/
theorem eval_toIR_carryWitness_congr (P : BigIntParams p m) (Pc Sc : Var (Coeffs m) (F p))
    {env env' : ProverEnvironment (F p)}
    (hP : ∀ (j : ℕ) (hj : j < 2 * m - 1),
      Expression.eval env.toEnvironment (Pc[j]'hj)
        = Expression.eval env'.toEnvironment (Pc[j]'hj))
    (hS : ∀ (j : ℕ) (hj : j < 2 * m - 1),
      Expression.eval env.toEnvironment (Sc[j]'hj)
        = Expression.eval env'.toEnvironment (Sc[j]'hj)) :
    (carryWitness P Pc Sc).toIR.eval env = (carryWitness P Pc Sc).toIR.eval env' := by
  have hcv : ∀ (x : Var (Coeffs m) (F p)),
      (∀ (j : ℕ) (hj : j < 2 * m - 1), Expression.eval env.toEnvironment (x[j]'hj)
        = Expression.eval env'.toEnvironment (x[j]'hj)) →
      coeffVals x.toList env = coeffVals x.toList env' := by
    intro x hx
    funext j
    rw [coeffVals_toList, coeffVals_toList]
    split
    · rename_i h; rw [hx j h]
    · rfl
  rw [carryWitness, IRLimbs.toIR_eq, Witgen.WitgenIR.eval]
  show Witgen.VExpr.eval { env := env, locals := _ } _
    = Witgen.VExpr.eval { env := env', locals := _ } _
  rw [IRLimbs.eval_program (computesV_carryProg _ _ _ _ _ _ _ _ _) env,
    IRLimbs.eval_program (computesV_carryProg _ _ _ _ _ _ _ _ _) env',
    hcv Pc hP, hcv Sc hS]

omit [NeZero m] in
/-- Bridge for `carryWitness` in the branch that matters: with the coefficients in range
and both carry magnitudes bounded by the offset (which the `Assumptions` and
`partial_div_bound` give), the witnessed cell is the offset running carry. -/
theorem getElem_eval_carryWitness (P : BigIntParams p m) (Pc Sc : Var (Coeffs m) (F p))
    (env : ProverEnvironment (F p)) (k : ℕ) (hk : k < 2 * m - 1)
    (hPb : ∀ (j : ℕ) (hj : j < 2 * m - 1),
      (Expression.eval env.toEnvironment (Pc[j]'hj)).val < (m + 1) * 2 ^ (2 * P.B))
    (hSb : ∀ (j : ℕ) (hj : j < 2 * m - 1),
      (Expression.eval env.toEnvironment (Sc[j]'hj)).val < (m + 1) * 2 ^ (2 * P.B))
    (hPle : evalPartial P.B env Pc k / 2 ^ (P.B * (k + 1)) ≤ carryOffset (m := m) P.B)
    (hSle : evalPartial P.B env Sc k / 2 ^ (P.B * (k + 1)) ≤ carryOffset (m := m) P.B) :
    (Witgen.VExpr.eval
        { env := env,
          locals := Witgen.evalSteps env (carryWitness P Pc Sc #[]).2.toList }
        (carryWitness P Pc Sc #[]).1)[k]
      = ((carryOffset (m := m) P.B + evalPartial P.B env Pc k / 2 ^ (P.B * (k + 1))
            - evalPartial P.B env Sc k / 2 ^ (P.B * (k + 1)) : ℕ) : F p) := by
  -- the coefficient values, and their prefix sums, in the shape the library states them
  have hpart : ∀ (x : Var (Coeffs m) (F p)) (j : ℕ),
      (∑ i ∈ Finset.range (j + 1), coeffVals x.toList env i * 2 ^ (P.B * i))
        = evalPartial P.B env x j := by
    intro x j
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeffVals_toList]
  have hcb : ∀ (x : Var (Coeffs m) (F p)),
      (∀ (j : ℕ) (hj : j < 2 * m - 1),
        (Expression.eval env.toEnvironment (x[j]'hj)).val < (m + 1) * 2 ^ (2 * P.B)) →
      ∀ j, j < 2 * m - 1 → coeffVals x.toList env j < 2 ^ coeffBits m P.B := by
    intro x hx j hj
    have h1 : (m + 1) * 2 ^ (2 * P.B) < 2 ^ (m + 1) * 2 ^ (2 * P.B) :=
      Nat.mul_lt_mul_of_lt_of_le Nat.lt_two_pow_self (le_refl _) (Nat.two_pow_pos _)
    have h2 : (2 : ℕ) ^ (m + 1) * 2 ^ (2 * P.B) = 2 ^ coeffBits m P.B := by
      rw [← pow_add, coeffBits]; congr 1; omega
    rw [coeffVals_toList, dif_pos hj]
    have := hx j hj
    omega
  have hOFF2 : 2 * carryOffset (m := m) P.B < 2 ^ carryBits m P.B := by
    have h1 : 2 * ((m + 1) * 2 ^ (P.B + 1)) = (m + 1) * 2 ^ (P.B + 2) := by ring
    have h2 : (m + 1) * 2 ^ (P.B + 2) < 2 ^ (m + 1) * 2 ^ (P.B + 2) :=
      Nat.mul_lt_mul_of_lt_of_le Nat.lt_two_pow_self (le_refl _) (Nat.two_pow_pos _)
    have h3 : (2 : ℕ) ^ (m + 1) * 2 ^ (P.B + 2) = 2 ^ carryBits m P.B := by
      rw [← pow_add, carryBits]; congr 1; omega
    rw [show carryOffset (m := m) P.B = (m + 1) * 2 ^ (P.B + 1) from rfl]
    omega
  unfold carryWitness
  rw [IRLimbs.eval_program (computesV_carryProg _ _ _ _ _ _ _ _ _) env]
  simp only [Vector.getElem_ofFn]
  rw [show (carryN P.B (coeffBits m P.B) (prefLen m P.B) (carryLen m P.B) (carryBits m P.B)
        (carryOffset (m := m) P.B) (coeffVals Pc.toList env) (coeffVals Sc.toList env) k)
      = carryOffset (m := m) P.B + evalPartial P.B env Pc k / 2 ^ (P.B * (k + 1))
          - evalPartial P.B env Sc k / 2 ^ (P.B * (k + 1)) from ?_]
  rw [carryN, prefN_eq P.B (coeffBits m P.B) (prefLen m P.B) (2 * m - 1) _
      (hcb Pc hPb) (by rw [prefLen]; exact two_pow_le_base_numChunks _) _ (by omega),
    prefN_eq P.B (coeffBits m P.B) (prefLen m P.B) (2 * m - 1) _
      (hcb Sc hSb) (by rw [prefLen]; exact two_pow_le_base_numChunks _) _ (by omega),
    hpart, hpart]
  exact carry_mod_eq hPle hSle hOFF2 (by rw [carryLen]; exact two_pow_le_base_numChunks _)

end Generator

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
  -- offset running carry out of index k:
  --   OFF + (Σ_{j ≤ k} P[j]·2^(B·j) − Σ_{j ≤ k} S[j]·2^(B·j)) / 2^(B*(k+1))
  let carry ← witnessVectorProgram (2 * m - 1) (carryWitness P Pc Sc)

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
    simp only [main, circuit_norm, Normalize.rangeCheck_localLength]
    split <;> simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Normalize.rangeCheck_localLength]
    split <;> simp +arith [circuit_norm]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, Normalize.rangeCheck_localLength,
      Normalize.rangeCheck_channelsWithGuarantees]
    split <;> simp +arith [circuit_norm]

omit [NeZero m] in
/-- Per-field projection of an `eval`-agreement hypothesis on the `Inputs` struct.
The `Var Inputs` `match` no longer iota-reduces on a struct *variable*, so the
destructuring has to happen here, once. -/
lemma eval_inputs_parts {input : Var (Inputs m) (F p)} {env env' : ProverEnvironment (F p)}
    (h : eval env input = eval env' input) :
    eval env input.lhs = eval env' input.lhs ∧ eval env input.rhs = eval env' input.rhs := by
  obtain ⟨lhs, rhs⟩ := input
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h ⊢
  exact h

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
    requirementsChannelsLawful := by
      intro input offset
      simp only [main, circuit_norm, Normalize.rangeCheck_channelsWithRequirements]
      split <;> simp +arith [circuit_norm]
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
      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input_lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input_rhs[k]'h).val else 0 with hSn
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
          rw [← sub_eq_zero]; exact h_top
        simp only [hCn, this, hOFFn_cast]
      -- per-index nat equation (unified, effective carry-in OFFn at k=0)
      have h_idx : ∀ k, (hk : k < 2 * m - 1) →
          Pn k + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B
            = Sn k + Cn k * 2 ^ B + OFFn := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩
        -- evaluate symbolic subterms
        have ha_e : Expression.eval env input_var_lhs[(⟨k, hk⟩ : Fin (2*m-1)).val] = input_lhs[k]'hk := by
          rw [← h_input.1]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var_rhs[(⟨k, hk⟩ : Fin (2*m-1)).val] = input_rhs[k]'hk := by
          rw [← h_input.2]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin (2*m-1)).val = 0 then 0
              else var { index := i₀ + ((⟨k, hk⟩ : Fin (2*m-1)).val - 1) } - Expression.const (OFFn : F p))
            = if k = 0 then 0 else env.get (i₀ + (k - 1)) - (OFFn : F p) := by
          split <;> simp [circuit_norm]
        simp only [ha_e, hb_e, hcin_e] at hlin
        -- the unified field equation
        have hfield : (input_lhs[k]'hk) + (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1)))
            + (OFFn : F p) * (2 ^ B : F p)
            = (input_rhs[k]'hk) + env.get (i₀ + k) * (2 ^ B : F p) + (OFFn : F p) := by
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
        have hlhs : (input_lhs[k]'hk).val + (if k = 0 then OFFn else Cn (k - 1)) + OFFn * 2 ^ B < p := by
          have hp1 := hPn_lt k hk
          simp only [hPn, dif_pos hk] at hp1
          omega
        have hrhs : (input_rhs[k]'hk).val + (env.get (i₀ + k)).val * 2 ^ B + OFFn < p := by
          have hp2 := hSn_lt k hk
          simp only [hSn, dif_pos hk] at hp2
          have hc : (env.get (i₀ + k)).val < 2 ^ W := h_range ⟨k, hk⟩
          have hcB : (env.get (i₀ + k)).val * 2 ^ B ≤ 2 ^ W * 2 ^ B := by
            apply Nat.mul_le_mul_right; omega
          omega
        have hlift := per_index_lift (B := B) (input_lhs[k]'hk)
          (if k = 0 then (OFFn : F p) else env.get (i₀ + (k - 1)))
          (input_rhs[k]'hk) (env.get (i₀ + k)) (OFFn : F p)
          (if k = 0 then OFFn else Cn (k - 1)) OFFn hpB hcin_val hOFFn_cast hlhs hrhs hfield
        simp only [hPn, hSn, hCn, dif_pos hk] at hlift ⊢
        convert hlift using 2
      -- express polyValue as range sums of Pn / Sn
      have hpv1 : polyValue B input_lhs = ∑ k ∈ Finset.range (2 * m - 1), Pn k * 2 ^ (B * k) := by
        rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun k => Pn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hPn, dif_pos i.isLt]
      have hpv2 : polyValue B input_rhs = ∑ k ∈ Finset.range (2 * m - 1), Sn k * 2 ^ (B * k) := by
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
      set Pn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input_lhs[k]'h).val else 0 with hPn
      set Sn : ℕ → ℕ := fun k => if h : k < 2 * m - 1 then (input_rhs[k]'h).val else 0 with hSn
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
      have hPFn_eq : ∀ k, evalPartial B env input_var_lhs k = PFn k := by
        intro k; simp only [evalPartial, hPFn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hPn]; split
        · rename_i h; rw [← h_input.1]; simp [Vector.getElem_map]
        · rfl
      have hPSn_eq : ∀ k, evalPartial B env input_var_rhs k = PSn k := by
        intro k; simp only [evalPartial, hPSn]
        apply Finset.sum_congr rfl
        intro j _; congr 1
        simp only [hSn]; split
        · rename_i h; rw [← h_input.2]; simp [Vector.getElem_map]
        · rfl
      -- carry value
      set Dk : ℕ → ℕ := fun k => 2 ^ (B * (k + 1)) with hDk
      set Cn : ℕ → ℕ := fun k => OFFn + PFn k / Dk k - PSn k / Dk k with hCn
      -- beta-reducing application lemmas (the `set`s above are functions)
      have hDk_app : ∀ k, Dk k = 2 ^ (B * (k + 1)) := fun k => rfl
      have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k + 1), Pn j * 2 ^ (B * j) := fun k => rfl
      have hPSn_app : ∀ k, PSn k = ∑ j ∈ Finset.range (k + 1), Sn j * 2 ^ (B * j) := fun k => rfl
      have hCn_app : ∀ k, Cn k = OFFn + PFn k / Dk k - PSn k / Dk k := fun k => rfl
      -- per-sequence div bounds (carry magnitude)
      have hPFdiv : ∀ k, PFn k / Dk k ≤ OFFn := by
        intro k; rw [hOFF_eq]; exact partial_div_bound B m hB1 Pn hPn_lt k
      have hPSdiv : ∀ k, PSn k / Dk k ≤ OFFn := by
        intro k; rw [hOFF_eq]; exact partial_div_bound B m hB1 Sn hSn_lt k
      have hOFF2 : OFFn + OFFn < p := by
        have : OFFn * 2 = OFFn + OFFn := by ring
        omega
      -- the coefficient bounds in the variable-side shape the bridge wants
      have hPb : ∀ (j : ℕ) (hj : j < 2 * m - 1),
          (Expression.eval env.toEnvironment (input_var_lhs[j]'hj)).val
            < (m + 1) * 2 ^ (2 * B) := by
        intro j hj
        have h := h_assumptions.1 ⟨j, hj⟩
        rw [← h_input.1] at h
        simpa [Vector.getElem_map] using h
      have hSb : ∀ (j : ℕ) (hj : j < 2 * m - 1),
          (Expression.eval env.toEnvironment (input_var_rhs[j]'hj)).val
            < (m + 1) * 2 ^ (2 * B) := by
        intro j hj
        have h := h_assumptions.2 ⟨j, hj⟩
        rw [← h_input.2] at h
        simpa [Vector.getElem_map] using h
      -- the witnessed value equals Cn
      have hwit_eq : ∀ k, k < 2 * m - 1 → env.get (i₀ + k) = (Cn k : F p) := by
        intro k hk
        have hcw := h_wit ⟨k, hk⟩
        rw [getElem_eval_carryWitness ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ _ _ env k hk
            hPb hSb
            (by rw [hPFn_eq k, ← hDk_app k]; exact hPFdiv k)
            (by rw [hPSn_eq k, ← hDk_app k]; exact hPSdiv k)] at hcw
        rw [hcw]
        simp only [hCn_app, hDk_app, hPFn_eq, hPSn_eq, ← hOFFn]
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
      have hPFn_top : PFn (2 * m - 2) = polyValue B input_lhs := by
        rw [hPFn_app, polyValue, ← Fin.sum_univ_eq_sum_range (fun j => Pn j * 2 ^ (B * j)),
          show 2 * m - 2 + 1 = 2 * m - 1 from by omega]
        apply Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hPn, dif_pos i.isLt]
      have hPSn_top : PSn (2 * m - 2) = polyValue B input_rhs := by
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
        have ha_e : Expression.eval env.toEnvironment input_var_lhs[i.val] = input_lhs[i.val]'hk := by
          rw [← h_input.1]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var_rhs[i.val] = input_rhs[i.val]'hk := by
          rw [← h_input.2]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0 else var { index := i₀ + (i.val - 1) } - Expression.const (OFFn : F p))
            = if i.val = 0 then 0 else env.get (i₀ + (i.val - 1)) - (OFFn : F p) := by
          split <;> simp [circuit_norm]
        rw [ha_e, hb_e, hcin_e]
        -- val-cast facts
        have hAk : ((Pn i.val : ℕ) : F p) = (input_lhs[i.val]'hk) := by
          simp only [hPn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Sn i.val : ℕ) : F p) = (input_rhs[i.val]'hk) := by
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

open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    implies_true]
  rw [show witnessVectorProgram (F := F p) (2 * m - 1) (carryWitness P input.lhs input.rhs)
      = witnessIR (fields (2 * m - 1)) (carryWitness P input.lhs input.rhs).toIR from rfl,
    Circuit.witnessIR_structuralComputableWitnesses_iff]
  refine ⟨?_, ?_, trivial, ?_⟩
  · -- witness obligation: the generator agrees when the inputs agree
    intro _ h_input
    obtain ⟨hlhs, hrhs⟩ := eval_inputs_parts h_input
    have hlhs_j : ∀ j, (hj : j < 2 * m - 1) →
        Expression.eval env.toEnvironment input.lhs[j] = Expression.eval env'.toEnvironment input.lhs[j] := by
      intro j hj
      rw [ProvableType.getElem_eval_fields_prover input.lhs j hj,
          ProvableType.getElem_eval_fields_prover input.lhs j hj, hlhs]
    have hrhs_j : ∀ j, (hj : j < 2 * m - 1) →
        Expression.eval env.toEnvironment input.rhs[j] = Expression.eval env'.toEnvironment input.rhs[j] := by
      intro j hj
      rw [ProvableType.getElem_eval_fields_prover input.rhs j hj,
          ProvableType.getElem_eval_fields_prover input.rhs j hj, hrhs]
    exact eval_toIR_carryWitness_congr P _ _ hlhs_j hrhs_j
  · -- forEach rangeCheck: each carry input is a previously-allocated witness var
    intro i
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Gadgets.ToBits.rangeCheck P.W P.hW) input _ _ ?_
      (rangeCheckComputableWitnesses P.W P.hW) env env'
    intro k e1 e2 hle h_agree _
    have hk : offset + (2 * m - 1) ≤ k := by
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at hle
      omega
    have hmem := eval_mem_varFromOffset_fields_of_agreesBelow h_agree hk
    have hx := hmem _ (Vector.getElem_mem i.isLt)
    simp only [circuit_norm] at hx
    simp only [circuit_norm]
    exact hx
  · -- final top-carry assertion (or `pure ()` when 2m-1 = 0)
    split
    · simp only [Circuit.pure_structuralComputableWitnesses_iff]
    · simp only [Circuit.assertZero_structuralComputableWitnesses_iff]

theorem computableWitness (P : BigIntParams p m) [Fact (p > 2)] : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main P input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P)

/-! ## Sealing the witness programs

The programs are *data*, and big data: `circuit_norm` and any `rfl` that reaches a
circuit's `localLength` would otherwise start evaluating them, since the digit lists
are `map`s over `List.range` and the digit programs are ordinary recursions over
those. Downstream files reason through the bridges above instead.
-/

attribute [irreducible] carryWitness

end EqViaCarries

end

end Solution.Secp256k1ScalarMulFixedBase
