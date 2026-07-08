import Solution.Secp256k1ScalarMul.SubModTheorems
import Solution.Secp256k1ScalarMul.AddModL

/-!
# Emulated field subtraction, *lazy* variant — `SubModL`

`FormalCircuit` computing `c ≡ a − b (mod P256)` over **normalized** (not
necessarily canonical) emulated elements. Like `AddModL` it omits the
`LessThan` canonical check: the output is normalized-only and the spec is at
the `Fp` level (`decodeFe`).

Because operands may be `≥ P256`, the borrow `q` in the identity
`r + b = a + q·P256` ranges over `{0,1,2}` (not a boolean); it is range-checked
to 2 bits. The honest witness is

  `q = 0`            if `a ≥ b`,
  `q = 1`            if `a < b` and `b − a ≤ P256`,
  `q = 2`            otherwise,

with `r = a + q·P256 − b`, which is `< 2^256` in every case.
-/

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

/-! ## Generalized `SubMod` rhs helpers (`qN ≤ 3`) -/

/-- `EqViaCarries` coefficient bound for the lazy `SubMod` `rhs` vector
`a_k + q·p_k` with `q ≤ 3`. -/
lemma SubModL.rhs_bounds3 (env : Environment (F circomPrime)) (i₀ : ℕ)
    (a_var : Var Emu (F circomPrime)) (a : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (ha_norm : a.Normalized limbBits) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 3) :
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
    rw [val_q_mul_limb3 hqN k.val] at h2
    have h3 := limbOfNat_lt P256 k.val
    have h4 : qN * limbOfNat P256 k.val ≤ 3 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have hbnd : 2 ^ limbBits + 3 * 2 ^ limbBits ≤ (numLimbs + 1) * 2 ^ (2 * limbBits) := by
      decide
    omega
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

/-- **`polyValue` bridge (rhs)** for the lazy `SubMod` `rhs` vector, `q ≤ 3`. -/
lemma SubModL.polyValue_rhs3 (env : Environment (F circomPrime)) (i₀ : ℕ)
    (a_var : Var Emu (F circomPrime)) (a : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (ha_norm : a.Normalized limbBits) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 3) :
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
      ZMod.val_add_of_lt, val_q_mul_limb3 hqN k.val]
    · simp only [dif_pos hk]
    · rw [val_q_mul_limb3 hqN k.val]
      have h1 : (a[k.val]'hk).val < 2 ^ limbBits := ha_norm ⟨k.val, hk⟩
      have h2 := limbOfNat_lt P256 k.val
      have h3 : qN * limbOfNat P256 k.val ≤ 3 * limbOfNat P256 k.val :=
        Nat.mul_le_mul_right _ hqN
      have hb : 2 ^ limbBits + 3 * 2 ^ limbBits < circomPrime := by decide
      omega
  · rw [value_eq_range_sum limbBits a]
    have hsplit : (∑ k ∈ Finset.range numLimbs,
          ((if h : k < numLimbs then (a[k]'h).val else 0) + qN * limbOfNat P256 k)
            * 2 ^ (limbBits * k))
        = (∑ k ∈ Finset.range numLimbs,
            (if h : k < numLimbs then (a[k]'h).val else 0) * 2 ^ (limbBits * k))
          + ∑ k ∈ Finset.range numLimbs, qN * (limbOfNat P256 k * 2 ^ (limbBits * k)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, ← Finset.mul_sum, limb_sum_P256]

namespace SubModL

/-- The honest borrow: `0` if `a ≥ b`, else `1` if `b − a ≤ P256`, else `2`. -/
def subQ (va vb : ℕ) : ℕ := if va < vb then (if vb - va ≤ P256 then 1 else 2) else 0

/-- The honest reduced difference `a + q·P256 − b`. -/
def subR (va vb : ℕ) : ℕ := va + subQ va vb * P256 - vb

lemma subQ_le3 (va vb : ℕ) : subQ va vb ≤ 3 := by
  unfold subQ; split <;> [split; skip] <;> omega

/-- `vb ≤ va + q·P256`, so the reduced difference `subR` is an exact ℕ
subtraction (needs `va, vb < 2^256`). -/
lemma subLe (va vb : ℕ) (_hva : va < 2 ^ (limbBits * numLimbs))
    (hvb : vb < 2 ^ (limbBits * numLimbs)) : vb ≤ va + subQ va vb * P256 := by
  have hM2p : (2 : ℕ) ^ (limbBits * numLimbs) < 2 * P256 := by decide
  unfold subQ
  split
  · split <;> omega
  · omega

lemma subR_lt (va vb : ℕ) (hva : va < 2 ^ (limbBits * numLimbs))
    (hvb : vb < 2 ^ (limbBits * numLimbs)) : subR va vb < 2 ^ (limbBits * numLimbs) := by
  have hM2p : (2 : ℕ) ^ (limbBits * numLimbs) < 2 * P256 := by decide
  have hpM : P256 < 2 ^ (limbBits * numLimbs) := P256_lt
  unfold subR subQ
  split
  · split <;> omega
  · omega

/-- The borrow-form identity `r + b = a + q·P256` for the honest witness. -/
lemma subR_add (va vb : ℕ) (hva : va < 2 ^ (limbBits * numLimbs))
    (hvb : vb < 2 ^ (limbBits * numLimbs)) :
    subR va vb + vb = va + subQ va vb * P256 :=
  Nat.sub_add_cancel (subLe va vb hva hvb)

/-- Inputs of `SubModL`: minuend and subtrahend, both normalized (loose). -/
structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat (subR (evalEmu env a) (evalEmu env b))
  let q ← ProvableType.witness (α := field) fun env =>
    ((subQ (evalEmu env a) (evalEmu env b) : ℕ) : F circomPrime)

  Gadgets.ToBits.rangeCheck 2 (by decide) q

  Normalize.circuit secpParams r

  -- r + b = a + q·P256 as integers, limb-coefficient-wise
  let lhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then r[k.val]'h + b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + q * pConst[k.val]'h else 0
  EqViaCarries.circuit secpParams { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.a.Normalized limbBits ∧ input.b.Normalized limbBits

def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  out.Normalized limbBits ∧ decodeFe out = decodeFe input.a - decodeFe input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    Gadgets.ToBits.rangeCheck]
  obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
  obtain ⟨hq_range, hr_norm, h_eq_impl⟩ := h_holds
  have hq_lt4 : (env.get (i₀ + numLimbs)).val < 4 := by simpa using hq_range
  set qN := (env.get (i₀ + numLimbs)).val with hqNdef
  have hq_cast : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime) :=
    (ZMod.natCast_zmod_val _).symm
  have hqN3 : qN ≤ 3 := by omega
  have h_polyeq := h_eq_impl
    ⟨SubMod.lhs_bounds env i₀ input_var_b input_b h_input.2 hb_norm (outVar_val_lt env i₀ hr_norm),
      SubModL.rhs_bounds3 env i₀ input_var_a input_a h_input.1 ha_norm qN hq_cast hqN3⟩
  rw [show secpParams.B = limbBits from rfl] at h_polyeq
  rw [SubMod.polyValue_lhs env i₀ input_var_b input_b h_input.2 hb_norm (outVar_val_lt env i₀ hr_norm),
    SubModL.polyValue_rhs3 env i₀ input_var_a input_a h_input.1 ha_norm qN hq_cast hqN3] at h_polyeq
  refine ⟨hr_norm, ?_⟩
  -- push the ℕ identity `r + b = a + q·P256` into the emulated field
  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) h_polyeq
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _,
    mul_zero, add_zero] at hcast
  simp only [decodeFe]
  exact eq_sub_of_add_eq hcast

/-- **Completeness core.** The honest witnesses satisfy the range check,
`Normalize`, and `EqViaCarries`. -/
lemma completeness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha_norm : a.Normalized limbBits) (hb_norm : b.Normalized limbBits)
    (h_wit_r : ∀ i : Fin numLimbs,
      env.get (i₀ + i.val)
        = (emuOfNat (subR (BigInt.value limbBits a) (BigInt.value limbBits b)))[i.val])
    (h_wit_q : env.get (i₀ + numLimbs)
      = ((subQ (BigInt.value limbBits a) (BigInt.value limbBits b) : ℕ) : F circomPrime)) :
    ZMod.val (env.get (i₀ + numLimbs)) < 2 ^ 2 ∧
      BigInt.Normalized limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
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
  set va := BigInt.value limbBits a with hva
  set vb := BigInt.value limbBits b with hvb
  have hva_lt : va < 2 ^ (limbBits * numLimbs) := BigInt.value_lt ha_norm
  have hvb_lt : vb < 2 ^ (limbBits * numLimbs) := BigInt.value_lt hb_norm
  set qNat := subQ va vb with hqNat
  set rN := subR va vb with hrN
  have hqN3 : qNat ≤ 3 := subQ_le3 va vb
  have hrN_pow : rN < 2 ^ (limbBits * numLimbs) := subR_lt va vb hva_lt hvb_lt
  have hkey : rN + vb = va + qNat * P256 := subR_add va vb hva_lt hvb_lt
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
  refine ⟨?_, hrv_norm, ⟨?_, ?_⟩, ?_⟩
  · rw [h_wit_q, ZMod.val_natCast_of_lt (Nat.lt_of_le_of_lt hqN3 (by decide))]
    omega
  · exact SubMod.lhs_bounds env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hrv_norm)
  · exact SubModL.rhs_bounds3 env i₀ a_var a h_input_a ha_norm qNat h_wit_q hqN3
  · rw [SubMod.polyValue_lhs env i₀ b_var b h_input_b hb_norm (outVar_val_lt env i₀ hrv_norm),
      SubModL.polyValue_rhs3 env i₀ a_var a h_input_a ha_norm qNat h_wit_q hqN3,
      hrv_val]
    exact hkey

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    Gadgets.ToBits.rangeCheck]
  obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
  have heva : evalEmu env input_var_a = BigInt.value limbBits input_a := by
    rw [evalEmu, BigInt.value, ← h_input.1]
  have hevb : evalEmu env input_var_b = BigInt.value limbBits input_b := by
    rw [evalEmu, BigInt.value, ← h_input.2]
  rw [heva, hevb] at h_env
  exact completeness_core i₀ env.toEnvironment input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 ha_norm hb_norm h_env.1 h_env.2

def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SubModL

end Solution.Secp256k1ScalarMul
