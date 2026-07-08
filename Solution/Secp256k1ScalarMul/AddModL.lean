import Solution.Secp256k1ScalarMul.AddModTheorems
import Solution.Secp256k1ScalarMul.Normalize
import Solution.Secp256k1ScalarMul.EqViaCarries

/-!
# Emulated field addition, *lazy* variant — `AddModL`

`FormalCircuit` computing `c ≡ a + b (mod P256)` over **normalized** (not
necessarily canonical) emulated elements. Unlike `AddMod` it does **not** prove
`c < P256`: it omits the `LessThan` canonical check, so its output is only
guaranteed normalized (`< 2^256`), and its spec is stated at the `Fp` level via
`decodeFe` (which is insensitive to the choice of residue representative). This
is the building block of lazy reduction: intermediate values flow uncanonicalized
and are only reduced (`AddMod`/`SubMod`/`Reduce`) where a comparison or the final
output needs it.

Because operands may be `≥ P256`, the sum `a + b < 2^257` and the quotient
`q = (a+b)/P256 ∈ {0,1,2}` is no longer boolean; it is range-checked to 2 bits.
-/

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

/-! ## Generalized quotient-bound helpers (`qN ≤ 3`)

`AddMod`'s `val_q_mul_limb` / `rhs_bounds` / `polyValue_rhs` assume a boolean
quotient (`qN ≤ 1`). The lazy gadgets have `qN ≤ 2`; we reprove the same facts
under `qN ≤ 3` (2-bit range check). The proofs mirror the boolean ones, with the
field-fit bound `3·2^limbBits < circomPrime` (still far below the prime). -/

lemma val_q_mul_limb3 {qN : ℕ} (hqN : qN ≤ 3) (k : ℕ) :
    (((qN : ℕ) : F circomPrime) * ((limbOfNat P256 k : ℕ) : F circomPrime)).val
      = qN * limbOfNat P256 k := by
  have hq_lt : qN < circomPrime := Nat.lt_of_le_of_lt hqN (by decide)
  rw [ZMod.val_mul_of_lt, ZMod.val_natCast_of_lt hq_lt, val_limbOfNat]
  rw [ZMod.val_natCast_of_lt hq_lt, val_limbOfNat]
  have h1 := limbOfNat_lt P256 k
  have h2 : qN * limbOfNat P256 k ≤ 3 * limbOfNat P256 k :=
    Nat.mul_le_mul_right _ hqN
  have hb : (3 : ℕ) * 2 ^ limbBits < circomPrime := by decide
  omega

/-- `EqViaCarries` coefficient bound for the lazy `rhs` vector `q·p_k + r_k`
with `q ≤ 3`. -/
lemma AddModL.rhs_bounds3 (env : Environment (F circomPrime)) (i₀ : ℕ) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 3)
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
    rw [val_q_mul_limb3 hqN k.val] at h1
    have h2 := limbOfNat_lt P256 k.val
    have h3 : qN * limbOfNat P256 k.val ≤ 3 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have h4 := hr k.val hk
    have hbnd : (3 : ℕ) * 2 ^ limbBits + 2 ^ limbBits ≤ (numLimbs + 1) * 2 ^ (2 * limbBits) := by
      decide
    omega
  · rw [dif_neg hk, show Expression.eval env (0 : Expression (F circomPrime)) = 0 from rfl,
      ZMod.val_zero]
    positivity

/-- **`polyValue` bridge (rhs)** for the lazy `rhs` vector, `q ≤ 3`. -/
lemma AddModL.polyValue_rhs3 (env : Environment (F circomPrime)) (i₀ : ℕ) (qN : ℕ)
    (hq : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime)) (hqN : qN ≤ 3)
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
      ZMod.val_add_of_lt, val_q_mul_limb3 hqN k.val]
    rw [val_q_mul_limb3 hqN k.val]
    have h2 := limbOfNat_lt P256 k.val
    have h3 : qN * limbOfNat P256 k.val ≤ 3 * limbOfNat P256 k.val :=
      Nat.mul_le_mul_right _ hqN
    have h4 := hr k.val hk
    have hb : (3 : ℕ) * 2 ^ limbBits + 2 ^ limbBits < circomPrime := by decide
    omega
  · rw [value_outVar limbBits env i₀]
    have hsplit : (∑ k ∈ Finset.range numLimbs,
          (qN * limbOfNat P256 k + (env.get (i₀ + k)).val) * 2 ^ (limbBits * k))
        = (∑ k ∈ Finset.range numLimbs, qN * (limbOfNat P256 k * 2 ^ (limbBits * k)))
          + ∑ k ∈ Finset.range numLimbs, (env.get (i₀ + k)).val * 2 ^ (limbBits * k) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, ← Finset.mul_sum, limb_sum_P256]

namespace AddModL

/-- Inputs of `AddModL`: two normalized operands (not necessarily canonical). -/
structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  -- witness r ≡ a + b (mod P256) as canonical digits, and the quotient q
  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((evalEmu env a + evalEmu env b) % P256)
  let q ← ProvableType.witness (α := field) fun env =>
    (((evalEmu env a + evalEmu env b) / P256 : ℕ) : F circomPrime)

  -- q ∈ {0,1,2,3}: range-check to 2 bits (no boolean assert — sum may exceed 2·P256)
  Gadgets.ToBits.rangeCheck 2 (by decide) q

  -- r is normalized (but NOT checked < P256 — that is the point)
  Normalize.circuit secpParams r

  -- a + b = q·P256 + r as integers, limb-coefficient-wise
  let lhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then q * pConst[k.val]'h + r[k.val]'h else 0
  EqViaCarries.circuit secpParams { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

/-- Preconditions: both operands are normalized (loose — no canonical bound). -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  input.a.Normalized limbBits ∧ input.b.Normalized limbBits

/-- Postcondition: the output is normalized and decodes to the base-field sum
(no canonical `< P256` guarantee). -/
def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  out.Normalized limbBits ∧ decodeFe out = decodeFe input.a + decodeFe input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    Gadgets.ToBits.rangeCheck]
  obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
  obtain ⟨hq_range, hr_norm, h_eq_impl⟩ := h_holds
  -- the quotient cell is < 4 (2-bit range check)
  have hq_lt4 : (env.get (i₀ + numLimbs)).val < 4 := by
    simpa using hq_range
  set qN := (env.get (i₀ + numLimbs)).val with hqNdef
  have hq_cast : env.get (i₀ + numLimbs) = ((qN : ℕ) : F circomPrime) :=
    (ZMod.natCast_zmod_val _).symm
  have hqN3 : qN ≤ 3 := by omega
  -- discharge the EqViaCarries assumptions and evaluate both polyValues
  have h_polyeq := h_eq_impl
    ⟨AddMod.lhs_bounds env input_var_a input_var_b input_a input_b h_input.1 h_input.2 ha_norm hb_norm,
      AddModL.rhs_bounds3 env i₀ qN hq_cast hqN3 (outVar_val_lt env i₀ hr_norm)⟩
  rw [show secpParams.B = limbBits from rfl] at h_polyeq
  rw [AddMod.polyValue_lhs env input_var_a input_var_b input_a input_b h_input.1 h_input.2 ha_norm hb_norm,
    AddModL.polyValue_rhs3 env i₀ qN hq_cast hqN3 (outVar_val_lt env i₀ hr_norm)] at h_polyeq
  refine ⟨hr_norm, ?_⟩
  -- push the ℕ identity `a + b = q·P256 + r` into the emulated field
  have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) h_polyeq
  push_cast at hcast
  rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _,
    mul_zero, zero_add] at hcast
  simp only [decodeFe]
  exact hcast.symm

/-- **Completeness core.** The honest witnesses (`r = (a+b) % P256` limbs,
`q = (a+b) / P256`) satisfy every constraint of `AddModL.main` (the range check,
`Normalize`, and `EqViaCarries` — no `LessThan`). -/
lemma completeness_core (i₀ : ℕ) (env : Environment (F circomPrime))
    (a_var b_var : Var Emu (F circomPrime)) (a b : Emu (F circomPrime))
    (h_input_a : Vector.map (Expression.eval env) a_var = a)
    (h_input_b : Vector.map (Expression.eval env) b_var = b)
    (ha_norm : a.Normalized limbBits) (hb_norm : b.Normalized limbBits)
    (h_wit_r : ∀ i : Fin numLimbs,
      env.get (i₀ + i.val)
        = (emuOfNat ((BigInt.value limbBits a + BigInt.value limbBits b) % P256))[i.val])
    (h_wit_q : env.get (i₀ + numLimbs)
      = (((BigInt.value limbBits a + BigInt.value limbBits b) / P256 : ℕ) : F circomPrime)) :
    ZMod.val (env.get (i₀ + numLimbs)) < 2 ^ 2 ∧
      BigInt.Normalized limbBits (Vector.map (Expression.eval env)
          (Vector.mapRange numLimbs fun i => var { index := i₀ + i })) ∧
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
  set va := BigInt.value limbBits a with hva
  set vb := BigInt.value limbBits b with hvb
  have hva_lt : va < 2 ^ (limbBits * numLimbs) := BigInt.value_lt ha_norm
  have hvb_lt : vb < 2 ^ (limbBits * numLimbs) := BigInt.value_lt hb_norm
  set qNat := (va + vb) / P256 with hqNat
  set rN := (va + vb) % P256 with hrN
  have hrN_lt : rN < P256 := Nat.mod_lt _ P256_pos
  have hrN_pow : rN < 2 ^ (limbBits * numLimbs) := lt_trans hrN_lt P256_lt
  have hq4 : qNat < 4 := by
    have hlt : va + vb < 4 * P256 := by
      have : (2 : ℕ) ^ (limbBits * numLimbs) < 2 * P256 := by decide
      omega
    have := (Nat.div_lt_iff_lt_mul P256_pos).mpr (by omega : va + vb < 4 * P256)
    omega
  have hqN3 : qNat ≤ 3 := by omega
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
  · -- range check: q < 4
    rw [h_wit_q, ZMod.val_natCast_of_lt (lt_trans hq4 (by decide : (4 : ℕ) < circomPrime))]
    omega
  · exact AddMod.lhs_bounds env a_var b_var a b h_input_a h_input_b ha_norm hb_norm
  · exact AddModL.rhs_bounds3 env i₀ qNat h_wit_q hqN3 (outVar_val_lt env i₀ hrv_norm)
  · rw [AddMod.polyValue_lhs env a_var b_var a b h_input_a h_input_b ha_norm hb_norm,
      AddModL.polyValue_rhs3 env i₀ qNat h_wit_q hqN3 (outVar_val_lt env i₀ hrv_norm),
      hrv_val]
    calc va + vb = P256 * qNat + rN := by
          rw [hqNat, hrN]
          exact (Nat.div_add_mod (va + vb) P256).symm
      _ = qNat * P256 + rN := by ring

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

/-- The `AddModL` formal circuit: `c ≡ a + b (mod P256)`, output normalized. -/
def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end AddModL

end Solution.Secp256k1ScalarMul
