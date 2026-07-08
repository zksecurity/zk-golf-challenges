import Solution.Secp256k1ScalarMulFixedBase.ScalarMul
import Challenge.Instances.Secp256k1ScalarMulFixedBase.Interface

/-!
# Helpers for the top-level `main` — Interface ↔ `ScalarMul` gadget bridge

`Main.lean`'s `soundness`/`completeness` proofs bridge the trusted instance
Interface (big-endian byte coordinates, `os2ip`-style `coordVal`) to the
`ScalarMul` gadget (4×64-bit little-endian limbs) at the **fixed** base point
`G`. This file holds the pure content of that bridge:

* `coordVal_eq` — the big-endian `os2ip` fold equals `fromLimbs 8` of the
  reversed byte-value list, i.e. `Interface.coordVal = ScalarMul.coordVal`;
* the constant limbs of the generator (`gxConst`/`gyConst`) with their
  evaluation, validity and decoding lemmas — the fixed-base analogue of the
  variable-base `pack` machinery, but with no in-circuit packing (the base
  point is a compile-time constant);
* `G_onCurve` — `G` lies on the curve, proved kernel-checkably (a `Nat`
  modular identity discharged by `decide`, never `native_decide`);
* small glue: `isBool_of_val_lt_two`, `outputValid_of_valid`,
  `decodeOutput_eq`.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace MainTheorems

open Challenge.Instances.Secp256k1ScalarMulFixedBase
open Solution.Secp256k1ScalarMulFixedBase.Limbs

/-! ## `coordVal`: big-endian fold vs little-endian limbs -/

/-- The big-endian base-256 fold equals `fromLimbs 8` of the reversed digit
list (plain positional reindexing; no bounds needed). -/
theorem foldl_base256_eq_fromLimbs (l : List ℕ) :
    l.foldl (fun acc x => acc * 256 + x) 0 = Limbs.fromLimbs 8 l.reverse := by
  rw [Limbs.fromLimbs, List.foldr_reverse]
  congr 1
  funext acc x
  norm_num [Nat.add_comm]

/-- The Interface's `os2ip`-style `coordVal` equals the gadget's
`fromLimbs`-of-reversed-vals `coordVal`. -/
theorem coordVal_eq (v : Vector (F circomPrime) Interface.coordBytes) :
    Interface.coordVal v = ScalarMul.coordVal v := by
  rw [Interface.coordVal, ScalarMul.coordVal, ← foldl_base256_eq_fromLimbs,
    List.foldl_map]
  rfl

/-! ## The fixed generator as constant limbs -/

/-- The generator's x-coordinate as a natural number (SEC 2, `G.x`). -/
def gxNat : ℕ := 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798

/-- The generator's y-coordinate as a natural number (SEC 2, `G.y`). -/
def gyNat : ℕ := 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

/-- Constant limbs of `G.x` (a compile-time value, not a witnessed input). -/
def gxConst : Var Emu (F circomPrime) := emuConst gxNat

/-- Constant limbs of `G.y`. -/
def gyConst : Var Emu (F circomPrime) := emuConst gyNat

/-- `gxNat`, as an element of the base field, is `G.x`. -/
lemma gxNat_cast : ((gxNat : ℕ) : Specs.Secp256k1.Fp) = Specs.Secp256k1.G.x := by rfl

/-- `gyNat`, as an element of the base field, is `G.y`. -/
lemma gyNat_cast : ((gyNat : ℕ) : Specs.Secp256k1.Fp) = Specs.Secp256k1.G.y := by rfl

lemma eval_gxConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) gxConst = emuOfNat gxNat :=
  DivOrZero.eval_emuConst env gxNat

lemma eval_gyConst (env : Environment (F circomPrime)) :
    Vector.map (Expression.eval env) gyConst = emuOfNat gyNat :=
  DivOrZero.eval_emuConst env gyNat

/-- The evaluated `gxConst` is a canonical emulated field element. -/
lemma fe_valid_gxConst (env : Environment (F circomPrime)) :
    Fe.Valid (Vector.map (Expression.eval env) gxConst) := by
  rw [eval_gxConst]; exact DivOrZero.fe_valid_emuOfNat (by decide)

lemma fe_valid_gyConst (env : Environment (F circomPrime)) :
    Fe.Valid (Vector.map (Expression.eval env) gyConst) := by
  rw [eval_gyConst]; exact DivOrZero.fe_valid_emuOfNat (by decide)

/-- The evaluated `gxConst` decodes to `G.x`. -/
lemma decodeFe_gxConst (env : Environment (F circomPrime)) :
    decodeFe (Vector.map (Expression.eval env) gxConst) = Specs.Secp256k1.G.x := by
  rw [eval_gxConst, decodeFe, DivOrZero.value_emuOfNat (by decide), gxNat_cast]

lemma decodeFe_gyConst (env : Environment (F circomPrime)) :
    decodeFe (Vector.map (Expression.eval env) gyConst) = Specs.Secp256k1.G.y := by
  rw [eval_gyConst, decodeFe, DivOrZero.value_emuOfNat (by decide), gyNat_cast]

/-! ## `G` is on the curve -/

/-- The generator lies on the curve. Proved from the `Nat` modular identity
`G.y² ≡ G.x³ + 7 (mod p)`, discharged by `decide` (kernel `Nat` arithmetic,
never `native_decide`). -/
lemma G_onCurve :
    Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve Specs.Secp256k1.G := by
  have key : gyNat ^ 2 % Specs.Secp256k1.p
      = (gxNat ^ 3 + 7) % Specs.Secp256k1.p := by decide
  show Specs.Secp256k1.G.y ^ 2
    = Specs.Secp256k1.G.x ^ 3 + Specs.Secp256k1.curve.a * Specs.Secp256k1.G.x
        + Specs.Secp256k1.curve.b
  rw [show Specs.Secp256k1.curve.a = 0 from rfl,
      show Specs.Secp256k1.curve.b = (7 : Specs.Secp256k1.Fp) from rfl,
      zero_mul, add_zero, ← gxNat_cast, ← gyNat_cast]
  have hcast : ((gyNat ^ 2 : ℕ) : Specs.Secp256k1.Fp)
      = ((gxNat ^ 3 + 7 : ℕ) : Specs.Secp256k1.Fp) := by
    rw [ZMod.natCast_eq_natCast_iff]; exact key
  rwa [Nat.cast_pow, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at hcast

/-! ## Small glue lemmas -/

/-- A field element with `val < 2` is boolean. -/
theorem isBool_of_val_lt_two {x : F circomPrime} (h : x.val < 2) : IsBool x := by
  have h01 : x.val = 0 ∨ x.val = 1 := by omega
  rcases h01 with h0 | h1
  · exact Or.inl ((ZMod.val_eq_zero x).mp h0)
  · refine Or.inr ?_
    have hx := ZMod.natCast_zmod_val x
    rw [← hx, h1, Nat.cast_one]

/-- The gadget's output validity gives the Interface's `OutputValid` on the
re-wrapped output, via the `coordVal` identity. -/
theorem outputValid_of_valid {out : ScalarMul.Outputs (F circomPrime)}
    (h : out.Valid) :
    Interface.OutputValid { x := out.x, y := out.y, isInf := out.isInf } := by
  obtain ⟨hx, hy, hb, hvx, hvy, hz⟩ := h
  exact ⟨hx, hy, hb,
    by rw [show Interface.coordVal out.x = ScalarMul.coordVal out.x from coordVal_eq _]
       exact hvx,
    by rw [show Interface.coordVal out.y = ScalarMul.coordVal out.y from coordVal_eq _]
       exact hvy,
    hz⟩

/-- The Interface decodes the re-wrapped output to the same group point as the
gadget. -/
theorem decodeOutput_eq (out : ScalarMul.Outputs (F circomPrime)) :
    Interface.decodeOutput { x := out.x, y := out.y, isInf := out.isInf }
      = ScalarMul.decodeOutput out := by
  rw [Interface.decodeOutput, ScalarMul.decodeOutput]
  by_cases h : out.isInf = 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Interface.decodeCoord, Interface.decodeCoord,
      coordVal_eq, coordVal_eq]

end MainTheorems
end Solution.Secp256k1ScalarMulFixedBase
