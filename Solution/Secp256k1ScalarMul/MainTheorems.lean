import Solution.Secp256k1ScalarMul.ScalarMul
import Challenge.Instances.Secp256k1ScalarMul.Interface

/-!
# Helpers for the top-level `main` — Interface ↔ `ScalarMul` gadget bridge

`Main.lean`'s `soundness`/`completeness` proofs bridge the trusted instance
Interface (big-endian byte coordinates, `os2ip`-style `coordVal`) to the
`ScalarMul` gadget (4×64-bit little-endian limbs, `Limbs.fromLimbs`). This file
holds the pure content of that bridge:

* `coordVal_eq` — the big-endian `os2ip` fold equals `fromLimbs 8` of the
  reversed byte-value list, i.e. `Interface.coordVal = ScalarMul.coordVal`;
* `pack` — the value-level byte→limb packing (`eval` of `Main.packCoord`),
  with its normalization (`pack_normalized`), value (`pack_value`),
  canonicity (`pack_valid`) and decoding (`decodeFe_pack`) lemmas;
* `eval_packCoordE` — evaluating the expression-level packing (`packCoordE`,
  definitionally `Main.packCoord`) gives `pack` of the evaluated bytes;
* small glue: `isBool_of_val_lt_two`, `outputValid_of_valid`,
  `decodeOutput_eq`.
-/

namespace Solution.Secp256k1ScalarMul
namespace MainTheorems

open Challenge.Instances.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

/-- Every truncated-subtraction index `31 − j` hits the 32-byte coordinate. -/
theorem idx_lt (j : ℕ) : 31 - j < Interface.coordBytes := by
  simp only [Interface.coordBytes]
  omega

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

/-- `coordVal` as a little-endian positional sum: little-endian byte `j` is
big-endian byte `31 − j`. -/
theorem coordVal_eq_le_sum (v : Vector (F circomPrime) Interface.coordBytes) :
    Interface.coordVal v
      = ∑ j ∈ Finset.range 32, (v[31 - j]'(idx_lt j)).val * 2 ^ (8 * j) := by
  rw [coordVal_eq, ScalarMul.coordVal, fromLimbs_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun j => (v[31 - j]'(idx_lt j)).val * 2 ^ (8 * j)) 32]
  have hlen : ((v.toList.map ZMod.val).reverse).length = 32 := by simp
  rw [← Fin.sum_congr'
    (fun j : Fin 32 => (v[31 - j.val]'(idx_lt j.val)).val * 2 ^ (8 * j.val)) hlen]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_cast, Fin.getElem_fin]
  congr 1
  rw [List.getElem_reverse, List.getElem_map]
  simp only [List.length_map, Vector.length_toList, Vector.getElem_toList]
  rfl

/-! ## The value-level packing -/

/-- Value-level byte→limb packing: limb `k` collects big-endian bytes
`31 − (8k+t)` with weight `2^(8t)` — exactly `eval env ∘ Main.packCoord`. -/
def pack (b : Vector (F circomPrime) Interface.coordBytes) : Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    ∑ t : Fin bytesPerLimb,
      b[Interface.coordBytes - 1 - (bytesPerLimb * k.val + t.val)]'(by
          have hk := k.isLt; have ht := t.isLt
          simp only [numLimbs, bytesPerLimb, Interface.coordBytes] at hk ht ⊢
          omega)
        * ((2 ^ (8 * t.val) : ℕ) : F circomPrime)

/-- The `.val` of limb `k` of `pack b`: the byte sum does not wrap
(`< 2^64 < circomPrime`). -/
theorem pack_getElem_val (b : Vector (F circomPrime) Interface.coordBytes)
    (hb : ∀ i : Fin Interface.coordBytes, (b[i]).val < 256)
    (k : ℕ) (hk : k < numLimbs) :
    ((pack b)[k]'hk).val
      = ∑ t ∈ Finset.range 8, (b[31 - (8 * k + t)]'(idx_lt _)).val * 2 ^ (8 * t) := by
  have hcast : (pack b)[k]'hk
      = ((∑ t ∈ Finset.range 8,
          (b[31 - (8 * k + t)]'(idx_lt _)).val * 2 ^ (8 * t) : ℕ) : F circomPrime) := by
    rw [pack, Vector.getElem_ofFn,
      ← Fin.sum_univ_eq_sum_range
        (fun t => (b[31 - (8 * k + t)]'(idx_lt _)).val * 2 ^ (8 * t)) 8,
      Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rfl
  have hlt : (∑ t ∈ Finset.range 8,
      (b[31 - (8 * k + t)]'(idx_lt _)).val * 2 ^ (8 * t)) < 2 ^ 64 := by
    have h := sum_lt_pow (B := 8) (n := 8)
      (fun t : Fin 8 => (b[31 - (8 * k + t.val)]'(idx_lt _)).val)
      (fun t => hb ⟨31 - (8 * k + t.val), idx_lt _⟩)
    rw [← Fin.sum_univ_eq_sum_range
      (fun t => (b[31 - (8 * k + t)]'(idx_lt _)).val * 2 ^ (8 * t)) 8]
    calc (∑ t : Fin 8, (b[31 - (8 * k + t.val)]'(idx_lt _)).val * 2 ^ (8 * t.val))
        < 2 ^ (8 * 8) := h
      _ = 2 ^ 64 := by norm_num
  rw [hcast, ZMod.val_natCast_of_lt (lt_trans hlt ToBytes.two_pow_64_lt_circomPrime)]

/-- `pack b` is `Normalized`: each limb is a canonical 64-bit value. -/
theorem pack_normalized (b : Vector (F circomPrime) Interface.coordBytes)
    (hb : ∀ i : Fin Interface.coordBytes, (b[i]).val < 256) :
    (pack b).Normalized limbBits := by
  intro k
  rw [Fin.getElem_fin, pack_getElem_val b hb k.val k.isLt]
  have h := sum_lt_pow (B := 8) (n := 8)
    (fun t : Fin 8 => (b[31 - (8 * k.val + t.val)]'(idx_lt _)).val)
    (fun t => hb ⟨31 - (8 * k.val + t.val), idx_lt _⟩)
  rw [← Fin.sum_univ_eq_sum_range
    (fun t => (b[31 - (8 * k.val + t)]'(idx_lt _)).val * 2 ^ (8 * t)) 8]
  calc (∑ t : Fin 8, (b[31 - (8 * k.val + t.val)]'(idx_lt _)).val * 2 ^ (8 * t.val))
      < 2 ^ (8 * 8) := h
    _ = 2 ^ limbBits := by norm_num

/-- **Packing decode identity**: the limb value of `pack b` is the Interface's
big-endian `coordVal` (base-`2^8` → base-`2^64` regrouping). -/
theorem pack_value (b : Vector (F circomPrime) Interface.coordBytes)
    (hb : ∀ i : Fin Interface.coordBytes, (b[i]).val < 256) :
    (pack b).value limbBits = Interface.coordVal b := by
  rw [coordVal_eq_le_sum, BigInt.value_eq_sum]
  calc (∑ k : Fin numLimbs, ((pack b)[k]).val * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range 4,
          (∑ t ∈ Finset.range 8, (b[31 - (8 * k + t)]'(idx_lt _)).val * 2 ^ (8 * t))
            * 2 ^ (8 * 8 * k) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k =>
          (∑ t ∈ Finset.range 8, (b[31 - (8 * k + t)]'(idx_lt _)).val * 2 ^ (8 * t))
            * 2 ^ (8 * 8 * k)) 4]
        apply Finset.sum_congr rfl
        intro k _
        rw [Fin.getElem_fin, pack_getElem_val b hb k.val k.isLt]
    _ = ∑ j ∈ Finset.range (4 * 8), (b[31 - j]'(idx_lt _)).val * 2 ^ (8 * j) :=
        (ToBytes.sum_regroup 8 8 (fun j => (b[31 - j]'(idx_lt _)).val) 4).symm
    _ = ∑ j ∈ Finset.range 32, (b[31 - j]'(idx_lt _)).val * 2 ^ (8 * j) := by norm_num

/-- Canonicity: with byte-ness and the Interface bound `coordVal < p`,
`pack b` is a well-formed emulated field element. -/
theorem pack_valid (b : Vector (F circomPrime) Interface.coordBytes)
    (hb : ∀ i : Fin Interface.coordBytes, (b[i]).val < 256)
    (hlt : Interface.coordVal b < Specs.Secp256k1.p) :
    Fe.Valid (pack b) :=
  ⟨pack_normalized b hb, by rw [pack_value b hb]; exact hlt⟩

/-- Decoding: `pack b` decodes to the Interface's decoded coordinate. -/
theorem decodeFe_pack (b : Vector (F circomPrime) Interface.coordBytes)
    (hb : ∀ i : Fin Interface.coordBytes, (b[i]).val < 256) :
    decodeFe (pack b) = Interface.decodeCoord b := by
  rw [decodeFe, pack_value b hb, Interface.decodeCoord]

/-! ## Expression-level packing -/

/-- Definitionally equal copy of `Main.packCoord` (which lives downstream of
this file), so the evaluation lemma `eval_packCoordE` can be stated here. -/
def packCoordE (v : Vector (Expression (F circomPrime)) Interface.coordBytes) :
    Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    Fin.foldl bytesPerLimb (fun acc t =>
      acc + v[Interface.coordBytes - 1 - (bytesPerLimb * k.val + t.val)]'(by
          have hk := k.isLt; have ht := t.isLt
          simp only [numLimbs, bytesPerLimb, Interface.coordBytes] at hk ht ⊢
          omega)
        * (((2 ^ (8 * t.val) : ℕ) : F circomPrime) : Expression (F circomPrime)))
      0

/-- Evaluating the expression-level packing gives the value-level packing of
the evaluated bytes. -/
theorem eval_packCoordE (env : Environment (F circomPrime))
    (v : Vector (Expression (F circomPrime)) Interface.coordBytes) :
    Vector.map (Expression.eval env) (packCoordE v)
      = pack (Vector.map (Expression.eval env) v) := by
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map]
  simp only [packCoordE, pack, Vector.getElem_ofFn]
  rw [ToBytes.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Expression.eval, Vector.getElem_map]

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
end Solution.Secp256k1ScalarMul
