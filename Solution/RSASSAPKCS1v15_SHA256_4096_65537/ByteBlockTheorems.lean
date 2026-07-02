import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Bytes
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesLemmas
import Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface

/-!
# Supporting lemmas for the `ByteBlock` assertion

Gadget-private helpers for `ByteBlock.lean`. `ByteBlock.main` inlines its two
constraint loops directly:

* the booleanity loop `Circuit.forEach bits (fun b => assertZero (b * (b - 1)))`,
* the digest-consistency loop `Circuit.forEach (Vector.ofFn fun dj => bytes[dj] -
  byteFromBits bits (digestBitIndex dj 0)) assertZero`.

The lemmas below distribute `Expression.eval` over subtraction, turn the
simplified per-bit booleanity constraint into `.val < 2`, and turn the per-byte
zero facts into the `DigestConsistent` predicate.

This file does not depend on `MainTheorems`/`ModExp`/`MulMod`/`Cost`/`Main`: it is
a leaf relative to those.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace ByteBlock

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open BytesLemmas

/-- `Expression.eval` distributes over subtraction (without unfolding either
operand — avoids recursing into `Fin.foldl` sub-expressions). -/
theorem eval_sub (env : Environment (F circomPrime)) (a b : Expression (F circomPrime)) :
    Expression.eval env (a - b) = Expression.eval env a - Expression.eval env b := by
  show Expression.eval env (Expression.add a (Expression.mul (Expression.const (-1)) b))
      = Expression.eval env a - Expression.eval env b
  rw [eval_add, eval_mul]
  show Expression.eval env a + (-1) * Expression.eval env b = _
  ring

/-- The per-bit booleanity constraint `eval(bit) · (eval(bit) + (−1)) = 0` (the
simplified form `circuit_proof_start` leaves of the inlined booleanity loop)
forces each evaluated bit to satisfy `.val < 2`. -/
theorem val_lt_two_of_holds {n : ℕ}
    (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) n)
    (h : ∀ i : Fin n,
      Expression.eval env (bits[i.val]'i.isLt) * (Expression.eval env (bits[i.val]'i.isLt) + -1) = 0) :
    ∀ (i : ℕ) (hi : i < n), (Expression.eval env (bits[i]'hi)).val < 2 := by
  intro i hi
  have hz := h ⟨i, hi⟩
  have hz' : Expression.eval env (bits[i]'hi) * (Expression.eval env (bits[i]'hi) - 1) = 0 := by
    rw [sub_eq_add_neg]; exact hz
  exact IsBool.val_lt_two (IsBool.iff_mul_sub_one.mpr hz')

/-- Turn the per-byte zero facts into the `DigestConsistent` predicate. -/
theorem digestConsistent_of_facts
    (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) digestBytesLen)
    (digBits : Vector (Expression (F circomPrime)) 256)
    (hbool : ∀ (i : ℕ) (h : i < 256), (Expression.eval env (digBits[i]'h)).val < 2)
    (hz : ∀ (dj : ℕ) (hdj : dj < digestBytesLen),
      Expression.eval env ((digBytes[dj]'hdj) - byteFromBits digBits (digestBitIndex dj 0)) = 0) :
    DigestConsistent env digBytes digBits := by
  intro dj hdj
  have hzj := hz dj hdj
  rw [eval_sub, sub_eq_zero] at hzj
  have hbase : digestBitIndex dj 0 + 8 ≤ 256 := by
    simp only [digestBitIndex]; omega
  have hbf := byteFromBits_val_gen (n := 256) env digBits (digestBitIndex dj 0) hbase hbool
  have hsum : (∑ t : Fin 8,
        (Expression.eval env (digBits[digestBitIndex dj 0 + t.val]'(by have := t.isLt; omega))).val * 2 ^ t.val)
      = ∑ t : Fin 8, (Expression.eval env
          (digBits[digestBitIndex dj t.val]'(by have := t.isLt; simp only [digestBitIndex]; omega))).val * 2 ^ t.val := by
    apply Finset.sum_congr rfl
    intro t _
    rw [getElem_congr_idx (show digestBitIndex dj 0 + t.val = digestBitIndex dj t.val from by
      simp [digestBitIndex])]
  calc (Expression.eval env (digBytes[dj]'hdj)).val
      = (Expression.eval env (byteFromBits digBits (digestBitIndex dj 0))).val := by rw [hzj]
    _ = _ := by rw [hbf, hsum]

end ByteBlock
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
