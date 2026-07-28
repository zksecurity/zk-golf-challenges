import Solution.Blake3CompressGF2Canonical.Round
import Mathlib.Tactic.IntervalCases

/-!
# Evaluation lemmas for pure BLAKE3 wiring

These lemmas isolate the only proofs about parsing, message permutation, and
final XOR wiring. The circuit hierarchy can then use exact functional specs.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.Instances.Blake3CompressGF2Canonical.Interface.Blake3Bits
open Challenge.F2Bits

theorem eval_splitWords (env : Environment (F p2)) (n : ℕ)
    (v : Vector (Expression (F p2)) (32 * n)) :
    Vector.map (fun w => Vector.map (Expression.eval env) w) (splitWords n v) =
      splitWords n (Vector.map (Expression.eval env) v) := by
  refine Vector.ext fun i hi => ?_
  refine Vector.ext fun j hj => ?_
  simp [splitWords, circuit_norm]

theorem eval_flattenWords (env : Environment (F p2)) {n : ℕ}
    (v : Vector (Word (Expression (F p2))) n) :
    Vector.map (Expression.eval env) (flattenWords v) =
      flattenWords (Vector.map (fun w => Vector.map (Expression.eval env) w) v) := by
  refine Vector.ext fun i hi => ?_
  simp [flattenWords, circuit_norm]

theorem eval_constWord (env : Environment (F p2)) (x : ℕ) :
    Vector.map (Expression.eval env) (constWord (α := Expression (F p2)) x) =
      constWord (α := F p2) x := by
  refine Vector.ext fun i hi => ?_
  by_cases h : x.testBit i = true <;>
    simp [constWord, h, circuit_norm]

theorem eval_initialState (env : Environment (F p2))
    (w : Vector (Word (Expression (F p2))) 28) :
    Vector.map (Expression.eval env) (initialState w) =
      initialState (Vector.map (fun x => Vector.map (Expression.eval env) x) w) := by
  refine Vector.ext fun i hi => ?_
  simp only [initialState, Vector.getElem_map, Vector.getElem_ofFn]
  split
  · simp [circuit_norm]
  · split
    · have hc := Vector.ext_iff.mp
        (eval_constWord env Specs.Blake3.iv[i / 32 - 8]) (i % 32)
        (Nat.mod_lt _ (by norm_num))
      simpa only [Vector.getElem_map, atWord] using hc
    · simp [circuit_norm]

theorem eval_initialBlock (env : Environment (F p2))
    (w : Vector (Word (Expression (F p2))) 28) :
    Vector.map (Expression.eval env) (initialBlock w) =
      initialBlock (Vector.map (fun x => Vector.map (Expression.eval env) x) w) := by
  refine Vector.ext fun i hi => ?_
  simp [initialBlock, circuit_norm]

theorem eval_permute (env : Environment (F p2))
    (m : Block (Expression (F p2))) :
    Vector.map (fun w => Vector.map (Expression.eval env) w) (permute m) =
      permute (Vector.map (fun w => Vector.map (Expression.eval env) w) m) := by
  refine Vector.ext fun i hi => ?_
  interval_cases i <;> simp [permute, circuit_norm]

theorem eval_permuteState (env : Environment (F p2))
    (m : State (Expression (F p2))) :
    Vector.map (Expression.eval env) (permuteState m) =
      permuteState (Vector.map (Expression.eval env) m) := by
  rw [permuteState, eval_flattenWords, eval_permute, eval_splitWords]
  rfl

theorem eval_finalizeState (env : Environment (F p2))
    (v initial : State (Expression (F p2))) :
    Vector.map (Expression.eval env) (finalizeState v initial) =
      finalizeState (Vector.map (Expression.eval env) v)
        (Vector.map (Expression.eval env) initial) := by
  refine Vector.ext fun i hi => ?_
  simp only [finalizeState, Vector.getElem_map, Vector.getElem_ofFn]
  split <;> simp [circuit_norm]

end Solution.Blake3CompressGF2Canonical
