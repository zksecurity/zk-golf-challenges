import Solution.SHA256.ScheduleStep
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^33)]

namespace Solution.SHA256

/-!
# Helper definitions and lemmas for `MessageSchedule`

The variable- and value-level schedule descriptions (`varSchedule` / `valSchedule`)
and the lemmas relating the `foldlRange` accumulator and the spec to them. The
per-step circuit now lives in the `ScheduleStep` gadget and `MessageSchedule.main`
inlines the fold over `subcircuit ScheduleStep.circuit`, so the bridges below are
phrased against that gadget. The gadget file keeps the six required declarations.
-/

namespace MessageSchedule

/-- Variable-level schedule after `k` expansion steps. Used as the explicit description
    of the foldlRange accumulator, mirroring `SHA256Rounds.stateVar`. -/
def varSchedule (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p))) :
    ℕ → SHA256Schedule (Expression (F p))
  | 0 =>
    Vector.append input_var_block
      (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))
  | k + 1 =>
    if h : k < 48 then
      (varSchedule i₀ input_var_block k).set
        (k + 16) (varFromOffset (fields 32) (i₀ + k * 227 + 194)) (by omega)
    else
      varSchedule i₀ input_var_block k

/-- Value-level schedule after `k` expansion steps. -/
def valSchedule (input_block : Vector ℕ 16) : ℕ → Vector ℕ 64
  | 0 => Vector.mapFinRange 64 fun i => if h : i.val < 16 then input_block.get ⟨i.val, h⟩ else 0
  | k + 1 =>
    if h : k < 48 then
      let prev := valSchedule input_block k
      let wj := _root_.add32
        (_root_.add32 (Specs.SHA256.lowerSigma1 prev[k + 16 - 2]) prev[k + 16 - 7])
        (_root_.add32 (Specs.SHA256.lowerSigma0 prev[k + 16 - 15]) prev[k + 16 - 16])
      prev.set (k + 16) wj (by omega)
    else
      valSchedule input_block k

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 33)] in
/-- `Specs.SHA256.messageSchedule` equals our `valSchedule` at index 48. -/
lemma messageSchedule_eq_valSchedule (input_block : Vector ℕ 16) :
    Specs.SHA256.messageSchedule input_block = valSchedule input_block 48 := by
  simp only [Specs.SHA256.messageSchedule]
  -- Generic step body, independent of the foldl bound, so the IH on `k` matches
  -- the new occurrence in `Fin.foldl_succ_last`.
  set body : Vector ℕ 64 → ℕ → Vector ℕ 64 := fun w n =>
    if h : n < 48 then
      have hj   : n + 16     < 64 := by omega
      let wj := _root_.add32
        (_root_.add32 (Specs.SHA256.lowerSigma1 w[n + 16 - 2]) w[n + 16 - 7])
        (_root_.add32 (Specs.SHA256.lowerSigma0 w[n + 16 - 15]) w[n + 16 - 16])
      w.set (n + 16) wj hj
    else w with hbody_def
  set init : Vector ℕ 64 :=
    Vector.mapFinRange 64 fun i => if h : i.val < 16 then input_block.get ⟨i.val, h⟩ else 0
  -- Rephrase RHS bodies in terms of `body`.
  have hspec : Fin.foldl 48 (fun w (i : Fin 48) =>
      w.set (i.val + 16)
        (_root_.add32 (_root_.add32 (Specs.SHA256.lowerSigma1 w[i.val + 16 - 2]) w[i.val + 16 - 7])
          (_root_.add32 (Specs.SHA256.lowerSigma0 w[i.val + 16 - 15]) w[i.val + 16 - 16]))
        (by have := i.isLt; omega)) init =
      Fin.foldl 48 (fun w (i : Fin 48) => body w i.val) init := by
    congr 1; funext w i
    have hi : i.val < 48 := i.isLt
    simp only [hbody_def, dif_pos hi]
  rw [hspec]
  suffices h : ∀ k (hk : k ≤ 48),
      Fin.foldl k (fun w (i : Fin k) => body w i.val) init =
        valSchedule input_block k by
    have h48 := h 48 (le_refl 48)
    convert h48 using 1
  intro k hk
  induction k with
  | zero => simp [valSchedule, Fin.foldl_zero, init]
  | succ k ih =>
    rw [Fin.foldl_succ_last, valSchedule]
    have hk' : k ≤ 48 := by omega
    specialize ih hk'
    rw [show (fun w (i : Fin k) => body w i.castSucc.val) =
           (fun w (i : Fin k) => body w i.val) from rfl, ih]
    simp only [Fin.val_last, hbody_def, dif_pos (show k < 48 from by omega)]

/-- The localLength of `ScheduleStep.circuit` is the constant 227. -/
@[simp] lemma scheduleStep_localLength (b : ScheduleStep.Inputs (Expression (F p))) :
    ScheduleStep.circuit.localLength b = 227 := rfl

/-- The output of `ScheduleStep.circuit` at offset `n` is the word at relative offset 194. -/
@[simp] lemma scheduleStep_output (b : ScheduleStep.Inputs (Expression (F p))) (n : ℕ) :
    ScheduleStep.circuit.output b n = varFromOffset (fields 32) (n + 194) := rfl

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 33)] in
/-- The 48-step `Fin.foldl` of the (circuit_norm–reduced) variable-level schedule body
    equals `varSchedule 48`. Used by the elaborated instance. -/
lemma finFoldl_eq_varSchedule_48 (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p))) :
    Fin.foldl 48
      (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin 48) =>
        acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 227 + 194))
          (by have := i.isLt; omega))
      (Vector.append input_var_block
        (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
      varSchedule i₀ input_var_block 48 := by
  suffices h : ∀ k (hk : k ≤ 48),
      Fin.foldl k
        (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
          acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 227 + 194))
            (by have := i.isLt; omega))
        (Vector.append input_var_block
          (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
        (show Vector (fields 32 (Expression (F p))) (16 + 48) from
          varSchedule i₀ input_var_block k) by
    have := h 48 (le_refl 48)
    convert this using 2
  intro k hk
  induction k with
  | zero => simp [varSchedule, Fin.foldl_zero]
  | succ k ih =>
    have hk' : k ≤ 48 := by omega
    have hk'' : k < 48 := by omega
    specialize ih hk'
    rw [Fin.foldl_succ_last]
    rw [show Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            acc.set (i.castSucc.val + 16) (varFromOffset (fields 32) (i₀ + i.castSucc.val * 227 + 194))
              (by have := i.isLt; omega))
            _ =
        Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 227 + 194))
              (by have := i.isLt; omega))
            _ from rfl, ih]
    simp only [Fin.val_last]
    rw [varSchedule, dif_pos hk'']

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 48` equals `varSchedule i₀ input_var k`.
    Phrased against the inlined fold body (the `circuit_norm`-reduced
    `subcircuit ScheduleStep.circuit` then `set`). -/
lemma foldlAcc_eq_varSchedule (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p)))
    (k : ℕ) (h : k < 48) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 48)
      (fun (w : SHA256Schedule (Expression (F p))) (i : Fin 48) (n : ℕ) =>
        (Vector.set w (i.val + 16)
            (ScheduleStep.circuit.output
              ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
               w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩ n)
            (by omega),
          [Operation.subcircuit (ScheduleStep.circuit.toSubcircuit n
            ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
             w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩)]))
      (Vector.append input_var_block (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p)))))
      ⟨k, h⟩ =
        varSchedule i₀ input_var_block k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  induction k with
  | zero => simp [varSchedule, Fin.foldl_zero]
  | succ k ih =>
    have hk : k < 48 := by omega
    specialize ih hk
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, varSchedule, dif_pos hk]
    simp only [Circuit.output, Circuit.localLength, scheduleStep_output, scheduleStep_localLength,
      circuit_norm]

end MessageSchedule
end Solution.SHA256
end
