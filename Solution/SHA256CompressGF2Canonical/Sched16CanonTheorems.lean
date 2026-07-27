import Solution.SHA256CompressGF2Canonical.ScheduleStepCanon
import Solution.SHA256CompressGF2.Sched16Theorems

/-!
# Private fold bridges for `Sched16Canon`
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Sched16Canon

/-- Explicit `ConstantLength` for the 16-step canonical schedule fold body
    (218 witnesses per step). -/
def constantLength :
    Circuit.ConstantLength (fun (x : Vector (fields 32 (Expression (F p2))) 32 × Fin 16) => do
      let ui ← ScheduleStepCanon.circuit (c128 (x.1[x.2.val]'(by omega)) (x.1[x.2.val + 1]'(by omega))
        (x.1[x.2.val + 9]'(by omega)) (x.1[x.2.val + 14]'(by omega)))
      return x.1.set (16 + x.2.val) ui (by omega)) where
  localLength := 218
  localLength_eq _ _ := by
    simp [circuit_norm, ScheduleStepCanon.circuit, ScheduleStepCanon.elaborated]

/-- The `k`-th step's witnessed output word: a fresh 32-bit witness vector at the
    canonical step's Pin32 offset (relative 186 within the 218-witness step). -/
def stepWord (i₀ k : ℕ) : Var (fields 32) (F p2) :=
  varFromOffset (fields 32) (i₀ + k * 218 + 186)

/-- `ScheduleStepCanon.circuit`'s output word is a fresh witness at relative offset 186. -/
@[simp] lemma scheduleStep_output (b : Var (fields 128) (F p2)) (n : ℕ) :
    ScheduleStepCanon.circuit.output b n = varFromOffset (fields 32) (n + 186) := rfl

/-- `ScheduleStepCanon.circuit`'s localLength is the constant 218. -/
@[simp] lemma scheduleStep_localLength (b : Var (fields 128) (F p2)) :
    ScheduleStepCanon.circuit.localLength b = 218 := rfl

/-- Variable-level 32-word buffer after `k` steps. -/
def varBuf (i₀ : ℕ) (v : Var (fields 512) (F p2)) :
    ℕ → Vector (fields 32 (Expression (F p2))) 32
  | 0 =>
    (Vector.ofFn fun j : Fin 16 => q512 v j.val) ++
      Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2)))
  | k + 1 =>
    if h : k < 16 then
      (varBuf i₀ v k).set (16 + k) (stepWord i₀ k) (by omega)
    else varBuf i₀ v k

lemma finFoldl_eq_varBuf (i₀ : ℕ) (v : Var (fields 512) (F p2)) :
    Fin.foldl 16
      (fun (w : Vector (fields 32 (Expression (F p2))) 32) (i : Fin 16) =>
        w.set (16 + i.val) (stepWord i₀ i.val) (by omega))
      ((Vector.ofFn fun j : Fin 16 => q512 v j.val) ++
        Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2)))) =
      varBuf i₀ v 16 := by
  suffices h : ∀ k (hk : k ≤ 16),
      Fin.foldl k
        (fun (w : Vector (fields 32 (Expression (F p2))) 32) (i : Fin k) =>
          w.set (16 + i.val) (stepWord i₀ i.val) (by have := i.isLt; omega))
        ((Vector.ofFn fun j : Fin 16 => q512 v j.val) ++
          Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2)))) =
        varBuf i₀ v k by
    exact h 16 (le_refl 16)
  intro k hk
  induction k with
  | zero => simp [varBuf, Fin.foldl_zero]
  | succ k ih =>
    have hk16 : k < 16 := by omega
    rw [Fin.foldl_succ_last]
    rw [show Fin.foldl k
          (fun (w : Vector (fields 32 (Expression (F p2))) 32) (i : Fin k) =>
            w.set (16 + i.castSucc.val) (stepWord i₀ i.castSucc.val)
              (by have := i.isLt; omega)) _
        = Fin.foldl k
          (fun (w : Vector (fields 32 (Expression (F p2))) 32) (i : Fin k) =>
            w.set (16 + i.val) (stepWord i₀ i.val)
              (by have := i.isLt; omega)) _ from rfl, ih (by omega)]
    simp only [Fin.val_last]
    rw [varBuf, dif_pos hk16]

theorem varBuf_out (i₀ : ℕ) (v : Var (fields 512) (F p2)) (j : ℕ) (hj : j < 16) :
    ∀ (m : ℕ), j < m → m ≤ 16 → (varBuf i₀ v m)[16 + j]'(by omega) = stepWord i₀ j := by
  intro m
  induction m with
  | zero => intro h _; exact absurd h (by omega)
  | succ m ih =>
    intro hjm hm
    have hm16 : m < 16 := by omega
    have hvb : varBuf i₀ v (m + 1)
        = (varBuf i₀ v m).set (16 + m) (stepWord i₀ m) (by omega) := by
      conv_lhs => rw [varBuf]
      rw [dif_pos hm16]
    rw [hvb]
    by_cases hjm' : j = m
    · subst hjm'; rw [Vector.getElem_set_self]
    · rw [Vector.getElem_set_ne (by omega) (by omega) (by omega)]
      exact ih (by omega) (by omega)

lemma foldlAcc_eq_varBuf (i₀ : ℕ) (v : Var (fields 512) (F p2)) (k : ℕ) (h : k < 16) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 16)
      (fun (w : Vector (fields 32 (Expression (F p2))) 32) (i : Fin 16) (n : ℕ) =>
        (Vector.set w (16 + i.val)
            (ScheduleStepCanon.circuit.output
              (c128 (w[i.val]'(by omega)) (w[i.val + 1]'(by omega))
                (w[i.val + 9]'(by omega)) (w[i.val + 14]'(by omega))) n) (by omega),
          [Operation.subcircuit (ScheduleStepCanon.circuit.toSubcircuit n
            (c128 (w[i.val]'(by omega)) (w[i.val + 1]'(by omega))
              (w[i.val + 9]'(by omega)) (w[i.val + 14]'(by omega))))]))
      ((Vector.ofFn fun j : Fin 16 => q512 v j.val) ++
        Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))
      ⟨k, h⟩ =
        varBuf i₀ v k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  induction k with
  | zero => simp [varBuf, Fin.foldl_zero]
  | succ k ih =>
    have hk : k < 16 := by omega
    specialize ih hk
    have hvb : varBuf i₀ v (k + 1) = (varBuf i₀ v k).set (16 + k) (stepWord i₀ k) (by omega) := by
      conv_lhs => rw [varBuf]
      rw [dif_pos hk]
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last, Circuit.output, Circuit.localLength,
      scheduleStep_output, scheduleStep_localLength, circuit_norm] at ih ⊢
    rw [ih]
    exact hvb.symm

/-- The fold body allocates exactly the canonical step's 218 witnesses (spelled as
the `do`-block that `main` writes, so the loop-peeling `simp` set can use it). -/
lemma stepBody_localLength (w : Vector (Var (fields 32) (F p2)) 32) (i : Fin 16) (n : ℕ) :
    (do
      let ui ← subcircuit ScheduleStepCanon.circuit (c128 (w[i.val]'(by omega))
        (w[i.val + 1]'(by omega)) (w[i.val + 9]'(by omega)) (w[i.val + 14]'(by omega)))
      pure (w.set (16 + i.val) ui (by omega))).localLength n = 218 := rfl

/-- `foldlAcc` bridge against the `do`-block body, as the loop-peeling lemma
presents the fold. -/
lemma foldlAcc_eq_varBuf_do (i₀ : ℕ) (v : Var (fields 512) (F p2)) (k : ℕ) (h : k < 16) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 16)
      (fun (w : Vector (Var (fields 32) (F p2)) 32) (i : Fin 16) => do
        let ui ← subcircuit ScheduleStepCanon.circuit (c128 (w[i.val]'(by omega))
          (w[i.val + 1]'(by omega)) (w[i.val + 9]'(by omega)) (w[i.val + 14]'(by omega)))
        pure (w.set (16 + i.val) ui (by omega)))
      ((Vector.ofFn fun j : Fin 16 => q512 v j.val) ++
        Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))
      ⟨k, h⟩ = varBuf i₀ v k :=
  foldlAcc_eq_varBuf i₀ v k h

/-- A canonical step's produced word is a fresh 32-cell witness block inside it. -/
theorem eval_stepWord_of_agreesBelow (i₀ k : ℕ) {kk : ℕ} (hk : i₀ + k * 218 + 218 ≤ kk)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow kk env') :
    eval env (stepWord i₀ k) = eval env' (stepWord i₀ k) := by
  unfold stepWord
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

/-- Every cell of the buffer after `k` steps is either an input word or one of the
`k` witness blocks already allocated, so it is determined below `i₀ + k * 218`. -/
theorem eval_varBuf_getElem_of_agreesBelow (i₀ : ℕ) (v : Var (fields 512) (F p2))
    {kk : ℕ} {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow kk env') (h_input : eval env v = eval env' v) :
    ∀ (k : ℕ), i₀ + k * 218 ≤ kk → ∀ (j : ℕ) (hj : j < 32),
      eval env ((varBuf i₀ v k)[j]'hj) = eval env' ((varBuf i₀ v k)[j]'hj) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    by_cases hj16 : j < 16
    · rw [show (varBuf i₀ v 0)[j]'hj = q512 v j from by
            show ((Vector.ofFn fun jj : Fin 16 => q512 v jj.val) ++ _)[j]'hj = _
            rw [Vector.getElem_append_left hj16, Vector.getElem_ofFn]]
      exact eval_q512_congr h_input j
    · rw [show (varBuf i₀ v 0)[j]'hj
              = Vector.replicate 32 (0 : Expression (F p2)) from by
            show ((Vector.ofFn fun jj : Fin 16 => q512 v jj.val) ++
              Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))[j]'hj = _
            rw [Vector.getElem_append_right hj (by omega), Vector.getElem_replicate]]
      refine eval_fields_of_getElem fun i hi => ?_
      rw [Vector.getElem_replicate]
      rfl
  | succ k ih =>
    intro hkk j hj
    rcases (by omega : k < 16 ∨ 16 ≤ k) with hk16 | hk16
    · have hvb : varBuf i₀ v (k + 1)
          = (varBuf i₀ v k).set (16 + k) (stepWord i₀ k) (by omega) := by
        conv_lhs => rw [varBuf]
        rw [dif_pos hk16]
      rw [hvb]
      by_cases hjk : j = 16 + k
      · subst hjk
        rw [Vector.getElem_set_self]
        exact eval_stepWord_of_agreesBelow i₀ k (by omega) h_agree
      · rw [Vector.getElem_set_ne (by omega) hj (by omega)]
        exact ih (by omega) j hj
    · have hvb : varBuf i₀ v (k + 1) = varBuf i₀ v k := by
        conv_lhs => rw [varBuf]
        rw [dif_neg (by omega)]
      rw [hvb]
      exact ih (by omega) j hj

end Sched16Canon

end Solution.SHA256CompressGF2
