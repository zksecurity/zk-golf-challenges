import Solution.SHA256CompressGF2.ScheduleStep

/-!
# Private helpers for `Sched16`
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

/-- Word `k` of a 512-bit vector. -/
def q512 (v : Var (fields 512) (F p2)) (k : ℕ) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => b512 v (32 * k + i.val)

/-- Concatenate 16 32-bit words into 512 bits. -/
def c512 (w : Fin 16 → Var (fields 32) (F p2)) : Var (fields 512) (F p2) :=
  Vector.ofFn fun i : Fin 512 => b32 (w ⟨i.val / 32, by omega⟩) i.val

/-- Word selector for 16 named words. -/
def c512sel (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : Var (fields 32) (F p2)) : ℕ → Var (fields 32) (F p2)
  | 0 => u0
  | 1 => u1
  | 2 => u2
  | 3 => u3
  | 4 => u4
  | 5 => u5
  | 6 => u6
  | 7 => u7
  | 8 => u8
  | 9 => u9
  | 10 => u10
  | 11 => u11
  | 12 => u12
  | 13 => u13
  | 14 => u14
  | _ => u15

/-- Concatenate 16 words into 512 bits (named args). -/
def c512x (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : Var (fields 32) (F p2)) : Var (fields 512) (F p2) :=
  Vector.ofFn fun i : Fin 512 => b32 (c512sel u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 (i.val / 32)) i.val

theorem toNat_eval_q512 (env : Environment (F p2)) (v : Var (fields 512) (F p2)) (k : ℕ)
    (hk : 32 * k + 32 ≤ 512) :
    toNat (Vector.map (Expression.eval env) (q512 v k)) = wordAt 32 (Vector.map (Expression.eval env) v) k := by
  rw [← wordAt_map_eval_eq_toNat v (q512 v k) k hk]
  intro j hj
  unfold q512 b512
  rw [Vector.getElem_ofFn]
  have hlt : 32 * k + j < 512 := by omega
  simp only [Nat.mod_eq_of_lt hlt]

/-! ## `eval`-agreement congruences for the schedule assembly maps -/

section EvalCongr

variable {env env' : ProverEnvironment (F p2)}

theorem eval_q512_congr {v : Var (fields 512) (F p2)} (h : eval env v = eval env' v) (k : ℕ) :
    eval env (q512 v k) = eval env' (q512 v k) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold q512 b512
  rw [Vector.getElem_ofFn]
  exact eval_getElem_congr h _ _

/-- `c512x` selects word `i / 32` for bit `i`, so word-level agreement suffices. -/
theorem eval_c512x_congr {u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 :
      Var (fields 32) (F p2)}
    (h : ∀ t < 16, eval env (c512sel u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 t)
      = eval env' (c512sel u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 t)) :
    eval env (c512x u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15)
      = eval env' (c512x u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold c512x b32
  rw [Vector.getElem_ofFn]
  exact eval_getElem_congr (h (i / 32) (by omega)) _ _

end EvalCongr

theorem wordAt_eval_c128_0 (env : Environment (F p2)) (a b c d : Var (fields 32) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (c128 a b c d)) 0
      = toNat (Vector.map (Expression.eval env) a) := by
  refine wordAt_map_eval_eq_toNat _ a 0 (by norm_num) ?_
  intro j hj
  unfold c128 b32
  rw [Vector.getElem_ofFn]
  rw [if_pos (by omega : 32 * 0 + j < 32)]
  simp only [show (32 * 0 + j) % 32 = j from by omega]

theorem wordAt_eval_c128_1 (env : Environment (F p2)) (a b c d : Var (fields 32) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (c128 a b c d)) 1
      = toNat (Vector.map (Expression.eval env) b) := by
  refine wordAt_map_eval_eq_toNat _ b 1 (by norm_num) ?_
  intro j hj
  unfold c128 b32
  rw [Vector.getElem_ofFn]
  rw [if_neg (by omega : ¬ 32 * 1 + j < 32), if_pos (by omega : 32 * 1 + j < 64)]
  simp only [show (32 * 1 + j) % 32 = j from by omega]

theorem wordAt_eval_c128_2 (env : Environment (F p2)) (a b c d : Var (fields 32) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (c128 a b c d)) 2
      = toNat (Vector.map (Expression.eval env) c) := by
  refine wordAt_map_eval_eq_toNat _ c 2 (by norm_num) ?_
  intro j hj
  unfold c128 b32
  rw [Vector.getElem_ofFn]
  rw [if_neg (by omega : ¬ 32 * 2 + j < 32), if_neg (by omega : ¬ 32 * 2 + j < 64),
    if_pos (by omega : 32 * 2 + j < 96)]
  simp only [show (32 * 2 + j) % 32 = j from by omega]

theorem wordAt_eval_c128_3 (env : Environment (F p2)) (a b c d : Var (fields 32) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (c128 a b c d)) 3
      = toNat (Vector.map (Expression.eval env) d) := by
  refine wordAt_map_eval_eq_toNat _ d 3 (by norm_num) ?_
  intro j hj
  unfold c128 b32
  rw [Vector.getElem_ofFn]
  rw [if_neg (by omega : ¬ 32 * 3 + j < 32), if_neg (by omega : ¬ 32 * 3 + j < 64),
    if_neg (by omega : ¬ 32 * 3 + j < 96)]
  simp only [show (32 * 3 + j) % 32 = j from by omega]

/-- Window `k` of the evaluated `c512x` is `toNat` of the `k`-th selected word. -/
theorem wordAt_eval_c512x_sel (env : Environment (F p2))
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : Var (fields 32) (F p2))
    (k : ℕ) (hk : k < 16) :
    wordAt 32 (Vector.map (Expression.eval env)
        (c512x u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15)) k
      = toNat (Vector.map (Expression.eval env)
          (c512sel u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 k)) := by
  refine wordAt_map_eval_eq_toNat _ _ k (by omega) ?_
  intro j hj
  unfold c512x b32
  rw [Vector.getElem_ofFn]
  have hdiv : (32 * k + j) / 32 = k := by omega
  simp only [hdiv, show (32 * k + j) % 32 = j from by omega]

namespace Sched16

/-- Explicit `ConstantLength` for the 16-step schedule fold body (125 witnesses per
    step). Naming it lets the fold in `main` skip synthesis and lets the cost/R1CS
    lemmas fold with the same instance. -/
def constantLength :
    Circuit.ConstantLength (fun (x : Vector (fields 32 (Expression (F p2))) 32 × Fin 16) => do
      let ui ← ScheduleStep.circuit (c128 (x.1[x.2.val]'(by omega)) (x.1[x.2.val + 1]'(by omega))
        (x.1[x.2.val + 9]'(by omega)) (x.1[x.2.val + 14]'(by omega)))
      return x.1.set (16 + x.2.val) ui (by omega)) where
  localLength := 125
  localLength_eq _ _ := by
    simp [circuit_norm, ScheduleStep.circuit, ScheduleStep.elaborated]

/-- The `k`-th step's witnessed output word: a fresh 32-bit witness vector at the
    step's Pin32 offset (relative 93 within the 125-witness step). -/
def stepWord (i₀ k : ℕ) : Var (fields 32) (F p2) :=
  varFromOffset (fields 32) (i₀ + k * 125 + 93)

/-- `ScheduleStep.circuit`'s output word is a fresh witness at relative offset 93. -/
@[simp] lemma scheduleStep_output (b : Var (fields 128) (F p2)) (n : ℕ) :
    ScheduleStep.circuit.output b n = varFromOffset (fields 32) (n + 93) := rfl

/-- `ScheduleStep.circuit`'s localLength is the constant 125. -/
@[simp] lemma scheduleStep_localLength (b : Var (fields 128) (F p2)) :
    ScheduleStep.circuit.localLength b = 125 := rfl

/-- Variable-level 32-word buffer after `k` steps (input words `[0..15]`, the
    `k` new witnessed words `[16..15+k]`). Closed form of the fold accumulator. -/
def varBuf (i₀ : ℕ) (v : Var (fields 512) (F p2)) :
    ℕ → Vector (fields 32 (Expression (F p2))) 32
  | 0 =>
    (Vector.ofFn fun j : Fin 16 => q512 v j.val) ++
      Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2)))
  | k + 1 =>
    if h : k < 16 then
      (varBuf i₀ v k).set (16 + k) (stepWord i₀ k) (by omega)
    else varBuf i₀ v k

/-- The 16-step `Fin.foldl` of the reduced buffer body equals `varBuf 16`. -/
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

/-- Buffer word `16 + j` (the `j`-th produced word) is `stepWord i₀ j` once `m > j`. -/
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

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 16` equals `varBuf i₀ v k`.
    Phrased against the inlined (subcircuit + `set`) fold body so it matches `h_holds`. -/
lemma foldlAcc_eq_varBuf (i₀ : ℕ) (v : Var (fields 512) (F p2)) (k : ℕ) (h : k < 16) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 16)
      (fun (w : Vector (fields 32 (Expression (F p2))) 32) (i : Fin 16) (n : ℕ) =>
        (Vector.set w (16 + i.val)
            (ScheduleStep.circuit.output
              (c128 (w[i.val]'(by omega)) (w[i.val + 1]'(by omega))
                (w[i.val + 9]'(by omega)) (w[i.val + 14]'(by omega))) n) (by omega),
          [Operation.subcircuit (ScheduleStep.circuit.toSubcircuit n
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

/-- The fold body allocates exactly the step's 125 witnesses (spelled as the
`do`-block that `main` writes, so the loop-peeling `simp` set can use it). -/
lemma stepBody_localLength (w : Vector (Var (fields 32) (F p2)) 32) (i : Fin 16) (n : ℕ) :
    (do
      let ui ← subcircuit ScheduleStep.circuit (c128 (w[i.val]'(by omega))
        (w[i.val + 1]'(by omega)) (w[i.val + 9]'(by omega)) (w[i.val + 14]'(by omega)))
      pure (w.set (16 + i.val) ui (by omega))).localLength n = 125 := rfl

/-- `foldlAcc` bridge against the `do`-block body, as the loop-peeling lemma
presents the fold. -/
lemma foldlAcc_eq_varBuf_do (i₀ : ℕ) (v : Var (fields 512) (F p2)) (k : ℕ) (h : k < 16) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 16)
      (fun (w : Vector (Var (fields 32) (F p2)) 32) (i : Fin 16) => do
        let ui ← subcircuit ScheduleStep.circuit (c128 (w[i.val]'(by omega))
          (w[i.val + 1]'(by omega)) (w[i.val + 9]'(by omega)) (w[i.val + 14]'(by omega)))
        pure (w.set (16 + i.val) ui (by omega)))
      ((Vector.ofFn fun j : Fin 16 => q512 v j.val) ++
        Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))
      ⟨k, h⟩ = varBuf i₀ v k :=
  foldlAcc_eq_varBuf i₀ v k h

/-- A step's produced word is a fresh 32-cell witness block inside the step. -/
theorem eval_stepWord_of_agreesBelow (i₀ k : ℕ) {kk : ℕ} (hk : i₀ + k * 125 + 125 ≤ kk)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow kk env') :
    eval env (stepWord i₀ k) = eval env' (stepWord i₀ k) := by
  unfold stepWord
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

/-- Every cell of the buffer after `k` steps is either an input word or one of the
`k` witness blocks already allocated, so it is determined below `i₀ + k * 125`. -/
theorem eval_varBuf_getElem_of_agreesBelow (i₀ : ℕ) (v : Var (fields 512) (F p2))
    {kk : ℕ} {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow kk env') (h_input : eval env v = eval env' v) :
    ∀ (k : ℕ), i₀ + k * 125 ≤ kk → ∀ (j : ℕ) (hj : j < 32),
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
    have hk16 : k < 16 ∨ 16 ≤ k := by omega
    rcases hk16 with hk16 | hk16
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

/-- The evaluated all-zero word has `toNat` zero. -/
theorem toNat_replicate0 (env : Environment (F p2)) :
    toNat (Vector.map (Expression.eval env) (Vector.replicate 32 (0 : Expression (F p2)))) = 0 := by
  have h : Vector.map (Expression.eval env) (Vector.replicate 32 (0 : Expression (F p2)))
      = Vector.replicate 32 (0 : F p2) := by rw [Vector.map_replicate]; rfl
  rw [h, toNat, wordAt]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_range] at hi
  simp [bitAt, hi]

end Sched16

end Solution.SHA256CompressGF2
