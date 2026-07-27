import Clean.Specs.SHA256

/-!
# Pure message-schedule lemmas

Linearizes `Specs.SHA256.messageSchedule` (a 48-step `Fin.foldl`) into the
sequential `valSchedule`, giving a per-index recurrence (`vs_step`). Defines the
16-word window-extension `extend16` used as the leaf spec of `Sched16`, and
proves it advances the schedule by one 16-word window (`extend16_window`).
-/

namespace Solution.SHA256CompressGF2.PureSchedule

open Specs.SHA256

/-- The 64-word schedule after `k` linearized expansion steps (word `k+16`
is finalized at step `k+1`). -/
def valSchedule (block : Vector ℕ 16) : ℕ → Vector ℕ 64
  | 0 => Vector.mapFinRange 64 fun i => if h : i.val < 16 then block.get ⟨i.val, h⟩ else 0
  | k + 1 =>
    if h : k < 48 then
      let prev := valSchedule block k
      let wj := add32 (add32 (lowerSigma1 prev[k + 16 - 2]) prev[k + 16 - 7])
                      (add32 (lowerSigma0 prev[k + 16 - 15]) prev[k + 16 - 16])
      prev.set (k + 16) wj (by omega)
    else valSchedule block k

theorem vs_succ_ne (block : Vector ℕ 16) (k i : ℕ) (hi : i < 64) (hne : i ≠ k + 16) :
    (valSchedule block (k+1))[i]'hi = (valSchedule block k)[i]'hi := by
  rw [valSchedule]
  by_cases h : k < 48
  · simp only [dif_pos h]; rw [Vector.getElem_set_ne _ _ (by omega)]
  · simp only [dif_neg h]

theorem vs_stable (block : Vector ℕ 16) (k : ℕ) :
    ∀ m, k ≤ m → ∀ (i : ℕ) (hi : i < 64), i < k + 16 →
      (valSchedule block m)[i]'hi = (valSchedule block k)[i]'hi := by
  intro m
  induction m with
  | zero => intro _ i hi hik; have : k = 0 := by omega
            subst this; rfl
  | succ m ih =>
    intro hm i hi hik
    rcases Nat.lt_or_ge k (m+1) with h | h
    · rw [vs_succ_ne block m i hi (by omega), ih (by omega) i hi hik]
    · have : k = m + 1 := by omega
      subst this; rfl

theorem vs_lt16 (block : Vector ℕ 16) (k i : ℕ) (hi : i < 16) :
    (valSchedule block k)[i]'(by omega) = block[i]'hi := by
  induction k with
  | zero => rw [valSchedule]; simp only [Vector.getElem_mapFinRange, dif_pos hi]; rfl
  | succ k ih => rw [vs_succ_ne block k i (by omega) (by omega), ih]

/-- The schedule recurrence, per index `t = k + 16` (`k < 48`). -/
theorem vs_step (block : Vector ℕ 16) (k : ℕ) (hk : k < 48) :
    (valSchedule block 48)[k + 16]'(by omega)
      = add32 (add32 (lowerSigma1 ((valSchedule block 48)[k + 14]'(by omega)))
                     ((valSchedule block 48)[k + 9]'(by omega)))
              (add32 (lowerSigma0 ((valSchedule block 48)[k + 1]'(by omega)))
                     ((valSchedule block 48)[k]'(by omega))) := by
  have hfin : (valSchedule block 48)[k + 16]'(by omega)
      = (valSchedule block (k+1))[k + 16]'(by omega) :=
    vs_stable block (k+1) 48 (by omega) (k+16) (by omega) (by omega)
  rw [hfin, valSchedule]
  simp only [dif_pos hk, Vector.getElem_set_self]
  rw [← vs_stable block k 48 (by omega) (k+16-2) (by omega) (by omega),
      ← vs_stable block k 48 (by omega) (k+16-7) (by omega) (by omega),
      ← vs_stable block k 48 (by omega) (k+16-15) (by omega) (by omega),
      ← vs_stable block k 48 (by omega) (k+16-16) (by omega) (by omega)]
  simp only [show k+16-2 = k+14 from by omega, show k+16-7 = k+9 from by omega,
    show k+16-15 = k+1 from by omega, show k+16-16 = k from by omega]

/-- `Specs.SHA256.messageSchedule` is the linearized `valSchedule` at step 48. -/
theorem messageSchedule_eq (block : Vector ℕ 16) :
    messageSchedule block = valSchedule block 48 := by
  simp only [messageSchedule]
  set body : Vector ℕ 64 → ℕ → Vector ℕ 64 := fun w n =>
    if h : n < 48 then
      have hj : n + 16 < 64 := by omega
      w.set (n + 16)
        (add32 (add32 (lowerSigma1 w[n + 16 - 2]) w[n + 16 - 7])
          (add32 (lowerSigma0 w[n + 16 - 15]) w[n + 16 - 16])) hj
    else w with hbody
  set init : Vector ℕ 64 :=
    Vector.mapFinRange 64 fun i => if h : i.val < 16 then block.get ⟨i.val, h⟩ else 0
  have hspec : Fin.foldl 48 (fun w (i : Fin 48) =>
      w.set (i.val + 16)
        (add32 (add32 (lowerSigma1 w[i.val + 16 - 2]) w[i.val + 16 - 7])
          (add32 (lowerSigma0 w[i.val + 16 - 15]) w[i.val + 16 - 16]))
        (by have := i.isLt; omega)) init =
      Fin.foldl 48 (fun w (i : Fin 48) => body w i.val) init := by
    congr 1; funext w i
    have hi : i.val < 48 := i.isLt
    simp only [hbody, dif_pos hi]
  rw [hspec]
  suffices h : ∀ k (hk : k ≤ 48),
      Fin.foldl k (fun w (i : Fin k) => body w i.val) init = valSchedule block k by
    exact h 48 (le_refl 48)
  intro k hk
  induction k with
  | zero => simp [valSchedule, Fin.foldl_zero, init]
  | succ k ih =>
    rw [Fin.foldl_succ_last, valSchedule]
    rw [show (fun w (i : Fin k) => body w i.castSucc.val) = (fun w (i : Fin k) => body w i.val) from rfl,
        ih (by omega)]
    simp only [Fin.val_last, hbody, dif_pos (show k < 48 from by omega)]

/-! ## Window extension (`extend16`): the leaf spec of `Sched16` -/

/-- 32-word buffer: input 16 words at `[0..15]`, next 16 computed by the schedule
recurrence (word `s+16` finalized at step `s+1`). -/
def ext32 (x : Vector ℕ 16) : ℕ → Vector ℕ 32
  | 0 => Vector.append x (Vector.replicate 16 0)
  | s + 1 =>
    if h : s < 16 then
      let prev := ext32 x s
      prev.set (s + 16)
        (add32 (add32 (lowerSigma1 prev[s + 14]) prev[s + 9])
               (add32 (lowerSigma0 prev[s + 1]) prev[s])) (by omega)
    else ext32 x s

theorem ext32_succ_ne (x : Vector ℕ 16) (s i : ℕ) (hi : i < 32) (hne : i ≠ s + 16) :
    (ext32 x (s+1))[i]'hi = (ext32 x s)[i]'hi := by
  rw [ext32]
  by_cases h : s < 16
  · simp only [dif_pos h]; rw [Vector.getElem_set_ne _ _ (by omega)]
  · simp only [dif_neg h]

theorem ext32_lt16 (x : Vector ℕ 16) (s i : ℕ) (hi : i < 16) :
    (ext32 x s)[i]'(by omega) = x[i]'hi := by
  induction s with
  | zero =>
    rw [ext32]
    show (x ++ Vector.replicate 16 0)[i]'(by omega) = x[i]'hi
    rw [Vector.getElem_append_left hi]
  | succ s ih => rw [ext32_succ_ne x s i (by omega) (by omega), ih]

theorem ext32_stable (x : Vector ℕ 16) (k : ℕ) :
    ∀ m, k ≤ m → ∀ (i : ℕ) (hi : i < 32), i < k + 16 →
      (ext32 x m)[i]'hi = (ext32 x k)[i]'hi := by
  intro m
  induction m with
  | zero => intro _ i hi hik; have : k = 0 := by omega
            subst this; rfl
  | succ m ih =>
    intro hm i hi hik
    rcases Nat.lt_or_ge k (m+1) with h | h
    · rw [ext32_succ_ne x m i hi (by omega), ih (by omega) i hi hik]
    · have : k = m + 1 := by omega
      subst this; rfl

/-- The 16 new words. -/
def extend16 (x : Vector ℕ 16) : Vector ℕ 16 :=
  Vector.ofFn fun j : Fin 16 => (ext32 x 16)[j.val + 16]'(by omega)

/-- Total 32-index accessor into the extension buffer (`x[m]` for `m < 16`,
`(extend16 x)[m-16]` for `16 ≤ m < 32`). -/
def extIdx (x : Vector ℕ 16) (m : ℕ) : ℕ := (ext32 x 16)[m % 32]'(Nat.mod_lt _ (by norm_num))

theorem extIdx_lt (x : Vector ℕ 16) (m : ℕ) (hm : m < 32) :
    extIdx x m = (ext32 x 16)[m]'hm := by
  unfold extIdx; simp only [Nat.mod_eq_of_lt hm]

theorem extIdx_input (x : Vector ℕ 16) (m : ℕ) (hm : m < 16) :
    extIdx x m = x[m]'hm := by
  rw [extIdx_lt x m (by omega), ext32_lt16 x 16 m hm]

theorem extIdx_output (x : Vector ℕ 16) (m : ℕ) (h1 : 16 ≤ m) (h2 : m < 32) :
    extIdx x m = (extend16 x)[m - 16]'(by omega) := by
  rw [extIdx_lt x m h2]
  unfold extend16
  rw [Vector.getElem_ofFn]
  congr 1
  exact (Nat.sub_add_cancel h1).symm

/-- `extIdx` at an output index, indexed by the output slot. -/
theorem extIdx_out' (x : Vector ℕ 16) (j : ℕ) (hj : j < 16) :
    extIdx x (j + 16) = (extend16 x)[j]'hj := by
  rw [extIdx_lt x (j + 16) (by omega)]
  unfold extend16
  rw [Vector.getElem_ofFn]

/-- Each new word as the schedule recurrence over `extIdx`. -/
theorem extend16_getElem (x : Vector ℕ 16) (j : ℕ) (hj : j < 16) :
    (extend16 x)[j]'hj
      = add32 (add32 (lowerSigma1 (extIdx x (j + 14))) (extIdx x (j + 9)))
              (add32 (lowerSigma0 (extIdx x (j + 1))) (extIdx x j)) := by
  unfold extend16
  rw [Vector.getElem_ofFn]
  rw [ext32_stable x (j+1) 16 (by omega) (j+16) (by omega) (by omega)]
  rw [ext32]
  simp only [dif_pos (show j < 16 from by omega), Vector.getElem_set_self]
  rw [extIdx_lt x (j+14) (by omega), extIdx_lt x (j+9) (by omega),
      extIdx_lt x (j+1) (by omega), extIdx_lt x j (by omega)]
  rw [ext32_stable x j 16 (by omega) (j+14) (by omega) (by omega),
      ext32_stable x j 16 (by omega) (j+9) (by omega) (by omega),
      ext32_stable x j 16 (by omega) (j+1) (by omega) (by omega),
      ext32_stable x j 16 (by omega) j (by omega) (by omega)]

/-- Window `k` of the linearized schedule (totalized by `% 64`; for `k ≤ 3`,
`16k + i < 64` so the mod is inert). -/
def window (block : Vector ℕ 16) (k : ℕ) : Vector ℕ 16 :=
  Vector.ofFn fun i : Fin 16 =>
    (valSchedule block 48)[(16 * k + i.val) % 64]'(Nat.mod_lt _ (by norm_num))

theorem window_getElem (block : Vector ℕ 16) (k : ℕ) (i : ℕ) (hi : i < 16)
    (hk : 16 * k + i < 64) :
    (window block k)[i]'hi = (valSchedule block 48)[16 * k + i]'hk := by
  unfold window
  rw [Vector.getElem_ofFn]
  simp only [Nat.mod_eq_of_lt hk]

/-- The extension buffer over `window block k` reproduces the schedule (indices
`16k .. 16k+15+j`). -/
theorem ext32_eq_window (block : Vector ℕ 16) (k : ℕ) (hk : k ≤ 2) :
    ∀ j, j ≤ 16 → ∀ (i : ℕ) (hi : i < 32), i < 16 + j →
      (ext32 (window block k) j)[i]'hi = (valSchedule block 48)[16 * k + i]'(by omega) := by
  intro j
  induction j with
  | zero =>
    intro _ i hi hik
    rw [ext32]
    show (window block k ++ Vector.replicate 16 0)[i]'hi = _
    rw [Vector.getElem_append_left (by omega : i < 16)]
    rw [window_getElem block k i (by omega) (by omega)]
  | succ j ih =>
    intro hj i hi hik
    by_cases hnew : i = j + 16
    · subst hnew
      rw [ext32]
      simp only [dif_pos (show j < 16 from by omega), Vector.getElem_set_self]
      rw [ih (by omega) (j+14) (by omega) (by omega), ih (by omega) (j+9) (by omega) (by omega),
        ih (by omega) (j+1) (by omega) (by omega), ih (by omega) j (by omega) (by omega)]
      have hstep := vs_step block (16 * k + j) (by omega)
      have hgc : ∀ (a b : ℕ) (ha : a < 64) (hb : b < 64), a = b →
          (valSchedule block 48)[a]'ha = (valSchedule block 48)[b]'hb := by
        intro a b ha hb hab; subst hab; rfl
      rw [hgc (16 * k + (j + 16)) ((16 * k + j) + 16) (by omega) (by omega) (by omega), hstep]
      rw [hgc (16 * k + j + 14) (16 * k + (j + 14)) (by omega) (by omega) (by omega),
        hgc (16 * k + j + 9) (16 * k + (j + 9)) (by omega) (by omega) (by omega),
        hgc (16 * k + j + 1) (16 * k + (j + 1)) (by omega) (by omega) (by omega)]
    · rw [ext32_succ_ne _ j i hi (by omega), ih (by omega) i hi (by omega)]

/-- Window 0 of the schedule is the original block. -/
theorem window_zero (block : Vector ℕ 16) : window block 0 = block := by
  refine Vector.ext fun i hi => ?_
  rw [window_getElem block 0 i hi (by omega)]
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [vs_lt16 block 48 i hi]

/-- `extend16` advances the schedule by one 16-word window. -/
theorem extend16_window (block : Vector ℕ 16) (k : ℕ) (hk : k ≤ 2) :
    extend16 (window block k) = window block (k + 1) := by
  refine Vector.ext fun j hj => ?_
  unfold extend16
  rw [Vector.getElem_ofFn]
  rw [ext32_eq_window block k hk 16 (le_refl 16) (j + 16) (by omega) (by omega)]
  rw [window_getElem block (k+1) j hj (by omega)]
  congr 1
  omega

end Solution.SHA256CompressGF2.PureSchedule
