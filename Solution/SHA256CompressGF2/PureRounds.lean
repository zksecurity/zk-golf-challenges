import Clean.Specs.SHA256

/-!
# Pure compression-round lemmas

Linearizes `Specs.SHA256.sha256Compress` (a 64-step `Fin.foldl`) into the
sequential `valState`, and splits it into four 16-round chunks `applyRounds16`
(the leaf spec of `Rounds16`), matching the circuit's chunking.
-/

namespace Solution.SHA256CompressGF2.PureRounds

open Specs.SHA256

/-- Round constant `n % 64` as a `ℕ` word. -/
def kAt (n : ℕ) : ℕ := (K[n % 64]'(Nat.mod_lt _ (by norm_num))).toNat

/-- State after `k` linearized rounds. -/
def valState (state : Vector ℕ 8) (w : Vector ℕ 64) : ℕ → Vector ℕ 8
  | 0 => state
  | k + 1 =>
    if h : k < 64 then
      sha256Round (valState state w k) (K[k]'h).toNat (w[k]'h)
    else valState state w k

/-- `sha256Compress` is the linearized `valState` at step 64. -/
theorem sha256Compress_eq (state : Vector ℕ 8) (w : Vector ℕ 64) :
    sha256Compress state w = valState state w 64 := by
  simp only [sha256Compress]
  suffices h : ∀ k (hk : k ≤ 64),
      Fin.foldl k
        (fun s (i : Fin k) =>
          sha256Round s (K[i.val]'(by have := i.isLt; omega)).toNat
            (w[i.val]'(by have := i.isLt; omega))) state = valState state w k by
    exact h 64 (le_refl 64)
  intro k hk
  induction k with
  | zero => simp [valState, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, valState, dif_pos (by omega : k < 64)]
    rw [show Fin.foldl k
          (fun s (i : Fin k) =>
            sha256Round s (K[i.castSucc.val]'(by have := i.isLt; omega)).toNat
              (w[i.castSucc.val]'(by have := i.isLt; omega))) state =
        Fin.foldl k
          (fun s (i : Fin k) =>
            sha256Round s (K[i.val]'(by have := i.isLt; omega)).toNat
              (w[i.val]'(by have := i.isLt; omega))) state from rfl, ih (by omega)]
    simp [Fin.val_last]

/-- Window `c` of the 64-word schedule (16 message words for chunk `c`). -/
def win64 (w : Vector ℕ 64) (c : ℕ) : Vector ℕ 16 :=
  Vector.ofFn fun i : Fin 16 => w[(16 * c + i.val) % 64]'(Nat.mod_lt _ (by norm_num))

theorem win64_getElem (w : Vector ℕ 64) (c i : ℕ) (hi : i < 16) (hc : 16 * c + i < 64) :
    (win64 w c)[i]'hi = w[16 * c + i]'hc := by
  unfold win64
  rw [Vector.getElem_ofFn]
  simp only [Nat.mod_eq_of_lt hc]

/-- Total mod-16 accessor into a 16-vector (`v[i]` for `i < 16`). -/
def at16 (v : Vector ℕ 16) (i : ℕ) : ℕ := v[i % 16]'(Nat.mod_lt _ (by norm_num))

theorem at16_lt (v : Vector ℕ 16) (i : ℕ) (hi : i < 16) : at16 v i = v[i]'hi := by
  unfold at16; simp only [Nat.mod_eq_of_lt hi]

/-- One 16-round chunk: 16 `sha256Round`s with constants `K[r0..r0+15]` and the
16 window words. -/
def applyRounds16 (r0 : ℕ) (sched : Vector ℕ 16) (state : Vector ℕ 8) : Vector ℕ 8 :=
  Fin.foldl 16 (fun s (i : Fin 16) => sha256Round s (kAt (r0 + i.val)) (at16 sched i.val)) state

/-- Sequential form of `applyRounds16` (left fold, `n` rounds). -/
def applyN (r0 : ℕ) (sched : Vector ℕ 16) : ℕ → Vector ℕ 8 → Vector ℕ 8
  | 0, s => s
  | n + 1, s => sha256Round (applyN r0 sched n s) (kAt (r0 + n)) (at16 sched n)

theorem foldl_eq_applyN (r0 : ℕ) (sched : Vector ℕ 16) (state : Vector ℕ 8) (n : ℕ) :
    Fin.foldl n (fun s (i : Fin n) => sha256Round s (kAt (r0 + i.val)) (at16 sched i.val)) state
      = applyN r0 sched n state := by
  induction n with
  | zero => simp [applyN, Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last]
    rw [show Fin.foldl n (fun s (i : Fin n) =>
          sha256Round s (kAt (r0 + i.castSucc.val)) (at16 sched i.castSucc.val)) state
        = Fin.foldl n (fun s (i : Fin n) =>
          sha256Round s (kAt (r0 + i.val)) (at16 sched i.val)) state from rfl, ih]
    rw [applyN]

theorem applyRounds16_eq_applyN (r0 : ℕ) (sched : Vector ℕ 16) (state : Vector ℕ 8) :
    applyRounds16 r0 sched state = applyN r0 sched 16 state :=
  foldl_eq_applyN r0 sched state 16

/-- A chunk of 16 rounds started from `valState (16c)` reaches `valState (16(c+1))`. -/
theorem applyRounds16_advance (state : Vector ℕ 8) (w : Vector ℕ 64) (c : ℕ) (hc : c ≤ 3) :
    applyRounds16 (16 * c) (win64 w c) (valState state w (16 * c)) = valState state w (16 * (c + 1)) := by
  have hpre : ∀ n, n ≤ 16 →
      Fin.foldl n (fun s (i : Fin n) =>
        sha256Round s (kAt (16 * c + i.val)) (at16 (win64 w c) i.val)) (valState state w (16 * c))
        = valState state w (16 * c + n) := by
    intro n
    induction n with
    | zero => intro _; simp [Fin.foldl_zero]
    | succ n ih =>
      intro hn
      rw [Fin.foldl_succ_last]
      simp only [Fin.val_last]
      rw [show Fin.foldl n (fun s (i : Fin n) =>
            sha256Round s (kAt (16 * c + i.castSucc.val)) (at16 (win64 w c) i.castSucc.val))
            (valState state w (16 * c))
          = Fin.foldl n (fun s (i : Fin n) =>
            sha256Round s (kAt (16 * c + i.val)) (at16 (win64 w c) i.val))
            (valState state w (16 * c)) from rfl, ih (by omega)]
      rw [show 16 * c + (n + 1) = (16 * c + n) + 1 from by ring, valState,
        dif_pos (by omega : 16 * c + n < 64)]
      congr 1
      · unfold kAt
        congr 2
        omega
      · rw [at16_lt _ n (by omega), win64_getElem w c n (by omega) (by omega)]
  have := hpre 16 (le_refl 16)
  rw [applyRounds16, this]
  congr 1

/-- `sha256Compress` splits into four 16-round chunks. -/
theorem sha256Compress_split (state : Vector ℕ 8) (w : Vector ℕ 64) :
    sha256Compress state w
      = applyRounds16 48 (win64 w 3)
          (applyRounds16 32 (win64 w 2)
            (applyRounds16 16 (win64 w 1)
              (applyRounds16 0 (win64 w 0) state))) := by
  rw [sha256Compress_eq]
  have h0 : applyRounds16 0 (win64 w 0) state = valState state w 16 := by
    have := applyRounds16_advance state w 0 (by omega)
    simpa using this
  have h1 : applyRounds16 16 (win64 w 1) (valState state w 16) = valState state w 32 := by
    have := applyRounds16_advance state w 1 (by omega); simpa using this
  have h2 : applyRounds16 32 (win64 w 2) (valState state w 32) = valState state w 48 := by
    have := applyRounds16_advance state w 2 (by omega); simpa using this
  have h3 : applyRounds16 48 (win64 w 3) (valState state w 48) = valState state w 64 := by
    have := applyRounds16_advance state w 3 (by omega); simpa using this
  rw [h0, h1, h2, h3]

end Solution.SHA256CompressGF2.PureRounds
