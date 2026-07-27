import Solution.SHA256CompressGF2.Theorems
import Solution.SHA256CompressGF2.Add32

/-!
# Top-level helpers for `main`

Wiring `def`s and word-level bridges used by the top-level `soundness`.
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

/-- Word `k` of a 256-bit vector. -/
def w256 (v : Var (fields 256) (F p2)) (k : ℕ) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => a256 v (32 * k + i.val)

/-- Concatenate a 256-bit state and a 512-bit schedule block. -/
def c768 (s : Var (fields 256) (F p2)) (w : Var (fields 512) (F p2)) :
    Var (fields 768) (F p2) :=
  Vector.ofFn fun i : Fin 768 =>
    if i.val < 256 then a256 s i.val else b512 w (i.val - 256)

/-- Output-word selector. -/
def o8sel (o0 o1 o2 o3 o4 o5 o6 o7 : Var (fields 32) (F p2)) : ℕ → Var (fields 32) (F p2)
  | 0 => o0
  | 1 => o1
  | 2 => o2
  | 3 => o3
  | 4 => o4
  | 5 => o5
  | 6 => o6
  | _ => o7

/-- Assemble the 256-bit output from 8 words. -/
def out256 (o0 o1 o2 o3 o4 o5 o6 o7 : Var (fields 32) (F p2)) :
    Var (fields 256) (F p2) :=
  Vector.ofFn fun i : Fin 256 => b32 (o8sel o0 o1 o2 o3 o4 o5 o6 o7 (i.val / 32)) i.val

theorem toNat_eval_w256 (env : Environment (F p2)) (v : Var (fields 256) (F p2)) (k : ℕ)
    (hk : 32 * k + 32 ≤ 256) :
    toNat (Vector.map (Expression.eval env) (w256 v k)) = wordAt 32 (Vector.map (Expression.eval env) v) k := by
  rw [← wordAt_map_eval_eq_toNat v (w256 v k) k hk]
  intro j hj
  unfold w256 a256
  rw [Vector.getElem_ofFn]
  have hlt : 32 * k + j < 256 := by omega
  simp only [Nat.mod_eq_of_lt hlt]

/-- The 8 state words of `c768 s w` are the words of `s`. -/
theorem ofFn_wordAt_c768_state (env : Environment (F p2)) (s : Var (fields 256) (F p2))
    (w : Var (fields 512) (F p2)) :
    (Vector.ofFn fun i : Fin 8 => wordAt 32 (Vector.map (Expression.eval env) (c768 s w)) i.val)
      = toWords 32 8 (Vector.map (Expression.eval env) s) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_ofFn, toWords, Vector.getElem_ofFn]
  refine wordAt_map_eval_eq_wordAt (c768 s w) (Vector.map (Expression.eval env) s) i i
    (by omega) (by omega) ?_
  intro l hl
  unfold c768 a256
  rw [Vector.getElem_ofFn, Vector.getElem_map]
  rw [if_pos (by omega : 32 * i + l < 256)]
  have hlt : 32 * i + l < 256 := by omega
  simp only [Nat.mod_eq_of_lt hlt]

/-- The 16 schedule words of `c768 s w` are the words of `w`. -/
theorem ofFn_wordAt_c768_sched (env : Environment (F p2)) (s : Var (fields 256) (F p2))
    (w : Var (fields 512) (F p2)) :
    (Vector.ofFn fun i : Fin 16 => wordAt 32 (Vector.map (Expression.eval env) (c768 s w)) (8 + i.val))
      = toWords 32 16 (Vector.map (Expression.eval env) w) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_ofFn, toWords, Vector.getElem_ofFn]
  refine wordAt_map_eval_eq_wordAt (c768 s w) (Vector.map (Expression.eval env) w) (8 + i) i
    (by omega) (by omega) ?_
  intro l hl
  unfold c768 b512
  rw [Vector.getElem_ofFn, Vector.getElem_map]
  rw [if_neg (by omega : ¬ 32 * (8 + i) + l < 256)]
  have hlt : 32 * i + l < 512 := by omega
  simp only [show 32 * (8 + i) + l - 256 = 32 * i + l from by omega, Nat.mod_eq_of_lt hlt]

/-- Window `k` of the evaluated `out256` is `toNat` of the `k`-th selected word. -/
theorem wordAt_eval_out256_sel (env : Environment (F p2))
    (o0 o1 o2 o3 o4 o5 o6 o7 : Var (fields 32) (F p2)) (k : ℕ) (hk : k < 8) :
    wordAt 32 (Vector.map (Expression.eval env) (out256 o0 o1 o2 o3 o4 o5 o6 o7)) k
      = toNat (Vector.map (Expression.eval env) (o8sel o0 o1 o2 o3 o4 o5 o6 o7 k)) := by
  refine wordAt_map_eval_eq_toNat _ _ k (by omega) ?_
  intro j hj
  unfold out256 b32
  rw [Vector.getElem_ofFn]
  have hdiv : (32 * k + j) / 32 = k := by omega
  simp only [hdiv, show (32 * k + j) % 32 = j from by omega]

/-! ## `eval`-agreement congruences for the top-level wiring maps -/

section EvalCongr

variable {env env' : ProverEnvironment (F p2)}

theorem eval_input_h_congr {v : Var Input (F p2)} (h : eval env v = eval env' v) :
    eval env v.h = eval env' v.h := by
  have h2 := congrArg (fun s : Input (F p2) => s.h) h
  simpa [circuit_norm] using h2

theorem eval_input_m_congr {v : Var Input (F p2)} (h : eval env v = eval env' v) :
    eval env v.m = eval env' v.m := by
  have h2 := congrArg (fun s : Input (F p2) => s.m) h
  simpa [circuit_norm] using h2

theorem eval_w256_congr {v : Var (fields 256) (F p2)} (h : eval env v = eval env' v) (k : ℕ) :
    eval env (w256 v k) = eval env' (w256 v k) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold w256 a256
  rw [Vector.getElem_ofFn]
  exact eval_getElem_congr h _ _

theorem eval_c768_congr {s : Var (fields 256) (F p2)} {w : Var (fields 512) (F p2)}
    (hs : eval env s = eval env' s) (hw : eval env w = eval env' w) :
    eval env (c768 s w) = eval env' (c768 s w) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold c768 a256 b512
  rw [Vector.getElem_ofFn]
  split
  · exact eval_getElem_congr hs _ _
  · exact eval_getElem_congr hw _ _

/-- The `Output` struct wrapper around the assembled 256-bit result. -/
theorem eval_out_mk_congr {u : Var (fields 256) (F p2)} (h : eval env u = eval env' u) :
    eval env (⟨u⟩ : Var Output (F p2)) = eval env' (⟨u⟩ : Var Output (F p2)) := by
  simp only [circuit_norm] at h ⊢
  rw [h]

end EvalCongr

/-- Explicit `ConstantLength` for the 8-add feed-forward `mapFinRange` body
    (Add32 localLength is 31). Naming it lets the map skip the expensive default
    `infer_constant_length` synthesis, and lets the cost/R1CS lemmas map with the
    same instance. -/
def feedConstantLength (input : Var Input (F p2)) (s4 : Var (fields 256) (F p2)) :
    Circuit.ConstantLength (fun i : Fin 8 => Add32.circuit ⟨w256 input.h i.val, w256 s4 i.val⟩) where
  localLength := 31
  localLength_eq _ _ := by simp [circuit_norm, Add32.circuit, Add32.elaborated]

end Solution.SHA256CompressGF2
