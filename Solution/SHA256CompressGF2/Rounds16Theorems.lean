import Solution.SHA256CompressGF2.Round

/-!
# Private helpers for `Rounds16`
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

/-- Plain total accessor into a 768-bit vector. -/
def a768 {α : Type} (v : Vector α 768) (k : ℕ) : α :=
  v[k % 768]'(Nat.mod_lt _ (by norm_num))

/-- Word `k` of a 768-bit vector. -/
def q768 (v : Var (fields 768) (F p2)) (k : ℕ) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => a768 v (32 * k + i.val)

/-- The 256-bit prefix of a 768-bit vector. -/
def st768 (v : Var (fields 768) (F p2)) : Var (fields 256) (F p2) :=
  Vector.ofFn fun i : Fin 256 => a768 v i.val

/-- Round constant `n % 64`, totalized. -/
def kAt (n : ℕ) : ℕ := (Specs.SHA256.K[n % 64]'(Nat.mod_lt _ (by norm_num))).toNat

/-- Concatenate a 256-bit state and a 32-bit word into a round input. -/
def c288s (s : Var (fields 256) (F p2)) (w : Var (fields 32) (F p2)) :
    Var (fields 288) (F p2) :=
  Vector.ofFn fun i : Fin 288 =>
    if i.val < 256 then a256 s i.val else b32 w i.val

theorem toNat_eval_q768 (env : Environment (F p2)) (v : Var (fields 768) (F p2)) (k : ℕ)
    (hk : 32 * k + 32 ≤ 768) :
    toNat (Vector.map (Expression.eval env) (q768 v k)) = wordAt 32 (Vector.map (Expression.eval env) v) k := by
  rw [← wordAt_map_eval_eq_toNat v (q768 v k) k hk]
  intro j hj
  unfold q768 a768
  rw [Vector.getElem_ofFn]
  have hlt : 32 * k + j < 768 := by omega
  simp only [Nat.mod_eq_of_lt hlt]

theorem wordAt_eval_st768 (env : Environment (F p2)) (v : Var (fields 768) (F p2)) (j : ℕ) (hj : j < 8) :
    wordAt 32 (Vector.map (Expression.eval env) (st768 v)) j = wordAt 32 (Vector.map (Expression.eval env) v) j := by
  refine wordAt_map_eval_eq_wordAt (st768 v) (Vector.map (Expression.eval env) v) j j
    (by omega) (by omega) ?_
  intro l hl
  unfold st768 a768
  rw [Vector.getElem_ofFn, Vector.getElem_map]
  have hlt : 32 * j + l < 768 := by omega
  simp only [Nat.mod_eq_of_lt hlt]

theorem wordAt_eval_c288s_state (env : Environment (F p2)) (s : Var (fields 256) (F p2))
    (w : Var (fields 32) (F p2)) (j : ℕ) (hj : j < 8) :
    wordAt 32 (Vector.map (Expression.eval env) (c288s s w)) j
      = wordAt 32 (Vector.map (Expression.eval env) s) j := by
  refine wordAt_map_eval_eq_wordAt (c288s s w) (Vector.map (Expression.eval env) s) j j
    (by omega) (by omega) ?_
  intro l hl
  unfold c288s a256
  rw [Vector.getElem_ofFn, Vector.getElem_map]
  rw [if_pos (by omega : 32 * j + l < 256)]
  have hlt : 32 * j + l < 256 := by omega
  simp only [Nat.mod_eq_of_lt hlt]

theorem wordAt_eval_c288s_msg (env : Environment (F p2)) (s : Var (fields 256) (F p2))
    (w : Var (fields 32) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (c288s s w)) 8
      = toNat (Vector.map (Expression.eval env) w) := by
  refine wordAt_map_eval_eq_toNat (c288s s w) w 8 (by norm_num) ?_
  intro j hj
  unfold c288s b32
  rw [Vector.getElem_ofFn]
  rw [if_neg (by omega : ¬ 32 * 8 + j < 256)]
  simp only [show (32 * 8 + j) % 32 = j from by omega]

/-! ## `eval`-agreement congruences for the round-loop assembly maps -/

section EvalCongr

variable {env env' : ProverEnvironment (F p2)}

theorem eval_q768_congr {v : Var (fields 768) (F p2)} (h : eval env v = eval env' v) (k : ℕ) :
    eval env (q768 v k) = eval env' (q768 v k) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold q768 a768
  rw [Vector.getElem_ofFn]
  exact eval_getElem_congr h _ _

theorem eval_st768_congr {v : Var (fields 768) (F p2)} (h : eval env v = eval env' v) :
    eval env (st768 v) = eval env' (st768 v) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold st768 a768
  rw [Vector.getElem_ofFn]
  exact eval_getElem_congr h _ _

theorem eval_c288s_congr {s : Var (fields 256) (F p2)} {w : Var (fields 32) (F p2)}
    (hs : eval env s = eval env' s) (hw : eval env w = eval env' w) :
    eval env (c288s s w) = eval env' (c288s s w) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold c288s a256 b32
  rw [Vector.getElem_ofFn]
  split
  · exact eval_getElem_congr hs _ _
  · exact eval_getElem_congr hw _ _

end EvalCongr

/-- The 8 state words of `c288s s w` are the words of `s`. -/
theorem ofFn_wordAt_c288s (env : Environment (F p2)) (s : Var (fields 256) (F p2))
    (w : Var (fields 32) (F p2)) :
    (Vector.ofFn fun i : Fin 8 => wordAt 32 (Vector.map (Expression.eval env) (c288s s w)) i.val)
      = Vector.ofFn fun i : Fin 8 => wordAt 32 (Vector.map (Expression.eval env) s) i.val := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn, wordAt_eval_c288s_state env s w i hi]

namespace Rounds16

/-- Explicit `ConstantLength` for the 16-round fold body (345 witnesses per round).
    Naming it lets the fold in `main` skip the expensive `infer_constant_length`
    synthesis (which times out on the `c288s`/`q768` window wrappers), and lets the
    cost/R1CS lemmas fold with the same instance. -/
def constantLength (r0 : ℕ) (v : Var (fields 768) (F p2)) :
    Circuit.ConstantLength (fun (x : Var (fields 256) (F p2) × Fin 16) =>
      Round.circuit (kAt (r0 + x.2.val)) (c288s x.1 (q768 v (8 + x.2.val)))) where
  localLength := 345
  localLength_eq _ _ := by
    simp [circuit_norm, Round.circuit, Round.elaborated]

/-- Closed-form variable-level accumulator after `k` rounds, starting from the
    256-bit prefix `st768 v` at witness offset `i₀`. Phrased via the round
    circuit's own `.output`, so the fold bridge is a `Fin.foldl` unfolding. -/
def stateVar256 (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) : ℕ → fields 256 (Expression (F p2))
  | 0 => st768 v
  | k + 1 => (Round.circuit (kAt (r0 + k))).output
      (c288s (stateVar256 r0 i₀ v k) (q768 v (8 + k))) (i₀ + k * 345)

lemma fin_foldl_eq_stateVar256 (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) (k : ℕ) :
    Fin.foldl k (fun (acc : fields 256 (Expression (F p2))) (i : Fin k) =>
      (Round.circuit (kAt (r0 + i.val))).output (c288s acc (q768 v (8 + i.val)))
        (i₀ + i.val * 345)) (st768 v)
      = stateVar256 r0 i₀ v k := by
  induction k with
  | zero => simp [stateVar256, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last]
    rw [stateVar256]
    rw [show Fin.foldl k (fun (acc : fields 256 (Expression (F p2))) (i : Fin k) =>
          (Round.circuit (kAt (r0 + i.castSucc.val))).output (c288s acc (q768 v (8 + i.castSucc.val)))
            (i₀ + i.castSucc.val * 345)) (st768 v)
        = Fin.foldl k (fun (acc : fields 256 (Expression (F p2))) (i : Fin k) =>
          (Round.circuit (kAt (r0 + i.val))).output (c288s acc (q768 v (8 + i.val)))
            (i₀ + i.val * 345)) (st768 v) from rfl, ih]

/-- The fold accumulator at index `⟨k, h⟩` equals `stateVar256 … k`. The accumulator
    type is spelled `fields 256 (Expression …)` (not `Var …`) so the LHS matches the
    `circuit_norm`-normalized `h_holds` syntactically. -/
lemma foldlAcc_eq_stateVar256 (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) (k : ℕ) (h : k < 16) :
    Circuit.FoldlM.foldlAcc (β := fields 256 (Expression (F p2))) i₀ (Vector.finRange 16)
      (fun s (i : Fin 16) => subcircuit (Round.circuit (kAt (r0 + i.val)))
        (c288s s (q768 v (8 + i.val)))) (st768 v) ⟨k, h⟩ =
      stateVar256 r0 i₀ v k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVar256 r0 i₀ v k

/-- `foldlAcc` bridge in the `Var`-spelled accumulator type, which is how the
`computableWitness` peeling lemmas present the fold. -/
lemma foldlAcc_eq_stateVar256_var (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) (k : ℕ) (h : k < 16) :
    Circuit.FoldlM.foldlAcc (β := Var (fields 256) (F p2)) i₀ (Vector.finRange 16)
      (fun s (i : Fin 16) => subcircuit (Round.circuit (kAt (r0 + i.val)))
        (c288s s (q768 v (8 + i.val)))) (st768 v) ⟨k, h⟩ =
      stateVar256 r0 i₀ v k :=
  foldlAcc_eq_stateVar256 r0 i₀ v k h

/-- The loop's final output, spelled through `subcircuit … |>.output` as the
`foldlRange` output lemma produces it. -/
lemma fin_foldl_subcircuit_eq_stateVar256 (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) (k : ℕ) :
    Fin.foldl k (fun (acc : Var (fields 256) (F p2)) (i : Fin k) =>
      (subcircuit (Round.circuit (kAt (r0 + i.val))) (c288s acc (q768 v (8 + i.val)))).output
        (i₀ + i.val * 345)) (st768 v)
      = stateVar256 r0 i₀ v k :=
  fin_foldl_eq_stateVar256 r0 i₀ v k

/-- The accumulator after `k` rounds is a function of the loop input and of the
witnesses allocated in the first `k` round blocks. -/
theorem eval_stateVar256_of_agreesBelow (r0 i₀ : ℕ) (v : Var (fields 768) (F p2))
    {kk : ℕ} {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow kk env') (h_input : eval env v = eval env' v) :
    ∀ k : ℕ, i₀ + k * 345 ≤ kk →
      eval env (stateVar256 r0 i₀ v k) = eval env' (stateVar256 r0 i₀ v k) := by
  intro k
  induction k with
  | zero => intro _; exact eval_st768_congr h_input
  | succ k ih =>
    intro hkk
    rw [stateVar256]
    exact Round.eval_subOut_of_agreesBelow _ _ (i₀ + k * 345) (by omega) h_agree
      (eval_c288s_congr (ih (by omega)) (eval_q768_congr h_input (8 + k)))

end Rounds16

end Solution.SHA256CompressGF2
