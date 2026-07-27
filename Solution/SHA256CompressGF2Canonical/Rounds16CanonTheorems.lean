import Solution.SHA256CompressGF2Canonical.RoundCanon
import Solution.SHA256CompressGF2.Rounds16Theorems

/-!
# Private fold bridges for `Rounds16Canon`
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Rounds16Canon

/-- Explicit `ConstantLength` for the 16-round canonical fold body (562 witnesses
    per round). -/
def constantLength (r0 : ℕ) (v : Var (fields 768) (F p2)) :
    Circuit.ConstantLength (fun (x : Var (fields 256) (F p2) × Fin 16) =>
      RoundCanon.circuit (kAt (r0 + x.2.val)) (c288s x.1 (q768 v (8 + x.2.val)))) where
  localLength := 562
  localLength_eq _ _ := by
    simp [circuit_norm, RoundCanon.circuit, RoundCanon.elaborated]

/-- Closed-form variable-level accumulator after `k` rounds. -/
def stateVar256 (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) : ℕ → fields 256 (Expression (F p2))
  | 0 => st768 v
  | k + 1 => (RoundCanon.circuit (kAt (r0 + k))).output
      (c288s (stateVar256 r0 i₀ v k) (q768 v (8 + k))) (i₀ + k * 562)

lemma fin_foldl_eq_stateVar256 (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) (k : ℕ) :
    Fin.foldl k (fun (acc : fields 256 (Expression (F p2))) (i : Fin k) =>
      (RoundCanon.circuit (kAt (r0 + i.val))).output (c288s acc (q768 v (8 + i.val)))
        (i₀ + i.val * 562)) (st768 v)
      = stateVar256 r0 i₀ v k := by
  induction k with
  | zero => simp [stateVar256, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last]
    rw [stateVar256]
    rw [show Fin.foldl k (fun (acc : fields 256 (Expression (F p2))) (i : Fin k) =>
          (RoundCanon.circuit (kAt (r0 + i.castSucc.val))).output (c288s acc (q768 v (8 + i.castSucc.val)))
            (i₀ + i.castSucc.val * 562)) (st768 v)
        = Fin.foldl k (fun (acc : fields 256 (Expression (F p2))) (i : Fin k) =>
          (RoundCanon.circuit (kAt (r0 + i.val))).output (c288s acc (q768 v (8 + i.val)))
            (i₀ + i.val * 562)) (st768 v) from rfl, ih]

lemma foldlAcc_eq_stateVar256 (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) (k : ℕ) (h : k < 16) :
    Circuit.FoldlM.foldlAcc (β := fields 256 (Expression (F p2))) i₀ (Vector.finRange 16)
      (fun s (i : Fin 16) => subcircuit (RoundCanon.circuit (kAt (r0 + i.val)))
        (c288s s (q768 v (8 + i.val)))) (st768 v) ⟨k, h⟩ =
      stateVar256 r0 i₀ v k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVar256 r0 i₀ v k

/-- `foldlAcc` bridge in the `Var`-spelled accumulator type, which is how the
`computableWitness` peeling lemmas present the fold. -/
lemma foldlAcc_eq_stateVar256_var (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) (k : ℕ) (h : k < 16) :
    Circuit.FoldlM.foldlAcc (β := Var (fields 256) (F p2)) i₀ (Vector.finRange 16)
      (fun s (i : Fin 16) => subcircuit (RoundCanon.circuit (kAt (r0 + i.val)))
        (c288s s (q768 v (8 + i.val)))) (st768 v) ⟨k, h⟩ =
      stateVar256 r0 i₀ v k :=
  foldlAcc_eq_stateVar256 r0 i₀ v k h

/-- The loop's final output, spelled through `subcircuit … |>.output` as the
`foldlRange` output lemma produces it. -/
lemma fin_foldl_subcircuit_eq_stateVar256 (r0 i₀ : ℕ) (v : Var (fields 768) (F p2)) (k : ℕ) :
    Fin.foldl k (fun (acc : Var (fields 256) (F p2)) (i : Fin k) =>
      (subcircuit (RoundCanon.circuit (kAt (r0 + i.val)))
        (c288s acc (q768 v (8 + i.val)))).output (i₀ + i.val * 562)) (st768 v)
      = stateVar256 r0 i₀ v k :=
  fin_foldl_eq_stateVar256 r0 i₀ v k

/-- The accumulator after `k` canonical rounds is a function of the loop input and
of the witnesses allocated in the first `k` round blocks. -/
theorem eval_stateVar256_of_agreesBelow (r0 i₀ : ℕ) (v : Var (fields 768) (F p2))
    {kk : ℕ} {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow kk env') (h_input : eval env v = eval env' v) :
    ∀ k : ℕ, i₀ + k * 562 ≤ kk →
      eval env (stateVar256 r0 i₀ v k) = eval env' (stateVar256 r0 i₀ v k) := by
  intro k
  induction k with
  | zero => intro _; exact eval_st768_congr h_input
  | succ k ih =>
    intro hkk
    rw [stateVar256]
    exact RoundCanon.eval_subOut_of_agreesBelow _ _ (i₀ + k * 562) (by omega) h_agree
      (eval_c288s_congr (ih (by omega)) (eval_q768_congr h_input (8 + k)))

end Rounds16Canon

end Solution.SHA256CompressGF2
