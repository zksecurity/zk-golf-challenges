import Solution.Blake3CompressGF2Canonical.Add32Theorems
import Challenge.Utils.CostR1CSCanonical

/-!
# `Add32` in canonical (C = identity) form: pinned/shallow encoding

The ripple-carry adder whose semantics is proved in `Add32Theorems.lean`, with
every constraint row's `C`-side a single fresh witness variable (identity `C`).

To keep the carry a *single variable* (shallow, so subcircuit composition does
not blow up `whnf`), we split each bit into **two** canonical rows:

* product row `dᵢ − (xᵢ+cᵢ)(yᵢ+cᵢ) = 0`   (C-side = the fresh product var `dᵢ`),
* carry row  `cᵢ₊₁ − (cᵢ + dᵢ)·1 = 0`      (C-side = the fresh carry var `cᵢ₊₁`;
  the obligation has no linear case, so the constant-one `B` is explicit).

We witness the 31 products `d₀..d₃₀` and then the 31 carries `c₁..c₃₁`, in the
same order the constraint rows pin them: row `t` pins the block's variable `t`
exactly (the ordered `isR1CS_Cidentity` discipline), so the `C` matrix is the
identity, not a permutation.
Cost per adder: 62 witnesses / 62 constraints.
-/

namespace Solution.Blake3CompressGF2Canonical.Add32Canon

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS
open Solution.Blake3CompressGF2Canonical.Add32 (at32 at31 carryVal carryE Inputs
  adder_correct toNat_eq_sum bitAt_eq)

def main (input : Var Inputs (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let x := input.x; let y := input.y
  let prods ← witnessVector 31 (fun env => Vector.ofFn fun i : Fin 31 =>
    let c := carryVal (fun j => (at32 x j).eval env) (fun j => (at32 y j).eval env) i.val
    ((at32 x i.val).eval env + c) * ((at32 y i.val).eval env + c))
  let carries ← witnessVector 31 (fun env => Vector.ofFn fun i : Fin 31 =>
    carryVal (fun j => (at32 x j).eval env) (fun j => (at32 y j).eval env) (i.val + 1))
  Circuit.forEach (Vector.finRange 31) (fun i =>
    assertZero (at31 prods i.val
      - (at32 x i.val + carryE carries i.val) * (at32 y i.val + carryE carries i.val)))
  Circuit.forEach (Vector.finRange 31) (fun i =>
    assertZero (at31 carries i.val - (carryE carries i.val + at31 prods i.val) * 1))
  return Vector.ofFn fun i : Fin 32 =>
    at32 x i.val + at32 y i.val + carryE carries i.val

instance elaborated : ElaboratedCircuit (F p2) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p2) main Add32.Assumptions Add32.Spec := by
  circuit_proof_start [main, Add32.Spec, carryE, at32, at31]
  obtain ⟨h_input_x, h_input_y⟩ := h_input
  obtain ⟨h_prod, h_carry⟩ := h_holds
  -- the two constraint families pin each witnessed carry to the honest carry chain
  have hget : ∀ n : ℕ, n < 31 → env.get (i₀ + 31 + n)
      = carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      have hp0 := h_prod ⟨0, by norm_num⟩
      have hc0 := h_carry ⟨0, by norm_num⟩
      simp only [Nat.zero_mod, Nat.add_zero, reduceIte, circuit_norm] at hp0 hc0
      have hunf : carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (0 + 1)
          = (Expression.eval env (input_var_x[0 % 32]'(by norm_num)) + 0)
              * (Expression.eval env (input_var_y[0 % 32]'(by norm_num)) + 0) + 0 := rfl
      rw [Nat.add_zero, hunf]
      simp only [Nat.zero_mod] at *
      linear_combination hc0 + hp0
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hp := h_prod ⟨n + 1, hn⟩
      have hc := h_carry ⟨n + 1, hn⟩
      simp only [Nat.mod_eq_of_lt hn, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
        Nat.mod_eq_of_lt (show n < 31 by omega), circuit_norm] at hp hc
      rw [hprev] at hp hc
      have hunf : carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (n + 1 + 1)
          = (Expression.eval env (input_var_x[(n+1) % 32]'(Nat.mod_lt _ (by norm_num)))
                + carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                    (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) (n + 1))
              * (Expression.eval env (input_var_y[(n+1) % 32]'(Nat.mod_lt _ (by norm_num)))
                + carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                    (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) (n + 1))
              + carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                  (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) (n + 1) := rfl
      rw [hunf]
      linear_combination hc + hp
  -- pointwise input-evaluation bridges
  have hx : ∀ (k : ℕ) (hk : k < 32),
      Expression.eval env (input_var_x[k]'hk) = input_x[k]'hk := by
    intro k hk
    have h2 := Vector.ext_iff.mp h_input_x k hk
    rwa [Vector.getElem_map] at h2
  have hy : ∀ (k : ℕ) (hk : k < 32),
      Expression.eval env (input_var_y[k]'hk) = input_y[k]'hk := by
    intro k hk
    have h2 := Vector.ext_iff.mp h_input_y k hk
    rwa [Vector.getElem_map] at h2
  rw [toNat_eq_sum, toNat_eq_sum, toNat_eq_sum]
  have key := adder_correct
    (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
    (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
  refine Eq.trans ?_ (Eq.trans key ?_)
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj32 := Finset.mem_range.mp hj
    rw [bitAt_eq _ j hj32, Vector.getElem_map, Vector.getElem_ofFn]
    simp only [circuit_norm]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [reduceIte, circuit_norm, carryVal]
    · simp only [if_neg hj0]
      rw [show Expression.eval env (var { index := i₀ + 31 + (j - 1) % 31 })
            = env.get (i₀ + 31 + (j - 1) % 31) from rfl,
        Nat.mod_eq_of_lt (show j - 1 < 31 by omega), hget (j - 1) (by omega),
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
  · have hXsum : (∑ j ∈ Finset.range 32,
        ZMod.val (Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num)))) * 2 ^ j)
        = ∑ j ∈ Finset.range 32, bitAt input_x j * 2 ^ j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj32 := Finset.mem_range.mp hj
      rw [bitAt_eq _ j hj32]
      simp only [Nat.mod_eq_of_lt hj32]
      rw [hx j hj32]
    have hYsum : (∑ j ∈ Finset.range 32,
        ZMod.val (Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) * 2 ^ j)
        = ∑ j ∈ Finset.range 32, bitAt input_y j * 2 ^ j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj32 := Finset.mem_range.mp hj
      rw [bitAt_eq _ j hj32]
      simp only [Nat.mod_eq_of_lt hj32]
      rw [hy j hj32]
    rw [hXsum, hYsum]

theorem completeness : Completeness (F p2) main Add32.Assumptions := by
  circuit_proof_start [main, Add32.Spec, carryE, at32, at31]
  obtain ⟨he_p, he_c, -⟩ := h_env
  have henv : ∀ k : ℕ, (hk : k < 31) → env.get (i₀ + 31 + k)
      = carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (k + 1) := by
    intro k hk
    have h := he_c ⟨k, hk⟩
    simp only [Vector.getElem_ofFn] at h
    exact h
  have henvp : ∀ k : ℕ, (hk : k < 31) → env.get (i₀ + k)
      = (Expression.eval env.toEnvironment (input_var_x[k % 32]'(Nat.mod_lt _ (by norm_num)))
          + carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                     (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) k)
        * (Expression.eval env.toEnvironment (input_var_y[k % 32]'(Nat.mod_lt _ (by norm_num)))
          + carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                     (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) k) := by
    intro k hk
    have h := he_p ⟨k, hk⟩
    simp only [Vector.getElem_ofFn] at h
    exact h
  refine ⟨?_, ?_⟩
  · -- product constraints: dᵢ = (xᵢ+cᵢ)(yᵢ+cᵢ)
    intro i
    obtain ⟨iv, hiv⟩ := i
    cases iv with
    | zero =>
      simp only [Nat.zero_mod, reduceIte, circuit_norm]
      have hp0 := henvp 0 (by norm_num)
      simp only [Nat.add_zero, Nat.zero_mod, carryVal] at hp0 ⊢
      rw [hp0]; ring
    | succ n =>
      simp only [Nat.mod_eq_of_lt hiv, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
        Nat.mod_eq_of_lt (show n < 31 by omega), circuit_norm]
      rw [henvp (n + 1) hiv, henv n (by omega)]
      ring
  · -- carry constraints: cᵢ₊₁ = cᵢ + dᵢ
    intro i
    obtain ⟨iv, hiv⟩ := i
    cases iv with
    | zero =>
      simp only [Nat.zero_mod, reduceIte, circuit_norm]
      have hc0 := henv 0 (by norm_num)
      have hp0 := henvp 0 (by norm_num)
      simp only [Nat.add_zero, Nat.zero_mod, carryVal] at hc0 hp0 ⊢
      rw [hc0, hp0]; ring
    | succ n =>
      simp only [Nat.mod_eq_of_lt hiv, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
        Nat.mod_eq_of_lt (show n < 31 by omega), circuit_norm]
      rw [henv (n + 1) hiv, henvp (n + 1) hiv, henv n (by omega)]
      have hunf : carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (n + 1 + 1)
          = (Expression.eval env.toEnvironment (input_var_x[(n+1) % 32]'(Nat.mod_lt _ (by norm_num)))
                + carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                    (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) (n + 1))
              * (Expression.eval env.toEnvironment (input_var_y[(n+1) % 32]'(Nat.mod_lt _ (by norm_num)))
                + carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                    (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) (n + 1))
              + carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                  (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) (n + 1) := rfl
      rw [hunf]
      ring

def circuit : FormalCircuit (F p2) Inputs (fields 32) :=
  { main, elaborated, Assumptions := Add32.Assumptions, Spec := Add32.Spec, soundness, completeness }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas
open Solution.Blake3CompressGF2Canonical (eval_fields_of_getElem eval_getElem_congr
  eval_varFromOffset_of_agreesBelow)

/-- Pointwise agreement on the `at32` reads of an operand vector. The canonical
adder's product generator reads `at32 x i` directly as well as through
`carryVal`, so pointwise operand agreement is used directly. -/
theorem eval_at32_pt_congr {v : Var (fields 32) (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) (j : ℕ) :
    Expression.eval env.toEnvironment (at32 v j)
      = Expression.eval env'.toEnvironment (at32 v j) :=
  eval_getElem_congr h _ _

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessVector_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · -- the product witnesses read the operands only, via `at32`
    intro _ h_input
    simp only [eval_at32_pt_congr (Add32.eval_x_congr h_input),
      eval_at32_pt_congr (Add32.eval_y_congr h_input)]
  · -- likewise the carry witnesses
    intro _ h_input
    simp only [eval_at32_pt_congr (Add32.eval_x_congr h_input),
      eval_at32_pt_congr (Add32.eval_y_congr h_input)]
  · intro _
    trivial
  · intro _
    trivial

theorem subcircuit_localLength (inp : Var Inputs (F p2)) (m : ℕ) :
    (subcircuit circuit inp).localLength m = 62 := rfl

/-- The canonical adder witnesses the 31 products first, then the 31 carries, so
the inlined sum bits read the carry block at relative offset 31. -/
theorem eval_subOut_of_agreesBelow (inp : Var Inputs (F p2)) (n : ℕ) {k : ℕ} (hk : n + 62 ≤ k)
    {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow k env') (h_input : eval env inp = eval env' inp) :
    eval env ((subcircuit circuit inp).output n)
      = eval env' ((subcircuit circuit inp).output n) := by
  have hout : (subcircuit circuit inp).output n
      = Vector.ofFn (fun i : Fin 32 =>
          at32 inp.x i.val + at32 inp.y i.val
            + carryE (Vector.mapRange 31 fun j => var ⟨n + 31 + j⟩) i.val) := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  refine eval_fields_of_getElem fun i hi => ?_
  rw [hout, Vector.getElem_ofFn]
  simp only [circuit_norm]
  rw [eval_getElem_congr (Add32.eval_x_congr h_input),
    eval_getElem_congr (Add32.eval_y_congr h_input),
    Add32.eval_carryE_of_agreesBelow (n + 31) (by omega) h_agree i]

end ComputableWitness

end Solution.Blake3CompressGF2Canonical.Add32Canon
