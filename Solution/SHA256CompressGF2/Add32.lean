import Challenge.Instances.SHA256CompressGF2Canonical.Interface
import Challenge.Utils.CostR1CS
import Solution.SHA256CompressGF2.EvalCongr
import Mathlib.Tactic.LinearCombination

/-!
# `Add32`: 32-bit ripple-carry modular adder over GF(2)

The one primitive SHA-256 needs that Keccak did not: `add32 x y = (x + y) mod 2^32`
by ripple carry. Over `F 2` the carry recurrence uses the **single-product char-2
form**

  `c₀ = 0,   cᵢ₊₁ = (xᵢ + cᵢ)·(yᵢ + cᵢ) + cᵢ`

(equal to the textbook `xᵢyᵢ ⊕ cᵢ(xᵢ ⊕ yᵢ)` because `a² = a` in `F 2`), so each
carry is pinned by a single degree-2 R1CS row `(cᵢ₊₁ − cᵢ) − (xᵢ+cᵢ)(yᵢ+cᵢ) = 0`.
We witness the 31 carries `c₁..c₃₁` (the bit-31 carry-out is dropped, mod 2^32);
the 32 sum bits `sᵢ = xᵢ ⊕ yᵢ ⊕ cᵢ` are inlined expressions (no witnesses),
matching flock's `CARRIES_PER_ADD = 31` layout.

Cost per adder: 31 witnesses / 31 constraints.
-/

namespace Solution.SHA256CompressGF2
namespace Add32

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

/-- Two 32-bit operands, as bit vectors. -/
structure Inputs (F : Type) where
  x : Vector F 32
  y : Vector F 32
deriving ProvableStruct

/-! ## Total accessors -/

/-- Entry `k % 32` (total access into a 32-vector). -/
@[reducible] def at32 {α : Type} (v : Vector α 32) (k : ℕ) : α :=
  v[k % 32]'(Nat.mod_lt _ (by norm_num))

/-- Entry `k % 31` (total access into a 31-vector). -/
@[reducible] def at31 {α : Type} (v : Vector α 31) (k : ℕ) : α :=
  v[k % 31]'(Nat.mod_lt _ (by norm_num))

/-! ## Pure ripple-carry semantics over `F 2` -/

/-- Honest carry into bit `i` (`c₀ = 0`), single-product char-2 form. -/
def carryVal (xv yv : ℕ → F p2) : ℕ → F p2
  | 0 => 0
  | i + 1 =>
    let c := carryVal xv yv i
    (xv i + c) * (yv i + c) + c

/-- Full-adder numeric identity on `F 2`: bit values of sum and carry decompose
`a + b + c` exactly. -/
theorem fullAdder_val : ∀ a b c : F p2,
    ZMod.val a + ZMod.val b + ZMod.val c
      = ZMod.val (a + b + c) + 2 * ZMod.val ((a + c) * (b + c) + c) := by decide

/-- Ripple-carry invariant: partial bit sums of `x`, `y` equal partial bit sums
of the sum bits plus the outgoing carry. -/
theorem adder_invariant (xv yv : ℕ → F p2) (k : ℕ) :
    (∑ i ∈ Finset.range k, ZMod.val (xv i) * 2 ^ i)
      + (∑ i ∈ Finset.range k, ZMod.val (yv i) * 2 ^ i)
      = (∑ i ∈ Finset.range k, ZMod.val (xv i + yv i + carryVal xv yv i) * 2 ^ i)
        + ZMod.val (carryVal xv yv k) * 2 ^ k := by
  induction k with
  | zero => simp [carryVal]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hfa := fullAdder_val (xv n) (yv n) (carryVal xv yv n)
    have hstep : carryVal xv yv (n + 1)
        = (xv n + carryVal xv yv n) * (yv n + carryVal xv yv n) + carryVal xv yv n := rfl
    have hfa' := congrArg (· * 2 ^ n) hfa
    simp only [add_mul] at hfa'
    rw [hstep, pow_succ]
    ring_nf
    ring_nf at hfa' ih
    linarith [ih, hfa']

/-- A sum of `k` bits weighted by `2^i` is `< 2^k`. -/
theorem sum_bits_lt (f : ℕ → F p2) (k : ℕ) :
    ∑ i ∈ Finset.range k, ZMod.val (f i) * 2 ^ i < 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hb : ZMod.val (f n) ≤ 1 := by
      have := ZMod.val_lt (f n); simp only [p2] at this; omega
    have hle : ZMod.val (f n) * 2 ^ n ≤ 2 ^ n := by
      calc ZMod.val (f n) * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ hb
        _ = 2 ^ n := one_mul _
    linarith

/-- The ripple-carry sum bits recompose to `(x + y) mod 2^32`. -/
theorem adder_correct (xv yv : ℕ → F p2) :
    (∑ i ∈ Finset.range 32, ZMod.val (xv i + yv i + carryVal xv yv i) * 2 ^ i)
      = ((∑ i ∈ Finset.range 32, ZMod.val (xv i) * 2 ^ i)
          + (∑ i ∈ Finset.range 32, ZMod.val (yv i) * 2 ^ i)) % 2 ^ 32 := by
  have hinv := adder_invariant xv yv 32
  have hlt := sum_bits_lt (fun i => xv i + yv i + carryVal xv yv i) 32
  have hc : ZMod.val (carryVal xv yv 32) < 2 := by
    have := ZMod.val_lt (carryVal xv yv 32); simp only [p2] at this; omega
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  rw [h32] at hinv hlt ⊢
  omega

/-! ## The circuit -/

/-- Carry into bit `i` as an expression over the witnessed carries
(`c₀ = 0`; `cᵢ = carries[i-1]` for `i ≥ 1`). -/
def carryE (carries : Vector (Expression (F p2)) 31) (i : ℕ) : Expression (F p2) :=
  if i = 0 then 0 else at31 carries (i - 1)

/-- Witness the 31 carries, pin each with the single-product row
`(cᵢ₊₁ − cᵢ) − (xᵢ+cᵢ)(yᵢ+cᵢ) = 0`, and return the 32 inlined sum bits. -/
def main (input : Var Inputs (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let x := input.x
  let y := input.y
  let carries ← witnessVector 31 (fun env => Vector.ofFn fun i : Fin 31 =>
    carryVal (fun j => (at32 x j).eval env) (fun j => (at32 y j).eval env) (i.val + 1))
  Circuit.forEach (Vector.finRange 31) (fun i =>
    assertZero ((at31 carries i.val - carryE carries i.val)
      - (at32 x i.val + carryE carries i.val) * (at32 y i.val + carryE carries i.val)))
  return Vector.ofFn fun i : Fin 32 =>
    at32 x i.val + at32 y i.val + carryE carries i.val

instance elaborated : ElaboratedCircuit (F p2) Inputs (fields 32) main := by
  elaborate_circuit

/-- No preconditions: over `F 2` every wire is already a bit. -/
def Assumptions (_ : Inputs (F p2)) : Prop := True

/-- Postcondition: the output word is `(x + y) mod 2^32`. -/
def Spec (input : Inputs (F p2)) (out : fields 32 (F p2)) : Prop :=
  toNat out = (toNat input.x + toNat input.y) % 2 ^ 32

/-- `toNat` on a 32-vector is the range-32 bit sum. -/
theorem toNat_eq_sum (v : Vector (F p2) 32) :
    toNat v = ∑ j ∈ Finset.range 32, bitAt v j * 2 ^ j := by
  unfold Challenge.F2Bits.toNat Challenge.F2Bits.wordAt
  exact Finset.sum_congr rfl fun j hj => by norm_num

/-- In-range `bitAt` is `ZMod.val` of the entry. -/
theorem bitAt_eq {N : ℕ} (v : Vector (F p2) N) (j : ℕ) (hj : j < N) :
    bitAt v j = ZMod.val (v[j]'hj) := by
  unfold Challenge.F2Bits.bitAt
  rw [getElem?_pos v j hj]
  rfl

theorem soundness : Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec, carryE, at32, at31]
  obtain ⟨h_input_x, h_input_y⟩ := h_input
  -- constraints pin each witnessed carry to the honest carry chain
  have hget : ∀ n : ℕ, n < 31 → env.get (i₀ + n)
      = carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 := h_holds ⟨0, by norm_num⟩
      simp only [Nat.zero_mod, Nat.add_zero, reduceIte, circuit_norm] at h0
      have hunf : carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (0 + 1)
          = (Expression.eval env (input_var_x[0 % 32]'(by norm_num)) + 0)
              * (Expression.eval env (input_var_y[0 % 32]'(by norm_num)) + 0) + 0 := rfl
      rw [Nat.add_zero, hunf]
      simp only [Nat.zero_mod] at *
      linear_combination h0
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hc := h_holds ⟨n + 1, hn⟩
      simp only [Nat.mod_eq_of_lt hn, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
        Nat.mod_eq_of_lt (show n < 31 by omega), circuit_norm] at hc
      rw [hprev] at hc
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
      linear_combination hc
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
  -- rewrite the three `toNat`s as bit sums and conclude with `adder_correct`
  rw [toNat_eq_sum, toNat_eq_sum, toNat_eq_sum]
  have key := adder_correct
    (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
    (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
  refine Eq.trans ?_ (Eq.trans key ?_)
  · -- LHS: output bits are the inlined sum bits
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj32 := Finset.mem_range.mp hj
    rw [bitAt_eq _ j hj32, Vector.getElem_map, Vector.getElem_ofFn]
    simp only [circuit_norm]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [reduceIte, circuit_norm, carryVal]
    · simp only [if_neg hj0]
      rw [show Expression.eval env (var { index := i₀ + (j - 1) % 31 })
            = env.get (i₀ + (j - 1) % 31) from rfl,
        Nat.mod_eq_of_lt (show j - 1 < 31 by omega), hget (j - 1) (by omega),
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
  · -- RHS: the evaluated inputs are the input bit values
    try simp only []
    have hXsum : (∑ j ∈ Finset.range 32,
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

theorem completeness : Completeness (F p2) main Assumptions := by
  circuit_proof_start [main, carryE, at32, at31]
  have henv : ∀ k : ℕ, (hk : k < 31) → env.get (i₀ + k)
      = carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (k + 1) := by
    intro k hk
    have h := h_env ⟨k, hk⟩
    simp only [Vector.getElem_ofFn] at h
    exact h
  intro i
  obtain ⟨iv, hiv⟩ := i
  cases iv with
  | zero =>
    have h0 := henv 0 (by norm_num)
    rw [Nat.add_zero] at h0
    simp only [Nat.zero_mod, reduceIte, circuit_norm]
    rw [h0]
    have hunf : carryVal (fun j => Expression.eval env.toEnvironment (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (fun j => Expression.eval env.toEnvironment (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num))))
                 (0 + 1)
        = (Expression.eval env.toEnvironment (input_var_x[0 % 32]'(by norm_num)) + 0)
            * (Expression.eval env.toEnvironment (input_var_y[0 % 32]'(by norm_num)) + 0) + 0 := rfl
    rw [hunf]
    simp only [Nat.zero_mod]
    ring
  | succ n =>
    simp only [Nat.mod_eq_of_lt hiv, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
      Nat.mod_eq_of_lt (show n < 31 by omega), circuit_norm]
    rw [henv (n + 1) hiv, henv n (by omega)]
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

/-- The adder as a composable `FormalCircuit`. -/
def circuit : FormalCircuit (F p2) Inputs (fields 32) :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

/-- Componentwise agreement builds struct agreement. -/
theorem eval_mk_congr {x y : Var (fields 32) (F p2)} {env env' : ProverEnvironment (F p2)}
    (hx : eval env x = eval env' x) (hy : eval env y = eval env' y) :
    eval env (⟨x, y⟩ : Var Inputs (F p2)) = eval env' (⟨x, y⟩ : Var Inputs (F p2)) := by
  simp only [circuit_norm] at hx hy ⊢
  rw [hx, hy]

theorem eval_x_congr {v : Var Inputs (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) : eval env v.x = eval env' v.x := by
  have h2 := congrArg (fun s : Inputs (F p2) => s.x) h
  simpa [circuit_norm] using h2

theorem eval_y_congr {v : Var Inputs (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) : eval env v.y = eval env' v.y := by
  have h2 := congrArg (fun s : Inputs (F p2) => s.y) h
  simpa [circuit_norm] using h2

/-- The witness generator reads the operands only through `at32`; agreement on the
operand vector makes the whole reader function equal, hence the recursive
`carryVal` chain agrees without any induction. -/
theorem eval_at32_fun_congr {v : Var (fields 32) (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) :
    (fun j => Expression.eval env.toEnvironment (at32 v j))
      = (fun j => Expression.eval env'.toEnvironment (at32 v j)) :=
  funext fun _ => eval_getElem_congr h _ _

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
  · intro _ h_input
    rw [eval_at32_fun_congr (eval_x_congr h_input), eval_at32_fun_congr (eval_y_congr h_input)]
  · intro _
    trivial

theorem subcircuit_localLength (inp : Var Inputs (F p2)) (m : ℕ) :
    (subcircuit circuit inp).localLength m = 31 := rfl

/-- The witnessed carry expression at index `i` reads only variables in the
adder's own 31-cell block. -/
theorem eval_carryE_of_agreesBelow (n : ℕ) {k : ℕ} (hk : n + 31 ≤ k)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow k env') (i : ℕ) :
    Expression.eval env.toEnvironment
        (carryE (Vector.mapRange 31 fun j => var ⟨n + j⟩) i)
      = Expression.eval env'.toEnvironment
        (carryE (Vector.mapRange 31 fun j => var ⟨n + j⟩) i) := by
  unfold carryE at31
  split
  · rfl
  · have hmod : (i - 1) % 31 < 31 := Nat.mod_lt _ (by norm_num)
    simp only [circuit_norm]
    exact h_agree (n + (i - 1) % 31) (by omega)

/-- The adder's output is affine in its inputs and its own witnessed carries, so
agreement needs both the input agreement and agreement below the block top. -/
theorem eval_subOut_of_agreesBelow (inp : Var Inputs (F p2)) (n : ℕ) {k : ℕ} (hk : n + 31 ≤ k)
    {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow k env') (h_input : eval env inp = eval env' inp) :
    eval env ((subcircuit circuit inp).output n)
      = eval env' ((subcircuit circuit inp).output n) := by
  have hout : (subcircuit circuit inp).output n
      = Vector.ofFn (fun i : Fin 32 =>
          at32 inp.x i.val + at32 inp.y i.val
            + carryE (Vector.mapRange 31 fun j => var ⟨n + j⟩) i.val) := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  refine eval_fields_of_getElem fun i hi => ?_
  rw [hout, Vector.getElem_ofFn]
  simp only [circuit_norm]
  rw [eval_getElem_congr (eval_x_congr h_input), eval_getElem_congr (eval_y_congr h_input),
    eval_carryE_of_agreesBelow n hk h_agree i]

end ComputableWitness

end Add32
end Solution.SHA256CompressGF2
