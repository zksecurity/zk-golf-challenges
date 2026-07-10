import Solution.Secp256k1ScalarMul.LessThan
import Solution.Secp256k1ScalarMul.EqViaCarries
import Solution.Secp256k1ScalarMul.MulModTheorems

/-!
# RSA modular multiplication (gadget G5)

This file defines `MulMod` (gadget **G5**), the core gadget of the RSA circuit
family: a `FormalCircuit` computing `c = a · b mod n` over normalized big
integers.

## Strategy

Witness the quotient `q = (a·b)/n` and remainder `r = (a·b)%n` as `BigInt m`
values, range-check both to be normalized, and then certify the two facts that
characterize the remainder:

- `a · b = q · n + r` as integers — checked via `EqViaCarries` on the
  schoolbook convolution coefficients of `a·b` and `q·n + r`;
- `r < n` — checked via `LessThan`.

Together with `Nat.div_add_mod` these yield `r = (a·b) % n`.

Soundness and completeness are fully proved here, with the arithmetic content
factored into the `mulMod_soundness_core` / `mulMod_completeness_core` lemmas.
-/

namespace Solution.Secp256k1ScalarMul
open Solution.Secp256k1ScalarMul.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod

/-- Inputs of `MulMod`: the two operands `a`, `b` and the `modulus`. -/
structure Inputs (m : ℕ) (F : Type) where
  a : BigInt m F
  b : BigInt m F
  modulus : BigInt m F
deriving ProvableStruct

/-- Natural-number value of a witnessed limb vector under a prover environment,
little-endian base `2^B`. Used only inside witness generators. -/
private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Secp256k1ScalarMul.Limbs.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)


/-- Witness the `m·m` partial products `a[i]·b[j]` of two big integers as fresh
cells and assert each equals the corresponding product, returning the *affine*
coefficient vector `bigIntMulVars` of the schoolbook convolution.

Each product assert `a[i]·b[j] − pp[i·m+j] = 0` is a single rank-1 (R1CS-clean)
row, and the returned coefficient vector is a linear form over the witnessed
products, so `EqViaCarries` sees only affine inputs. -/
def witnessedMul (a b : Var (BigInt m) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) (2 * m - 1)) := do
  -- witness the product matrix pp[i*m+j] = a[i].val * b[j].val
  let pp ← ProvableType.witness (α := fields (m * m)) fun env =>
    Vector.ofFn fun t : Fin (m * m) =>
      (Expression.eval env.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt)))
        * (Expression.eval env.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m))))
  -- assert each witnessed product equals a[i]*b[j]
  let constraints : Vector (Expression (F p)) (m * m) :=
    Vector.mapFinRange (m * m) fun t =>
      (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
        * (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        - pp[t.val]
  Circuit.forEach constraints assertZero
  return bigIntMulVars pp

/-- The output of `witnessedMul a b off` is the affine coefficient vector
`bigIntMulVars` over the freshly witnessed product matrix at offset `off`.
Isolated (own heartbeat budget) so the `MulMod` soundness/completeness proofs can
keep `witnessedMul` opaque under `circuit_proof_start`. -/
lemma witnessedMul_output (off : ℕ) (a b : Var (BigInt m) (F p)) :
    (witnessedMul a b off).1
      = bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i }) := by
  simp only [witnessedMul, circuit_norm]

/-- `witnessedMul a b` allocates exactly `m·m` cells (the product matrix). -/
lemma witnessedMul_localLength (off : ℕ) (a b : Var (BigInt m) (F p)) :
    Operations.localLength (witnessedMul a b off).2 = m * m := by
  simp only [witnessedMul, circuit_norm, Nat.mul_zero, Nat.add_zero]

/-- Soundness reading of the `witnessedMul` operations: every product assert holds,
i.e. `a[t/m]·b[t%m] = env.get (off + t)` for each `t`. Stated as the exact
`forAllNoOffset` shape that `circuit_proof_start` leaves in `h_holds`. -/
lemma witnessedMul_soundness (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (witnessedMul a b off).2) :
    ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val) := by
  simp only [witnessedMul, circuit_norm] at h
  intro t; have := h t; rw [add_neg_eq_zero] at this; exact this

/-- Per-element eval bridge for the `witnessedMul` output: combining
`witnessedMul_output` with the map-eval bridge, each coefficient of the output
evaluates like the schoolbook convolution `bigIntMulNoReduce a b`. Own budget. -/
lemma witnessedMul_eval_bridge (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (h_prod : ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val)) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (witnessedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [witnessedMul_output off a b]
  have hvec := witnessedMul_map_eval env off a b h_prod
  have := congrArg (fun v => v[k.val]) hvec
  simpa only [Vector.getElem_map] using this

/-- The `witnessedMul` operations carry no requirements (only asserts), so the
soundness-goal `forAllNoOffset Requirements` obligation is vacuously satisfied. -/
lemma witnessedMul_requirements (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (witnessedMul a b off).2 := by
  simp only [witnessedMul, circuit_norm]

/-- From `UsesLocalWitnessesCompleteness` on the `witnessedMul` block: the product
witnesses take their intended values `env.get (off+t) = a[t/m]·b[t%m]`. The
`UsesLocal` offset param `off'` may differ from the block's internal offset `off`
(they are equal up to `Nat.add_comm`); we commute on the small unfolded goal only. -/
lemma witnessedMul_usesLocalWitnesses (off off' : ℕ) (a b : Var (BigInt m) (F p))
    (penv : ProverEnvironment (F p)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (witnessedMul a b off).2) :
    ∀ t : Fin (m * m), penv.toEnvironment.get (off + t.val)
        = Expression.eval penv.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
            * Expression.eval penv.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m))) := by
  subst heq
  simp only [witnessedMul, circuit_norm] at h
  intro t
  have := h t
  simpa only [Vector.getElem_ofFn] using this

/-- Completeness reading: if every product witness holds (`env.get (off+t) =
a[t/m]·b[t%m]`), the `witnessedMul` operations are satisfiable in the sense
`circuit_proof_start` requires (the predicate the soundness/completeness goal
leaves: asserts hold; the irrelevant subcircuit/interact fields are arbitrary). -/
lemma witnessedMul_completeness (off : ℕ) (a b : Var (BigInt m) (F p)) (penv : ProverEnvironment (F p))
    (h : ∀ t : Fin (m * m), penv.toEnvironment.get (off + t.val)
        = Expression.eval penv.toEnvironment (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
            * Expression.eval penv.toEnvironment (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment, subcircuit := fun {_n} s => s.ProverAssumptions penv }
      (witnessedMul a b off).2 := by
  simp only [witnessedMul, circuit_norm]
  intro t; rw [h t]; ring

lemma evalValue_stable (B : ℕ) (x : Var (BigInt m) (F p))
    {env env' : ProverEnvironment (F p)}
    (h : eval env x = eval env' x) :
    evalValue B env x = evalValue B env' x := by
  have h_vec :
      x.map (Expression.eval env.toEnvironment)
        = x.map (Expression.eval env'.toEnvironment) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    have h_i := congrArg (fun y : BigInt m (F p) => y[i]) h
    rw [ProvableType.getElem_eval_fields_prover (env := env) x i hi,
      ProvableType.getElem_eval_fields_prover (env := env') x i hi]
    exact h_i
  simp [evalValue, h_vec]

lemma bigIntWitnessOutput_stable
    (compute : ProverEnvironment (F p) → BigInt m (F p))
    {offset k : ℕ} {env env' : ProverEnvironment (F p)}
    (h_agree : env.AgreesBelow k env') (hk : offset + m ≤ k) :
    eval env
        ((ProvableType.witness (α := BigInt m) compute).output offset)
      = eval env'
        ((ProvableType.witness (α := BigInt m) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env) _ i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env') _ i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)

lemma witnessedMul_structuralComputableWitnesses
    {Parent : TypeMap} [CircuitType Parent] (parentInput : Var Parent (F p))
    (a b : Var (BigInt m) (F p)) (offset : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment (F p)),
      offset ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput →
        eval env a = eval env' a ∧ eval env b = eval env' b) :
    ∀ env env',
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' offset ((witnessedMul a b).operations offset) := by
  intro env env'
  unfold witnessedMul
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  constructor
  · intro h_agree h_parent
    obtain ⟨ha, hb⟩ := hinput offset env env' (Nat.le_refl offset) h_agree h_parent
    apply Vector.ext
    intro t ht
    simp only [Vector.getElem_ofFn]
    have ht_div : t / m < m := by
      exact Nat.div_lt_of_lt_mul ht
    have ht_mod : t % m < m := by
      exact Nat.mod_lt _ (Nat.pos_of_neZero m)
    have ha_t :
        Expression.eval env.toEnvironment (a[t / m]'ht_div)
          = Expression.eval env'.toEnvironment (a[t / m]'ht_div) := by
      have h := congrArg (fun x : BigInt m (F p) => x[t / m]) ha
      rw [ProvableType.getElem_eval_fields_prover (env := env) a (t / m) ht_div,
        ProvableType.getElem_eval_fields_prover (env := env') a (t / m) ht_div]
      exact h
    have hb_t :
        Expression.eval env.toEnvironment (b[t % m]'ht_mod)
          = Expression.eval env'.toEnvironment (b[t % m]'ht_mod) := by
      have h := congrArg (fun x : BigInt m (F p) => x[t % m]) hb
      rw [ProvableType.getElem_eval_fields_prover (env := env) b (t % m) ht_mod,
        ProvableType.getElem_eval_fields_prover (env := env') b (t % m) ht_mod]
      exact h
    simp [ha_t, hb_t]
  · intro _
    trivial

lemma witnessedMul_output_stable
    (off : ℕ) (a b : Var (BigInt m) (F p))
    {k : ℕ} {env env' : ProverEnvironment (F p)}
    (h_agree : env.AgreesBelow k env') (hk : off + m * m ≤ k) :
    Vector.map (Expression.eval env.toEnvironment) (witnessedMul a b off).1
      = Vector.map (Expression.eval env'.toEnvironment) (witnessedMul a b off).1 := by
  rw [witnessedMul_output off a b]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  rw [eval_bigIntMulVars_coeff env.toEnvironment
      (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i }) ⟨i, hi⟩,
    eval_bigIntMulVars_coeff env'.toEnvironment
      (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i }) ⟨i, hi⟩]
  apply Finset.sum_congr rfl
  intro j _
  split
  · rename_i hidx_parts
    have hidx : j.val * m + (i - j.val) < m * m := by
      have hj := j.isLt
      have hsub : i - j.val < m := hidx_parts.2
      calc
        j.val * m + (i - j.val) < j.val * m + m := by omega
        _ = (j.val + 1) * m := by ring
        _ ≤ m * m := by
          apply Nat.mul_le_mul_right
          omega
    simp only [Vector.getElem_mapRange, Expression.eval]
    apply h_agree
    omega
  · rfl

/-- The `main` circuit of `MulMod`.

Inputs are a struct with fields `a := input.a`, `b := input.b`,
`n := input.modulus`. We witness `q = (a·b)/n` and `r = (a·b)%n`, normalize both,
certify `a·b = q·n + r` and `r < n`, and return `r`.

The schoolbook products of `a·b` and `q·n` are witnessed via `witnessedMul`, so
the coefficient vectors fed to `EqViaCarries` are affine (R1CS-row clean). -/
def main (P : BigIntParams p m) [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) := do
  let a := input.a
  let b := input.b
  let n := input.modulus

  -- 1. witness q = (a·b)/n and r = (a·b)%n as BigInt m
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let rval : ℕ := prod % evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  -- 2. normalize q and r (subcircuit calls)
  Normalize.circuit P q
  Normalize.circuit P r

  -- 3. Pc = a·b ; S = q·n + r via witnessed partial products (affine coeffs)
  let Pc ← witnessedMul a b
  let Sqn ← witnessedMul q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]

  -- 4. certify a·b = q·n + r as integers (subcircuit call)
  EqViaCarries.circuit P { lhs := Pc, rhs := S }

  -- 5. certify r < n (subcircuit call)
  LessThan.circuit P { lhs := r, rhs := n }

  -- 6. return r
  return r

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P) where
  -- q (m) + r (m) + normalize q (m*B) + normalize r (m*B)
  --   + witnessedMul a b (m*m) + witnessedMul q n (m*m)
  --   + eqViaCarries ((2m-1)*W + (2m-1)) + lessThan (m + m*B + m)
  localLength _ :=
    m + m + m * P.B + m * P.B + (m * m) + (m * m)
      + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m)
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, witnessedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, Gadgets.ToBits.rangeCheck]

/-- Preconditions: `a`, `b`, `n` are normalized, `a, b < n`, and `n` is positive
(so that the quotient `q < n` fits in `m` limbs). -/
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  a.Normalized B ∧ b.Normalized B ∧ n.Normalized B ∧
    a.value B < n.value B ∧ b.value B < n.value B ∧ 0 < n.value B

/-- Postcondition: the output is normalized and denotes `(a·b) mod n`. -/
def Spec (B : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  out.Normalized B ∧ out.value B = (a.value B * b.value B) % n.value B


/-- The `MulMod` formal circuit: `c = a · b mod n` over normalized big integers. -/
def circuit (P : BigIntParams p m) [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec,
        LessThan.circuit, LessThan.elaborated, LessThan.main,
        LessThan.Assumptions, LessThan.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hbb_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_norm, hr_norm, hAB_ops, hQN_ops, h_eq_impl, h_lt_impl⟩ := h_holds
      -- fully explicit offsets/outputs: never let Lean `whnf` the `m*m` loop offset
      have h_pAB := witnessedMul_soundness (i₀ + m + m + m * B + m * B) input_var.a input_var.b env hAB_ops
      have h_pQN := witnessedMul_soundness
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
      refine ⟨?_, witnessedMul_requirements _ _ _ _, witnessedMul_requirements _ _ _ _⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.b,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := witnessedMul_eval_bridge env (i₀ + m + m + m * B + m * B)
        input_var.a input_var.b h_pAB
      have heqQN_get := witnessedMul_eval_bridge env
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pQN
      exact mulMod_soundness_core_wm (B := B) hp i₀ env
        input_var.a input_var.b input_var.modulus
        (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).1
        (witnessedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + m * B + m * B + Operations.localLength
            (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)).1
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_norm
        heqAB_get heqQN_get h_eq_impl h_lt_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec,
        LessThan.circuit, LessThan.elaborated, LessThan.main,
        LessThan.Assumptions, LessThan.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_lt, hbb_lt, hn_pos⟩ := h_assumptions
      obtain ⟨hq_env, hr_env, hAB_uses, hQN_uses⟩ := h_env
      have h_pvAB := witnessedMul_usesLocalWitnesses (i₀ + m + m + m * B + m * B)
        (i₀ + m + m + m * B + m * B) input_var.a input_var.b env rfl hAB_uses
      have h_pvQN := witnessedMul_usesLocalWitnesses
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)
        (Operations.localLength (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2
          + (i₀ + m + m + m * B + m * B))
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env
        (Nat.add_comm _ _) hQN_uses
      have h_pAB : ∀ t : Fin (m * m),
          Expression.eval env.toEnvironment (input_var.a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
              * Expression.eval env.toEnvironment (input_var.b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
            = env.toEnvironment.get ((i₀ + m + m + m * B + m * B) + t.val) :=
        fun t => (h_pvAB t).symm
      have h_pQN : ∀ t : Fin (m * m),
          Expression.eval env.toEnvironment
              ((Vector.mapRange m fun i => var { index := i₀ + i })[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
              * Expression.eval env.toEnvironment (input_var.modulus[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
            = env.toEnvironment.get ((i₀ + m + m + m * B + m * B + Operations.localLength
                (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2) + t.val) :=
        fun t => (h_pvQN t).symm
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← h_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b % BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.b,
          Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := witnessedMul_eval_bridge env.toEnvironment (i₀ + m + m + m * B + m * B)
        input_var.a input_var.b h_pAB
      have heqQN_get := witnessedMul_eval_bridge env.toEnvironment
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pQN
      have core := mulMod_completeness_core_wm (B := B) hB hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus
        (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).1
        (witnessedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + m * B + m * B + Operations.localLength
            (witnessedMul input_var.a input_var.b (i₀ + m + m + m * B + m * B)).2)).1
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hab_lt hbb_lt hn_pos
        hqwit hrwit heqAB_get heqQN_get
      -- single explicit `exact` (lazy `.1/.2` projections; no eager `obtain` ⇒ no `whnf` blowup)
      exact ⟨core.1, core.2.1,
        witnessedMul_completeness (i₀ + m + m + m * B + m * B) input_var.a input_var.b env h_pvAB,
        witnessedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus env h_pvQN,
        core.2.2⟩

/-- From a whole-vector eval-agreement of a `fields`-shaped variable, each element
agrees. Generic-`F p` inline of `Params.eval_mem_of_map_eval_eq`. -/
private lemma eval_mem_of_map_eval_eq_gen {m' : ℕ} {env env' : ProverEnvironment (F p)}
    {x : Vector (Expression (F p)) m'}
    (h : x.map (Expression.eval env.toEnvironment) = x.map (Expression.eval env'.toEnvironment)) :
    ∀ a ∈ x, Expression.eval env.toEnvironment a = Expression.eval env'.toEnvironment a := by
  intro a ha
  simp only [Vector.mem_iff_getElem] at ha
  rcases ha with ⟨i, hi, rfl⟩
  simpa only [Vector.getElem_map] using congrArg (fun y : Vector (F p) m' => y[i]) h

/-- From `eval env x = eval env' x` of a `BigInt m` variable, its limb expressions
map to the same values under the two environments. -/
private lemma bigInt_map_eval_eq_of_eval_eq {x : Var (BigInt m) (F p)}
    {env env' : ProverEnvironment (F p)} (h : eval env x = eval env' x) :
    x.map (Expression.eval env.toEnvironment) = x.map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  rw [ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ProvableType.getElem_eval_fields_prover (env := env') x i hi]
  exact congrArg (fun y : BigInt m (F p) => y[i]) h

-- Keep `witnessedMul` and the child gadgets opaque during the structural peel so
-- `bind`/`provableWitness`/`assertion` do not recurse into their internal
-- witnesses; we discharge each block through its own `*ComputableWitnesses`
-- theorem instead.
attribute [local irreducible] witnessedMul Normalize.circuit EqViaCarries.circuit LessThan.circuit

theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  -- name each block, its output, and its starting offset
  let qc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env input.a * evalValue P.B env input.b
    let qval : ℕ := prod / evalValue P.B env input.modulus
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let q := qc.output offset
  let rOff := offset + qc.localLength offset
  let rc : Circuit (F p) (Var (BigInt m) (F p)) := ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env input.a * evalValue P.B env input.b
    let rval : ℕ := prod % evalValue P.B env input.modulus
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r := rc.output rOff
  let nqOff := rOff + rc.localLength rOff
  let nqc : Circuit (F p) Unit := Normalize.circuit P q
  let nrOff := nqOff + nqc.localLength nqOff
  let nrc : Circuit (F p) Unit := Normalize.circuit P r
  let pcOff := nrOff + nrc.localLength nrOff
  let pcv := (witnessedMul input.a input.b).output pcOff
  let sqOff := pcOff + (witnessedMul input.a input.b).localLength pcOff
  let sqv := (witnessedMul q input.modulus).output sqOff
  let eqOff := sqOff + (witnessedMul q input.modulus).localLength sqOff
  let Sv : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then sqv[k.val] + r[k.val]'h else sqv[k.val]
  let eqc : Circuit (F p) Unit := EqViaCarries.circuit P { lhs := pcv, rhs := Sv }
  let ltOff := eqOff + eqc.localLength eqOff
  have h_qlen : qc.localLength offset = m := by
    simp [qc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_rlen : rc.localLength rOff = m := by
    simp [rc, ProvableType.witness, Circuit.localLength, Operations.localLength, size]
  have h_pclen : (witnessedMul input.a input.b).localLength pcOff = m * m :=
    witnessedMul_localLength pcOff input.a input.b
  have h_sqlen : (witnessedMul q input.modulus).localLength sqOff = m * m :=
    witnessedMul_localLength sqOff q input.modulus
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · -- q witness reads only the input
    intro _ h_input
    have ha : evalValue P.B env input.a = evalValue P.B env' input.a :=
      evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.a) h_input)
    have hb : evalValue P.B env input.b = evalValue P.B env' input.b :=
      evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.b) h_input)
    have hn : evalValue P.B env input.modulus = evalValue P.B env' input.modulus :=
      evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · -- r witness reads only the input
    intro _ h_input
    have ha : evalValue P.B env input.a = evalValue P.B env' input.a :=
      evalValue_stable P.B input.a (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.a) h_input)
    have hb : evalValue P.B env input.b = evalValue P.B env' input.b :=
      evalValue_stable P.B input.b (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.b) h_input)
    have hn : evalValue P.B env input.modulus = evalValue P.B env' input.modulus :=
      evalValue_stable P.B input.modulus (by
        simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input)
    simp only [ha, hb, hn]
  · -- Normalize q (q is the first witness output)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input q nqOff
      (by
        intro k env env' hle h_agree _
        have hk : offset + m ≤ k := by
          dsimp only [nqOff, rOff] at hle
          rw [h_qlen] at hle
          omega
        exact bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · -- Normalize r (r is the second witness output)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input r nrOff
      (by
        intro k env env' hle h_agree _
        have hk : rOff + m ≤ k := by
          dsimp only [nrOff, nqOff] at hle
          rw [h_rlen] at hle
          omega
        exact bigIntWitnessOutput_stable _ h_agree hk)
      (Normalize.computableWitnesses P) env env'
  · -- witnessedMul a b : both operands are raw inputs
    exact witnessedMul_structuralComputableWitnesses input input.a input.b pcOff
      (by
        intro k env env' _ _ h_input
        have ha : eval env input.a = eval env' input.a := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.a) h_input
        have hb : eval env input.b = eval env' input.b := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.b) h_input
        exact ⟨ha, hb⟩)
      env env'
  · -- witnessedMul q n : q is a prior witness output, n is a raw input
    exact witnessedMul_structuralComputableWitnesses input q input.modulus sqOff
      (by
        intro k env env' hk_off h_agree h_input
        have hq : eval env q = eval env' q := by
          have hk : offset + m ≤ k := by
            dsimp only [sqOff, pcOff, nrOff, nqOff, rOff] at hk_off
            rw [h_qlen] at hk_off
            omega
          exact bigIntWitnessOutput_stable _ h_agree hk
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input
        exact ⟨hq, hn⟩)
      env env'
  · -- EqViaCarries: lhs = Pc (witnessedMul output), rhs = S (built from Sqn and r)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (EqViaCarries.circuit P) input { lhs := pcv, rhs := Sv } eqOff
      (by
        intro k env env' hle h_agree _
        have hk_pc : pcOff + m * m ≤ k := by
          dsimp only [eqOff, sqOff] at hle
          rw [h_pclen] at hle
          omega
        have hk_sq : sqOff + m * m ≤ k := by
          dsimp only [eqOff] at hle
          rw [h_sqlen] at hle
          omega
        have hk_r : rOff + m ≤ k := by
          dsimp only [eqOff, sqOff, pcOff, nrOff, nqOff] at hle
          rw [h_rlen] at hle
          omega
        have hPc : Vector.map (Expression.eval env.toEnvironment) pcv
            = Vector.map (Expression.eval env'.toEnvironment) pcv :=
          witnessedMul_output_stable pcOff input.a input.b h_agree hk_pc
        have hSq : Vector.map (Expression.eval env.toEnvironment) sqv
            = Vector.map (Expression.eval env'.toEnvironment) sqv :=
          witnessedMul_output_stable sqOff q input.modulus h_agree hk_sq
        have hr_vec : eval env r = eval env' r := bigIntWitnessOutput_stable _ h_agree hk_r
        have hr_map : r.map (Expression.eval env.toEnvironment)
            = r.map (Expression.eval env'.toEnvironment) := bigInt_map_eval_eq_of_eval_eq hr_vec
        have hS : Vector.map (Expression.eval env.toEnvironment) Sv
            = Vector.map (Expression.eval env'.toEnvironment) Sv := by
          apply Vector.ext
          intro i hi
          simp only [Vector.getElem_map, Sv, Vector.getElem_mapFinRange]
          split
          · rename_i hlt
            have hsq_i : Expression.eval env.toEnvironment sqv[i]
                = Expression.eval env'.toEnvironment sqv[i] := by
              have := congrArg (fun v : Vector (F p) (2 * m - 1) => v[i]'(by simpa using hi)) hSq
              simpa only [Vector.getElem_map] using this
            have hr_i : Expression.eval env.toEnvironment (r[i]'hlt)
                = Expression.eval env'.toEnvironment (r[i]'hlt) := by
              have := congrArg (fun v : Vector (F p) m => v[i]'hlt) hr_map
              simpa only [Vector.getElem_map] using this
            simp only [Expression.eval, hsq_i, hr_i]
          · have := congrArg (fun v : Vector (F p) (2 * m - 1) => v[i]'(by simpa using hi)) hSq
            simpa only [Vector.getElem_map] using this
        simp only [circuit_norm]
        rw [hPc, hS])
      (EqViaCarries.computableWitnesses P) env env'
  · -- LessThan: lhs = r (prior witness output), rhs = n (raw input)
    exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (LessThan.circuit P) input { lhs := r, rhs := input.modulus } ltOff
      (by
        intro k env env' hle h_agree h_input
        have hk_r : rOff + m ≤ k := by
          dsimp only [ltOff, eqOff, sqOff, pcOff, nrOff, nqOff] at hle
          rw [h_rlen] at hle
          omega
        have hr_vec : eval env r = eval env' r := bigIntWitnessOutput_stable _ h_agree hk_r
        have hn : eval env input.modulus = eval env' input.modulus := by
          simpa [circuit_norm] using congrArg (fun x : Inputs m (F p) => x.modulus) h_input
        simp only [circuit_norm]
        rw [bigInt_map_eval_eq_of_eval_eq hr_vec, bigInt_map_eval_eq_of_eval_eq hn])
      (LessThan.computableWitnesses P) env env'

theorem computableWitness (P : BigIntParams p m) [Fact (p > 2)] : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses ((main P) input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := (circuit P).base) (computableWitnesses P)

/-- Output-agreement: the `MulMod` output is the remainder witness `r`, allocated at
`offset + m` (right after the quotient `q`), reading only the `m` cells
`[offset+m, offset+2m)`. Environments agreeing below `offset + m + m` (in particular
below `offset + (circuit P).localLength input`) evaluate the output identically. -/
lemma eval_output_of_agreesBelow (P : BigIntParams p m) [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) {offset k : ℕ}
    {env env' : ProverEnvironment (F p)}
    (h_agree : env.AgreesBelow k env') (hk : offset + m + m ≤ k) :
    eval env ((main P input).output offset) = eval env' ((main P input).output offset) := by
  rw [(elaborated P).output_eq input offset]
  show eval env (varFromOffset (BigInt m) (offset + m))
    = eval env' (varFromOffset (BigInt m) (offset + m))
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env) _ i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env') _ i hi]
  simp only [ProvableType.varFromOffset_fields, Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + m + i) (by omega)

end MulMod

end

end Solution.Secp256k1ScalarMul
