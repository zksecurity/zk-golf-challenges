import Solution.RSASSAPKCS1v15_SHA256_4096_65537.LessThan
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.EqViaCarries
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModTheorems

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

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

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
  Specs.RSA.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)


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

/-! ## Computable witnesses -/

omit [NeZero m] in
/-- `evalValue` reads a limb vector only through the evaluation of its individual
limbs; hence it is invariant under environments that agree on those limbs. -/
private lemma evalValue_congr (B : ℕ) {env env' : ProverEnvironment (F p)}
    (x : Var (BigInt m) (F p))
    (h : ∀ j, (hj : j < m) →
      Expression.eval env.toEnvironment x[j] = Expression.eval env'.toEnvironment x[j]) :
    evalValue B env x = evalValue B env' x := by
  simp only [evalValue]
  have hmap : Vector.map (Expression.eval env.toEnvironment) x
      = Vector.map (Expression.eval env'.toEnvironment) x := by
    apply Vector.ext; intro j hj; simp only [Vector.getElem_map]; exact h j hj
  rw [hmap]

/-- `(witnessedMul a b).localLength off = m * m` in `Circuit.localLength` form. -/
lemma witnessedMul_circuit_localLength (a b : Var (BigInt m) (F p)) (off : ℕ) :
    (witnessedMul a b).localLength off = m * m :=
  witnessedMul_localLength off a b

/-- Structural computable-witness fact for the raw `witnessedMul a b` circuit: its
only witness is the product matrix `pp`, whose generator reads `a`,`b` through the
evaluation of their limbs. So the witness obligation follows from an agreement
hypothesis on `a`,`b`; the trailing `forEach assertZero` carries no obligation. -/
lemma witnessedMul_structuralComputableWitnesses
    (parentInput : Var (Inputs m) (F p)) (a b : Var (BigInt m) (F p)) (n0 : ℕ)
    (env env' : ProverEnvironment (F p))
    (hab : env.AgreesBelow n0 env' → eval env parentInput = eval env' parentInput →
      (∀ i, (hi : i < m) → Expression.eval env.toEnvironment a[i] = Expression.eval env'.toEnvironment a[i]) ∧
      (∀ i, (hi : i < m) → Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])) :
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
      parentInput env env' n0 ((witnessedMul a b).operations n0) := by
  unfold witnessedMul
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    implies_true, and_true]
  simp only [circuit_norm]
  intro h_agree h_input
  obtain ⟨ha, hb⟩ := hab h_agree (by simp only [circuit_norm]; exact h_input)
  apply Vector.ext
  intro t ht
  simp only [Vector.getElem_ofFn]
  rw [ha _ (Nat.div_lt_of_lt_mul ht), hb _ (Nat.mod_lt _ (Nat.pos_of_neZero m))]

omit [NeZero m] in
/-- Agreement of the `bigIntMulVars` output over a fresh witness block `pp` at
offset `ppOff`: under `env.AgreesBelow k env'` covering the block, both envs
evaluate the affine coefficient vector identically. -/
lemma map_eval_bigIntMulVars_varFromOffset_agree {ppOff k : ℕ} {e1 e2 : ProverEnvironment (F p)}
    (h_agree : e1.AgreesBelow k e2) (hk : ppOff + m * m ≤ k) :
    Vector.map (Expression.eval e1.toEnvironment)
        (bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F p) { index := ppOff + i }))
      = Vector.map (Expression.eval e2.toEnvironment)
        (bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F p) { index := ppOff + i })) := by
  set pp := (Vector.mapRange (m * m) fun i => var (F := F p) { index := ppOff + i }) with hpp
  have hpp_agree : ∀ j, (hj : j < m * m) →
      Expression.eval e1.toEnvironment (pp[j]'hj) = Expression.eval e2.toEnvironment (pp[j]'hj) := by
    intro j hj
    rw [hpp, Vector.getElem_mapRange]
    simp only [Expression.eval]
    exact h_agree (ppOff + j) (by omega)
  apply Vector.ext
  intro c hc
  rw [Vector.getElem_map, Vector.getElem_map,
      eval_bigIntMulVars_coeff e1.toEnvironment pp ⟨c, hc⟩,
      eval_bigIntMulVars_coeff e2.toEnvironment pp ⟨c, hc⟩]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ c ∧ c - i.val < m
  · simp only [dif_pos h]; exact hpp_agree _ _
  · simp only [dif_neg h]

omit [NeZero m] in
/-- Agreement of a `varFromOffset (BigInt m)` witness block. -/
lemma map_eval_varFromOffset_agree {off k : ℕ} {e1 e2 : ProverEnvironment (F p)}
    (h_agree : e1.AgreesBelow k e2) (hk : off + m ≤ k) :
    Vector.map (Expression.eval e1.toEnvironment)
        (Vector.mapRange m fun i => var (F := F p) { index := off + i })
      = Vector.map (Expression.eval e2.toEnvironment)
        (Vector.mapRange m fun i => var (F := F p) { index := off + i }) := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapRange]
  simp only [Expression.eval]
  exact h_agree (off + j) (by omega)

omit [NeZero m] in
/-- Agreement of the `S = Sqn + r` coefficient vector used by `MulMod`, from the
agreement of `Sqn` and the agreement of the `r` witness cells at offset `rOff`. -/
lemma map_eval_sMix_agree {e1 e2 : ProverEnvironment (F p)} (rOff : ℕ)
    (Sqn : Vector (Expression (F p)) (2 * m - 1))
    (hSqn : Vector.map (Expression.eval e1.toEnvironment) Sqn
      = Vector.map (Expression.eval e2.toEnvironment) Sqn)
    (hr : ∀ j, j < m → e1.toEnvironment.get (rOff + j) = e2.toEnvironment.get (rOff + j)) :
    Vector.map (Expression.eval e1.toEnvironment)
        (Vector.mapFinRange (2 * m - 1) fun c =>
          if _h : c.val < m then Sqn[c.val] + var (F := F p) { index := rOff + c.val } else Sqn[c.val])
      = Vector.map (Expression.eval e2.toEnvironment)
        (Vector.mapFinRange (2 * m - 1) fun c =>
          if _h : c.val < m then Sqn[c.val] + var (F := F p) { index := rOff + c.val } else Sqn[c.val]) := by
  apply Vector.ext
  intro c hc
  simp only [Vector.getElem_map, Vector.getElem_mapFinRange]
  have hs : Expression.eval e1.toEnvironment Sqn[c] = Expression.eval e2.toEnvironment Sqn[c] := by
    have := congrArg (fun v => v[c]'(by omega)) hSqn
    simpa [Vector.getElem_map] using this
  by_cases hcm : c < m
  · simp only [dif_pos hcm]
    rw [show Expression.eval e1.toEnvironment (Sqn[c] + var (F := F p) { index := rOff + c })
          = Expression.eval e1.toEnvironment Sqn[c] + e1.toEnvironment.get (rOff + c) from rfl,
      show Expression.eval e2.toEnvironment (Sqn[c] + var (F := F p) { index := rOff + c })
          = Expression.eval e2.toEnvironment Sqn[c] + e2.toEnvironment.get (rOff + c) from rfl,
      hs, hr c hcm]
  · simp only [dif_neg hcm]; exact hs

open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  refine ⟨?wq, ?wr, ?nq, ?nr, ?wab, ?wqn, ?eq, ?lt⟩
  case wq =>
    simp only [circuit_norm]
    intro _ h_input
    have ha : ∀ j, (hj : j < m) →
        Expression.eval env.toEnvironment input.a[j] = Expression.eval env'.toEnvironment input.a[j] := by
      intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.a) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
    have hb : ∀ j, (hj : j < m) →
        Expression.eval env.toEnvironment input.b[j] = Expression.eval env'.toEnvironment input.b[j] := by
      intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.b) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
    have hn : ∀ j, (hj : j < m) →
        Expression.eval env.toEnvironment input.modulus[j] = Expression.eval env'.toEnvironment input.modulus[j] := by
      intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.modulus) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
    simp only [evalValue_congr P.B input.a ha, evalValue_congr P.B input.b hb,
      evalValue_congr P.B input.modulus hn]
  case wr =>
    simp only [circuit_norm]
    intro _ h_input
    have ha : ∀ j, (hj : j < m) →
        Expression.eval env.toEnvironment input.a[j] = Expression.eval env'.toEnvironment input.a[j] := by
      intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.a) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
    have hb : ∀ j, (hj : j < m) →
        Expression.eval env.toEnvironment input.b[j] = Expression.eval env'.toEnvironment input.b[j] := by
      intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.b) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
    have hn : ∀ j, (hj : j < m) →
        Expression.eval env.toEnvironment input.modulus[j] = Expression.eval env'.toEnvironment input.modulus[j] := by
      intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.modulus) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
    simp only [evalValue_congr P.B input.a ha, evalValue_congr P.B input.b hb,
      evalValue_congr P.B input.modulus hn]
  case nq =>
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input _ _ ?_ (Normalize.computableWitnesses P) env env'
    intro k e1 e2 hle h_agree _
    have hk : offset + m ≤ k := by
      simp only [circuit_norm] at hle; omega
    simp only [circuit_norm]
    exact map_eval_varFromOffset_agree h_agree hk
  case nr =>
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input _ _ ?_ (Normalize.computableWitnesses P) env env'
    intro k e1 e2 hle h_agree _
    have hk : offset + m + m ≤ k := by
      simp only [circuit_norm] at hle; omega
    simp only [circuit_norm]
    exact map_eval_varFromOffset_agree h_agree hk
  case wab =>
    refine witnessedMul_structuralComputableWitnesses input _ _ _ env env' ?_
    intro _ h_input
    constructor
    · intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.a) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
    · intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.b) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
  case wqn =>
    refine witnessedMul_structuralComputableWitnesses input _ _ _ env env' ?_
    intro h_agree h_input
    simp only [circuit_norm, witnessedMul_circuit_localLength] at h_agree
    constructor
    · intro j hj
      simp only [circuit_norm]
      exact h_agree (offset + j) (by omega)
    · intro j hj
      have hm := congrArg (fun s : Inputs m (F p) => s.modulus) h_input
      simp only [circuit_norm] at hm
      have := congrArg (fun v : Vector (F p) m => v[j]'hj) hm
      simpa [Vector.getElem_map] using this
  case eq =>
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (EqViaCarries.circuit P) input _ _ ?_ (EqViaCarries.computableWitnesses P) env env'
    intro k e1 e2 hle h_agree h_input
    simp only [circuit_norm, witnessedMul_circuit_localLength, Normalize.circuit,
      Normalize.elaborated, Normalize.main, Gadgets.ToBits.rangeCheck] at hle
    have hkAB : offset + m + m + m * P.B + m * P.B + m * m ≤ k := by omega
    have hkQN : offset + m + m + m * P.B + m * P.B + m * m + m * m ≤ k := by omega
    have hkR : offset + m + m ≤ k := by omega
    have hPc := map_eval_bigIntMulVars_varFromOffset_agree
      (ppOff := offset + m + m + m * P.B + m * P.B) h_agree hkAB
    have hSqn := map_eval_bigIntMulVars_varFromOffset_agree
      (ppOff := offset + m + m + m * P.B + m * P.B + m * m) h_agree hkQN
    have hr : ∀ j, j < m → e1.toEnvironment.get (offset + m + j) = e2.toEnvironment.get (offset + m + j) := by
      intro j hj; exact h_agree (offset + m + j) (by omega)
    have hS := map_eval_sMix_agree (offset + m) _ hSqn hr
    simp only [circuit_norm, witnessedMul_output, witnessedMul_circuit_localLength,
      Normalize.circuit, Normalize.elaborated, Normalize.main, Gadgets.ToBits.rangeCheck]
    rw [hPc, hS]
  case lt =>
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (LessThan.circuit P) input _ _ ?_ (LessThan.computableWitnesses P) env env'
    intro k e1 e2 hle h_agree h_input
    have hk : offset + m + m ≤ k := by
      simp only [circuit_norm, witnessedMul_circuit_localLength] at hle; omega
    have hr := map_eval_varFromOffset_agree (off := offset + m) h_agree (by omega)
    have hn : Vector.map (Expression.eval e1.toEnvironment) input.modulus
        = Vector.map (Expression.eval e2.toEnvironment) input.modulus := by
      have := congrArg (fun s : Inputs m (F p) => s.modulus) h_input
      simpa [circuit_norm] using this
    simp only [circuit_norm]
    rw [hr, hn]

/-- The `MulMod` output is `r`, the remainder witness block at `offset + m`. Each
of its cells is invariant under environments agreeing below the whole circuit
length. Mirrors `CompressBlock.eval_mem_output_of_agreesBelow`; used by `ModExp`. -/
lemma eval_mem_output_of_agreesBelow {offset : ℕ} {env env' : ProverEnvironment (F p)}
    (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p))
    (h_agree : env.AgreesBelow
      (offset + (m + m + m * P.B + m * P.B + m * m + m * m
        + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m))) env') :
    ∀ (j : ℕ) (hj : j < m),
      Expression.eval env.toEnvironment (((main P input).output offset)[j]'hj)
        = Expression.eval env'.toEnvironment (((main P input).output offset)[j]'hj) := by
  intro j hj
  have hout : (main P input).output offset = varFromOffset (BigInt m) (offset + m) :=
    (elaborated P).output_eq input offset
  rw [hout]
  exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
    h_agree (by omega) _ (Vector.getElem_mem hj)

/-- Vector-level agreement of the `MulMod` output. Mirrors
`CompressBlock.eval_output_of_agreesBelow`; used by `ModExp`. -/
lemma eval_output_of_agreesBelow {offset : ℕ} {env env' : ProverEnvironment (F p)}
    (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p))
    (h_agree : env.AgreesBelow
      (offset + (m + m + m * P.B + m * P.B + m * m + m * m
        + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m))) env') :
    eval env.toEnvironment ((main P input).output offset)
      = eval env'.toEnvironment ((main P input).output offset) := by
  have hout : (main P input).output offset = varFromOffset (BigInt m) (offset + m) :=
    (elaborated P).output_eq input offset
  rw [hout]
  simp only [circuit_norm]
  exact map_eval_varFromOffset_agree h_agree (by omega)

end MulMod

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
