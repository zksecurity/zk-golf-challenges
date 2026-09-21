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

/-- Witness the `m·m` partial products `a[i]·b[j]` of two big integers as fresh
cells and assert each equals the corresponding product, returning the *affine*
coefficient vector `bigIntMulVars` of the schoolbook convolution.

Each product assert `a[i]·b[j] − pp[i·m+j] = 0` is a single rank-1 (R1CS-clean)
row, and the returned coefficient vector is a linear form over the witnessed
products, so `EqViaCarries` sees only affine inputs. -/
def witnessedMul (a b : Var (BigInt m) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) (2 * m - 1)) := do
  -- witness the product matrix pp[i*m+j] = a[i].val * b[j].val. The generator is a
  -- literal witness-IR vector of field products of the input expressions (`Vector.ofFn`
  -- over `Fin (m*m)` stays one term even with symbolic `m`).
  let pp ← Circuit.witnessVector (m * m) (.lit (Vector.ofFn fun t : Fin (m * m) =>
    Witgen.FExpr.mul (.expr (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt)))
      (.expr (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m))))))
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
  intro t; have := h t; rw [sub_eq_zero] at this; exact this

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
  exact h

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

/-! ## Witness programs for the quotient and the remainder

`q = a·b/n` and `r = a·b%n` are big-integer division, so both come out of the digit
library: the operands are read into digit registers for free (their limbs are disjoint
bit windows), multiplied, and divided by binary long division.

The two are separate `witness` operations, so neither can refer to the other's
`let`-steps and a shared program would have to be spliced into one site, which would
change the circuit. Each site therefore runs the whole `mulP`/`divmodP` chain and keeps
one register; the division loop dominates either way.

`qrN` is the pair of registers as a total function of the operands' values, which is
what keeps the `computableWitnesses` bridges free of side conditions; `lval_qrN` reads
them back as `a·b/n` and `a·b%n` under the gadget's `Assumptions`.
-/

section Generator
open Witgen WitgenNat WitgenBigNat IRLimbs

/-- Digits of an operand register: a normalized `m`-limb value is below `2^(B·m)`. -/
def opLen (m B : ℕ) : ℕ := numChunks (B * m)

/-- Width of the dividend `a·b`. -/
def prodBits (m B : ℕ) : ℕ := 2 * (B * m)

/-- Digits of the quotient register. -/
def quotLen (m B : ℕ) : ℕ := numChunks (prodBits m B)

/-- Digits of the remainder register: one more than the modulus needs. -/
def remLen (m B : ℕ) : ℕ := opLen m B + 1

/-- Quotient and remainder of `a·b` by `n`, as digit registers. Both witness sites of
`main` run this: the two are separate `witness` operations, so neither can refer to the
other's `let`-steps, and a shared program would have to be spliced into one site — which
would change the circuit. The division loop is the dominant cost either way. -/
def qrProg (B : ℕ) (a b n : Var (BigInt m) (F p)) :
    M (F p) (List (U64Expr (F p)) × List (U64Expr (F p))) := do
  let pr ← mulP (digitsOf B a (opLen m B)) (digitsOf B b (opLen m B))
  divmodP (digitsOf B n (opLen m B)) pr (quotLen m B) (remLen m B) (prodBits m B)

omit [NeZero m] in
theorem computesPair_qrProg {B : ℕ} (hB : 0 < B) (a b n : Var (BigInt m) (F p)) :
    ComputesPair #[] (qrProg B a b n)
      (fun env => divmod (ofNat (bigVal B n env) (opLen m B))
        (mul (ofNat (bigVal B a env) (opLen m B)) (ofNat (bigVal B b env) (opLen m B)))
        (quotLen m B) (remLen m B) (prodBits m B)) := by
  refine Computes.bind (computesBig_mulP _ _ (evalsBig_digitsOf hB a (opLen m B))
    (evalsBig_digitsOf hB b (opLen m B))) ?_
  intro S1 pr hS1 hpr
  exact computesPair_divmodP _ _ _ _ _ ((evalsBig_digitsOf hB n (opLen m B)).mono hS1) hpr

/-- The quotient witness program. -/
def qWitness (B : ℕ) (a b n : Var (BigInt m) (F p)) : M (F p) (VExpr (F p) m) := do
  let qr ← qrProg B a b n
  Pure.pure (limbsOut qr.1 B m)

/-- The remainder witness program. -/
def rWitness (B : ℕ) (a b n : Var (BigInt m) (F p)) : M (F p) (VExpr (F p) m) := do
  let qr ← qrProg B a b n
  Pure.pure (limbsOut qr.2 B m)

/-- The register a witness site reads, as a total function of the operands' values. -/
def qrN (B : ℕ) (m : ℕ) (va vb vn : ℕ) : List ℕ × List ℕ :=
  divmod (ofNat vn (opLen m B)) (mul (ofNat va (opLen m B)) (ofNat vb (opLen m B)))
    (quotLen m B) (remLen m B) (prodBits m B)

omit [NeZero m] in
theorem computesV_qWitness {B : ℕ} (hB : 0 < B) (a b n : Var (BigInt m) (F p)) :
    ComputesV #[] (qWitness B a b n)
      (fun env => Vector.ofFn fun j : Fin m =>
        ((lval (qrN B m (bigVal B a env) (bigVal B b env) (bigVal B n env)).1
          / 2 ^ (B * j.val) % 2 ^ B : ℕ) : F p)) := by
  refine Computes.bind (computesPair_qrProg hB a b n) ?_
  intro S1 qr hS1 hqr
  have h1 : EvalsBig S1 qr.1
      (fun env => (divmod (ofNat (bigVal B n env) (opLen m B))
        (mul (ofNat (bigVal B a env) (opLen m B)) (ofNat (bigVal B b env) (opLen m B)))
        (quotLen m B) (remLen m B) (prodBits m B)).1) := hqr.1
  exact Computes.pure (evalsV_limbsOut h1 B m)

omit [NeZero m] in
theorem computesV_rWitness {B : ℕ} (hB : 0 < B) (a b n : Var (BigInt m) (F p)) :
    ComputesV #[] (rWitness B a b n)
      (fun env => Vector.ofFn fun j : Fin m =>
        ((lval (qrN B m (bigVal B a env) (bigVal B b env) (bigVal B n env)).2
          / 2 ^ (B * j.val) % 2 ^ B : ℕ) : F p)) := by
  refine Computes.bind (computesPair_qrProg hB a b n) ?_
  intro S1 qr hS1 hqr
  have h2 : EvalsBig S1 qr.2
      (fun env => (divmod (ofNat (bigVal B n env) (opLen m B))
        (mul (ofNat (bigVal B a env) (opLen m B)) (ofNat (bigVal B b env) (opLen m B)))
        (quotLen m B) (remLen m B) (prodBits m B)).2) := hqr.2
  exact Computes.pure (evalsV_limbsOut h2 B m)

/-! ### Reading the registers back -/

omit [NeZero m] in
/-- Under the gadget's `Assumptions` the two registers really hold `a·b/n` and `a·b%n`. -/
theorem lval_qrN {B : ℕ} {va vb vn : ℕ} (hvn : 0 < vn)
    (ha : va < 2 ^ (B * m)) (hb : vb < 2 ^ (B * m)) (hn : vn < 2 ^ (B * m)) :
    lval (qrN B m va vb vn).1 = va * vb / vn ∧ lval (qrN B m va vb vn).2 = va * vb % vn := by
  have hop : (2 : ℕ) ^ (B * m) ≤ base ^ opLen m B := by
    rw [opLen]; exact two_pow_le_base_numChunks _
  have hva : lval (ofNat va (opLen m B)) = va := lval_ofNat_of_lt (by omega)
  have hvb : lval (ofNat vb (opLen m B)) = vb := lval_ofNat_of_lt (by omega)
  have hvn' : lval (ofNat vn (opLen m B)) = vn := lval_ofNat_of_lt (by omega)
  have hprod : lval (mul (ofNat va (opLen m B)) (ofNat vb (opLen m B))) = va * vb := by
    rw [lval_mul, hva, hvb]
  have hbits : va * vb < 2 ^ prodBits m B := by
    have h1 : va * vb < 2 ^ (B * m) * 2 ^ (B * m) :=
      Nat.mul_lt_mul_of_lt_of_le ha (le_of_lt hb) (Nat.two_pow_pos _)
    have h2 : (2 : ℕ) ^ (B * m) * 2 ^ (B * m) = 2 ^ prodBits m B := by
      rw [← pow_add, prodBits]; congr 1; omega
    omega
  obtain ⟨-, -, -, -, h5, h6⟩ :=
    divmod_spec (ofNat vn (opLen m B))
      (mul (ofNat va (opLen m B)) (ofNat vb (opLen m B))) (prodBits m B) (quotLen m B)
      (remLen m B) (bounded_ofNat _ _) (bounded_mul _ _ (bounded_ofNat _ _) (bounded_ofNat _ _))
      (by rw [hvn']; exact hvn) (by rw [length_ofNat, remLen]; omega)
      (by rw [hprod]; exact hbits)
      (by rw [quotLen]; exact two_pow_le_base_numChunks _)
  rw [qrN]
  rw [h5, h6, hprod, hvn']
  exact ⟨rfl, rfl⟩

/-! ### The witness-site bridges -/

omit [NeZero m] in
/-- Bridge for the quotient witness: under the gadget's `Assumptions` the witnessed cell
is limb `k` of `a·b / n`. -/
theorem getElem_eval_qWitness (P : BigIntParams p m) (a b n : Var (BigInt m) (F p))
    (env : ProverEnvironment (F p)) (k : ℕ) (hk : k < m)
    (hna : BigInt.Normalized P.B (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized P.B (b.map (Expression.eval env.toEnvironment)))
    (hnn : BigInt.Normalized P.B (n.map (Expression.eval env.toEnvironment)))
    (hnpos : 0 < BigInt.value P.B (n.map (Expression.eval env.toEnvironment))) :
    (Witgen.VExpr.eval
        { env := env, locals := Witgen.evalSteps env (qWitness P.B a b n #[]).2.toList }
        (qWitness P.B a b n #[]).1)[k]
      = ((BigInt.value P.B (a.map (Expression.eval env.toEnvironment))
            * BigInt.value P.B (b.map (Expression.eval env.toEnvironment))
            / BigInt.value P.B (n.map (Expression.eval env.toEnvironment))
            / 2 ^ (P.B * k) % 2 ^ P.B : ℕ) : F p) := by
  rw [IRLimbs.eval_program (computesV_qWitness (by have := P.hB1; omega) a b n) env]
  simp only [Vector.getElem_ofFn]
  rw [bigVal_eq_value P.B a env hna, bigVal_eq_value P.B b env hnb,
    bigVal_eq_value P.B n env hnn,
    (lval_qrN hnpos (BigInt.value_lt hna) (BigInt.value_lt hnb) (BigInt.value_lt hnn)).1]

omit [NeZero m] in
/-- Bridge for the remainder witness. -/
theorem getElem_eval_rWitness (P : BigIntParams p m) (a b n : Var (BigInt m) (F p))
    (env : ProverEnvironment (F p)) (k : ℕ) (hk : k < m)
    (hna : BigInt.Normalized P.B (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized P.B (b.map (Expression.eval env.toEnvironment)))
    (hnn : BigInt.Normalized P.B (n.map (Expression.eval env.toEnvironment)))
    (hnpos : 0 < BigInt.value P.B (n.map (Expression.eval env.toEnvironment))) :
    (Witgen.VExpr.eval
        { env := env, locals := Witgen.evalSteps env (rWitness P.B a b n #[]).2.toList }
        (rWitness P.B a b n #[]).1)[k]
      = ((BigInt.value P.B (a.map (Expression.eval env.toEnvironment))
            * BigInt.value P.B (b.map (Expression.eval env.toEnvironment))
            % BigInt.value P.B (n.map (Expression.eval env.toEnvironment))
            / 2 ^ (P.B * k) % 2 ^ P.B : ℕ) : F p) := by
  rw [IRLimbs.eval_program (computesV_rWitness (by have := P.hB1; omega) a b n) env]
  simp only [Vector.getElem_ofFn]
  rw [bigVal_eq_value P.B a env hna, bigVal_eq_value P.B b env hnb,
    bigVal_eq_value P.B n env hnn,
    (lval_qrN hnpos (BigInt.value_lt hna) (BigInt.value_lt hnb) (BigInt.value_lt hnn)).2]

omit [NeZero m] in
/-- Both witness programs read the operands only through their evaluated limbs. -/
theorem eval_toIR_qWitness_congr {B : ℕ} (hB : 0 < B) (a b n : Var (BigInt m) (F p))
    {env env' : ProverEnvironment (F p)}
    (ha : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (a[j]'hj)
      = Expression.eval env'.toEnvironment (a[j]'hj))
    (hb : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (b[j]'hj)
      = Expression.eval env'.toEnvironment (b[j]'hj))
    (hn : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (n[j]'hj)
      = Expression.eval env'.toEnvironment (n[j]'hj)) :
    (qWitness B a b n).toIR.eval env = (qWitness B a b n).toIR.eval env' := by
  rw [IRLimbs.toIR_eq, Witgen.WitgenIR.eval]
  show Witgen.VExpr.eval { env := env, locals := _ } _
    = Witgen.VExpr.eval { env := env', locals := _ } _
  rw [IRLimbs.eval_program (computesV_qWitness hB a b n) env,
    IRLimbs.eval_program (computesV_qWitness hB a b n) env',
    bigVal_congr B a ha, bigVal_congr B b hb, bigVal_congr B n hn]

omit [NeZero m] in
theorem eval_toIR_rWitness_congr {B : ℕ} (hB : 0 < B) (a b n : Var (BigInt m) (F p))
    {env env' : ProverEnvironment (F p)}
    (ha : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (a[j]'hj)
      = Expression.eval env'.toEnvironment (a[j]'hj))
    (hb : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (b[j]'hj)
      = Expression.eval env'.toEnvironment (b[j]'hj))
    (hn : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (n[j]'hj)
      = Expression.eval env'.toEnvironment (n[j]'hj)) :
    (rWitness B a b n).toIR.eval env = (rWitness B a b n).toIR.eval env' := by
  rw [IRLimbs.toIR_eq, Witgen.WitgenIR.eval]
  show Witgen.VExpr.eval { env := env, locals := _ } _
    = Witgen.VExpr.eval { env := env', locals := _ } _
  rw [IRLimbs.eval_program (computesV_rWitness hB a b n) env,
    IRLimbs.eval_program (computesV_rWitness hB a b n) env',
    bigVal_congr B a ha, bigVal_congr B b hb, bigVal_congr B n hn]


end Generator

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

  -- 1. witness q = (a·b)/n and r = (a·b)%n as BigInt m, out of the digit library: the
  -- operands are read into digit registers for free, multiplied schoolbook, and divided
  -- by binary long division.
  let q ← witnessVectorProgram m (qWitness P.B a b n)
  let r ← witnessVectorProgram m (rWitness P.B a b n)

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
      -- the input struct is destructured and its components are rewritten to their
      -- values; the core lemma wants the modulus in evaluated-variable form
      rw [← h_input.2.2] at h_lt_impl
      -- fully explicit offsets/outputs: never let Lean `whnf` the `m*m` loop offset
      have h_pAB := witnessedMul_soundness (i₀ + m + m + m * B + m * B) input_var_a input_var_b env hAB_ops
      have h_pQN := witnessedMul_soundness
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var_modulus env hQN_ops
      refine ⟨?_, witnessedMul_requirements _ _ _ _, witnessedMul_requirements _ _ _ _⟩
      have h_input' : (Vector.map (Expression.eval env) input_var_a,
          Vector.map (Expression.eval env) input_var_b,
          Vector.map (Expression.eval env) input_var_modulus)
            = ((input_a, input_b, input_modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [h_input.1, h_input.2.1, h_input.2.2]
      have heqAB_get := witnessedMul_eval_bridge env (i₀ + m + m + m * B + m * B)
        input_var_a input_var_b h_pAB
      have heqQN_get := witnessedMul_eval_bridge env
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var_modulus h_pQN
      exact mulMod_soundness_core_wm (B := B) hp i₀ env
        input_var_a input_var_b input_var_modulus
        (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).1
        (witnessedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var_modulus
          (i₀ + m + m + m * B + m * B + Operations.localLength
            (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).2)).1
        (input_a, input_b, input_modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_norm
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
        (i₀ + m + m + m * B + m * B) input_var_a input_var_b env rfl hAB_uses
      have h_pvQN := witnessedMul_usesLocalWitnesses
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).2)
        (Operations.localLength (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).2
          + (i₀ + m + m + m * B + m * B))
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var_modulus env
        (Nat.add_comm _ _) hQN_uses
      have h_pAB : ∀ t : Fin (m * m),
          Expression.eval env.toEnvironment (input_var_a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
              * Expression.eval env.toEnvironment (input_var_b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
            = env.toEnvironment.get ((i₀ + m + m + m * B + m * B) + t.val) :=
        fun t => (h_pvAB t).symm
      have h_pQN : ∀ t : Fin (m * m),
          Expression.eval env.toEnvironment
              ((Vector.mapRange m fun i => var { index := i₀ + i })[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
              * Expression.eval env.toEnvironment (input_var_modulus[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
            = env.toEnvironment.get ((i₀ + m + m + m * B + m * B + Operations.localLength
                (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).2) + t.val) :=
        fun t => (h_pvQN t).symm
      -- the operand denotations, in the shape the two register bridges produce
      have heva : BigInt.value B (Vector.map (Expression.eval env.toEnvironment) input_var_a)
          = BigInt.value B input_a := by rw [← h_input.1]
      have hevb : BigInt.value B (Vector.map (Expression.eval env.toEnvironment) input_var_b)
          = BigInt.value B input_b := by rw [← h_input.2.1]
      have hevn : BigInt.value B (Vector.map (Expression.eval env.toEnvironment) input_var_modulus)
          = BigInt.value B input_modulus := by rw [← h_input.2.2]
      -- the side conditions of the two witness bridges, in variable form
      have hna : BigInt.Normalized B (input_var_a.map (Expression.eval env.toEnvironment)) := by
        rw [h_input.1]; exact ha_norm
      have hnb : BigInt.Normalized B (input_var_b.map (Expression.eval env.toEnvironment)) := by
        rw [h_input.2.1]; exact hb_norm
      have hnn : BigInt.Normalized B
          (input_var_modulus.map (Expression.eval env.toEnvironment)) := by
        rw [h_input.2.2]; exact hn_norm
      have hnpos : 0 < BigInt.value B
          (input_var_modulus.map (Expression.eval env.toEnvironment)) := by
        rw [h_input.2.2]; exact hn_pos
      -- both witnessed cells come out of the shared quotient/remainder registers, so the
      -- two bridges read them back directly
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input_a * BigInt.value B input_b / BigInt.value B input_modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i
        have hq := hq_env i
        rw [getElem_eval_qWitness ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ _ _ _ env i.val i.isLt
            hna hnb hnn hnpos] at hq
        rw [hq, heva, hevb, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input_a * BigInt.value B input_b % BigInt.value B input_modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i
        have hr := hr_env i
        rw [getElem_eval_rWitness ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ _ _ _ env i.val i.isLt
            hna hnb hnn hnpos] at hr
        rw [hr, heva, hevb, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var_a,
          Vector.map (Expression.eval env.toEnvironment) input_var_b,
          Vector.map (Expression.eval env.toEnvironment) input_var_modulus)
            = ((input_a, input_b, input_modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [h_input.1, h_input.2.1, h_input.2.2]
      have heqAB_get := witnessedMul_eval_bridge env.toEnvironment (i₀ + m + m + m * B + m * B)
        input_var_a input_var_b h_pAB
      have heqQN_get := witnessedMul_eval_bridge env.toEnvironment
        (i₀ + m + m + m * B + m * B + Operations.localLength
          (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var_modulus h_pQN
      have core := mulMod_completeness_core_wm (B := B) hB hp i₀ env.toEnvironment
        input_var_a input_var_b input_var_modulus
        (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).1
        (witnessedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var_modulus
          (i₀ + m + m + m * B + m * B + Operations.localLength
            (witnessedMul input_var_a input_var_b (i₀ + m + m + m * B + m * B)).2)).1
        (input_a, input_b, input_modulus) h_input' ha_norm hb_norm hn_norm hab_lt hbb_lt hn_pos
        hqwit hrwit heqAB_get heqQN_get
      -- the goal mentions the destructured input's value; the core lemma states the
      -- modulus in evaluated-variable form
      rw [← h_input.2.2]
      -- single explicit `exact` (lazy `.1/.2` projections; no eager `obtain` ⇒ no `whnf` blowup)
      exact ⟨core.1, core.2.1,
        witnessedMul_completeness (i₀ + m + m + m * B + m * B) input_var_a input_var_b env h_pvAB,
        witnessedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var_modulus env h_pvQN,
        core.2.2⟩

/-! ## Computable witnesses -/

/-- `(witnessedMul a b).localLength off = m * m` in `Circuit.localLength` form. -/
lemma witnessedMul_circuit_localLength (a b : Var (BigInt m) (F p)) (off : ℕ) :
    (witnessedMul a b).localLength off = m * m :=
  witnessedMul_localLength off a b

omit [NeZero m] in
/-- Per-field projection of an `eval`-agreement hypothesis on the `Inputs` struct.
The `Var Inputs` `match` no longer iota-reduces on a struct *variable*, so the
destructuring has to happen here, once. -/
lemma eval_inputs_parts {input : Var (Inputs m) (F p)} {env env' : ProverEnvironment (F p)}
    (h : eval env input = eval env' input) :
    Vector.map (Expression.eval env.toEnvironment) input.a
        = Vector.map (Expression.eval env'.toEnvironment) input.a ∧
      Vector.map (Expression.eval env.toEnvironment) input.b
        = Vector.map (Expression.eval env'.toEnvironment) input.b ∧
      Vector.map (Expression.eval env.toEnvironment) input.modulus
        = Vector.map (Expression.eval env'.toEnvironment) input.modulus := by
  obtain ⟨a, b, modulus⟩ := input
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h
  exact h

omit [NeZero m] in
/-- Element-wise form of `eval_inputs_parts`. -/
lemma eval_inputs_getElem {input : Var (Inputs m) (F p)} {env env' : ProverEnvironment (F p)}
    (h : eval env input = eval env' input) :
    (∀ j, (hj : j < m) → Expression.eval env.toEnvironment (input.a[j]'hj)
        = Expression.eval env'.toEnvironment (input.a[j]'hj)) ∧
      (∀ j, (hj : j < m) → Expression.eval env.toEnvironment (input.b[j]'hj)
        = Expression.eval env'.toEnvironment (input.b[j]'hj)) ∧
      (∀ j, (hj : j < m) → Expression.eval env.toEnvironment (input.modulus[j]'hj)
        = Expression.eval env'.toEnvironment (input.modulus[j]'hj)) := by
  obtain ⟨hA, hB, hN⟩ := eval_inputs_parts h
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have hx := congrArg (fun v : Vector (F p) m => v[j]'hj) hA
    simp only [Vector.getElem_map] at hx; exact hx
  · have hx := congrArg (fun v : Vector (F p) m => v[j]'hj) hB
    simp only [Vector.getElem_map] at hx; exact hx
  · have hx := congrArg (fun v : Vector (F p) m => v[j]'hj) hN
    simp only [Vector.getElem_map] at hx; exact hx

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
  simp only [circuit_norm, explicit_provable_type]
  intro h_agree h_input
  obtain ⟨ha, hb⟩ := hab h_agree (by simp only [circuit_norm]; exact h_input)
  refine Vector.ext fun t ht => ?_
  simp only [Vector.getElem_ofFn, circuit_norm]
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
    IRLimbs.witnessVectorProgram_eq_witnessIR,
    Circuit.witnessIR_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  refine ⟨?wq, ?wr, ?nq, ?nr, ?wab, ?wqn, ?eq, ?lt⟩
  case wq =>
    intro _ h_input
    have h_in : eval env input = eval env' input := by
      simpa only [circuit_norm] using h_input
    obtain ⟨ha, hb, hn⟩ := eval_inputs_getElem h_in
    exact eval_toIR_qWitness_congr (by have := P.hB1; omega) _ _ _ ha hb hn
  case wr =>
    intro _ h_input
    have h_in : eval env input = eval env' input := by
      simpa only [circuit_norm] using h_input
    obtain ⟨ha, hb, hn⟩ := eval_inputs_getElem h_in
    exact eval_toIR_rWitness_congr (by have := P.hB1; omega) _ _ _ ha hb hn
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
    obtain ⟨ha, hb, _⟩ := eval_inputs_getElem h_input
    exact ⟨ha, hb⟩
  case wqn =>
    refine witnessedMul_structuralComputableWitnesses input _ _ _ env env' ?_
    intro h_agree h_input
    simp only [circuit_norm, witnessedMul_circuit_localLength] at h_agree
    constructor
    · intro j hj
      simp only [circuit_norm]
      exact h_agree (offset + j) (by omega)
    · exact (eval_inputs_getElem h_input).2.2
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
    exact ⟨hPc, hS⟩
  case lt =>
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (LessThan.circuit P) input _ _ ?_ (LessThan.computableWitnesses P) env env'
    intro k e1 e2 hle h_agree h_input
    have hk : offset + m + m ≤ k := by
      simp only [circuit_norm, witnessedMul_circuit_localLength] at hle; omega
    have hr := map_eval_varFromOffset_agree (off := offset + m) h_agree (by omega)
    have hn : Vector.map (Expression.eval e1.toEnvironment) input.modulus
        = Vector.map (Expression.eval e2.toEnvironment) input.modulus :=
      (eval_inputs_parts h_input).2.2
    simp only [circuit_norm]
    exact ⟨hr, hn⟩

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

/-! ## Sealing the witness programs

The programs are *data*, and big data: `circuit_norm` and any `rfl` that reaches a
circuit's `localLength` would otherwise start evaluating them, since the digit lists
are `map`s over `List.range` and the digit programs are ordinary recursions over
those. Downstream files reason through the bridges above instead.
-/

attribute [irreducible] qWitness rWitness

end MulMod

end

end Solution.Secp256k1ScalarMul
