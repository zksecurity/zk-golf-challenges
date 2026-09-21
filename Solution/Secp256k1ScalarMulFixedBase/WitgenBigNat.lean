import Solution.Secp256k1ScalarMulFixedBase.WitgenNat

/-!
# Big naturals in the witness IR's u64 sort

`WitgenNat` says what the digit operations *mean*; this file builds the witness-IR
programs that perform them, and proves each one leaves exactly those digits in its
`letU` locals.

A big value is carried as a *list of u64-sorted expressions*, one per digit, together
with the ℕ it denotes — that is `EvalsBig`. The monadic plumbing (`Computes`, its
`bind`, and `letU`) is the same `let`-chain reasoning the solution already used for
the modular-exponentiation chain, retargeted from the old unbounded Nat sort to u64.

Every operation here is a `Witgen.M` program that appends a fixed number of `letU`s per
digit, so a program's size is linear in the digit count (quadratic for multiplication,
and `bits × digits` for division). That is prover runtime, not elaboration cost: the
steps are produced by a recursive `def` and never reduced during type-checking.

## Step counts

Exactly (verified by evaluating `(p #[]).2.size`), with `la`/`lb` the operand digit
counts:

| program | steps | result digits |
|---|---|---|
| `readBitsAt`, `constDigits`, `bitAtE`, `limbF` | `0` (pure expressions) | |
| `addP a b c` | `2 · max la lb` | `max la lb + 1` |
| `shl1P a c` | `2 · la` | `la` |
| `subP a b c` | `3 · la` | `la` |
| `mulAddP b x c` | `2 · lb` | `lb + 1` |
| `selectP c a b` | `min la lb` | `min la lb` |
| `mulP a b` | `2 · la · (2 · lb + la)` | `lb + 2 · la` |
| `divStepP n bit q r` | `6 · rlen + 2 · qlen + 1` | |
| `divmodP n x qlen rlen bits` | `bits · (6 · rlen + 2 · qlen + 1)` | |
| `mulModP n a b qlen rlen bits` | `2 · la · (2 · lb + la) + bits · (6 · rlen + 2 · qlen + 1)` | `rlen` |
| `powModP n qlen rlen bits bs x` | `(bs.length + bs.count true)` × one `mulModP` | `rlen` |

Every intermediate in a `powModP` chain is an `rlen`-digit register, so its `mulModP`
calls cost `6 · rlen² + bits · (6 · rlen + 2 · qlen + 1)` each.

Concretely, for **secp** (`rlen = qlen = 9`, `bits = 512`): a `divmodP` is 37,376 steps,
a chained `mulModP` 486 + 37,376 = 37,862, and the Fermat inverse `invModP P256 …` runs
256 + 249 = 505 of them, so ≈ 19.1 M steps. For **one RSA mulmod** (`rlen = qlen = 129`,
`bits = 8192`): a `divmodP` is 8,462,336 steps and the whole `mulModP` 99,846 +
8,462,336 ≈ 8.56 M.

Binary long division dominates everything, by a factor `bits / rlen` over the
multiplication it follows. Knuth algorithm D (one base-`2^W` quotient digit per step
instead of one bit) would cut `divmodP` by a factor of about `W`, at the price of the
quotient-digit correction argument; reading the quotient register to recover the
remainder without a second division would help the callers that need both. Both are
follow-ups: this file does the simple provable thing and records the cost.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace WitgenBigNat

open Witgen WitgenNat

variable {K : Type} [FiniteField K] {α β γ δ : Type}

/-! ## `letU`-chain reasoning

Three facts about `Witgen.evalSteps`, each an easy induction, and the consequence that
makes a chain compositional: the value bound by a `let`-step is readable through
`localVar` in every extension of the state. -/

/-- Evaluating a concatenation of step lists is evaluating them in sequence. -/
theorem evalSteps_append (env : ProverEnvironment K) (steps steps' : List (Step K))
    (locals : Array (K ⊕ UInt64)) :
    evalSteps env (steps ++ steps') locals
      = evalSteps env steps' (evalSteps env steps locals) := by
  induction steps generalizing locals with
  | nil => rfl
  | cons st steps ih => cases st <;> simp only [List.cons_append, evalSteps, ih]

/-- Each step contributes exactly one local. -/
theorem size_evalSteps (env : ProverEnvironment K) (steps : List (Step K))
    (locals : Array (K ⊕ UInt64)) :
    (evalSteps env steps locals).size = locals.size + steps.length := by
  induction steps generalizing locals with
  | nil => simp [evalSteps]
  | cons st steps ih =>
      cases st <;> simp only [evalSteps, ih, List.length_cons, Array.size_push] <;> omega

/-- Appending steps never disturbs an already-bound local. -/
theorem getElem?_evalSteps (env : ProverEnvironment K) (steps : List (Step K))
    (locals : Array (K ⊕ UInt64)) {i : ℕ} (hi : i < locals.size) :
    (evalSteps env steps locals)[i]? = locals[i]? := by
  induction steps generalizing locals with
  | nil => rfl
  | cons st steps ih =>
      cases st <;>
        simp only [evalSteps] <;>
        rw [ih _ (by rw [Array.size_push]; omega), Array.getElem?_push,
          if_neg (by omega : ¬ i = locals.size)]

/-- The local bound by a `letU` step, read back through `localVar`, in an arbitrary
extension of the state that bound it. -/
theorem eval_localVar_push_letU (env : ProverEnvironment K) (S : Array (Step K))
    (e : U64Expr K) (steps : List (Step K)) (i : ℕ) :
    U64Expr.eval { env, locals := evalSteps env (S.toList ++ Step.letU e :: steps), idx := i }
        (.localVar S.size)
      = U64Expr.eval { env, locals := evalSteps env S.toList } e := by
  have hsize : (evalSteps env S.toList : Array (K ⊕ UInt64)).size = S.size := by
    rw [size_evalSteps]; simp
  rw [evalSteps_append]
  simp only [evalSteps, U64Expr.eval]
  rw [getElem?_evalSteps _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
    if_pos hsize.symm]

/-! ## What a u64-sorted expression computes -/

/-- The u64-sorted expression `e` has ℕ value `val env` in every context extending `S`. -/
def EvalsU (S : Array (Step K)) (e : U64Expr K) (val : ProverEnvironment K → ℕ) : Prop :=
  ∀ (env : ProverEnvironment K) (steps : List (Step K)) (i : ℕ), S.toList <+: steps →
    (U64Expr.eval { env, locals := evalSteps env steps, idx := i } e).toNat = val env

theorem EvalsU.mono {S S' : Array (Step K)} {e : U64Expr K} {val}
    (h : EvalsU S e val) (hS : S.toList <+: S'.toList) : EvalsU S' e val :=
  fun env steps i hsteps => h env steps i (hS.trans hsteps)

theorem EvalsU.congr {S : Array (Step K)} {e : U64Expr K} {val val'}
    (h : EvalsU S e val) (hv : ∀ env, val env = val' env) : EvalsU S e val' :=
  fun env steps i hsteps => (h env steps i hsteps).trans (hv env)

theorem EvalsU.eval {S : Array (Step K)} {e : U64Expr K} {val} (h : EvalsU S e val)
    (env : ProverEnvironment K) :
    (U64Expr.eval { env, locals := evalSteps env S.toList } e).toNat = val env :=
  h env S.toList 0 (List.prefix_refl _)

/-- Whatever a u64 expression computes is below `2 ^ 64`. -/
theorem EvalsU.lt {S : Array (Step K)} {e : U64Expr K} {val} (h : EvalsU S e val)
    (env : ProverEnvironment K) : val env < 2 ^ 64 := by
  rw [← h.eval env]
  exact (U64Expr.eval _ e).toNat_lt_size

/-! ## What a *list* of u64 expressions computes

A big value is a digit list: each entry computes one digit, every digit is a digit, and
together they denote `val env`. Keeping the digit list itself environment-dependent is
what lets the division loop's registers be described at all. -/

/-- The expressions `ds` are the digits `dv env`, in every context extending `S`. The
denoted value is then `lval (dv env)`, which the `WitgenNat` lemmas compute. The digit
list is a parameter rather than an existential so that callers can name it: it is
always one of the `WitgenNat` functions applied to the operands' digits. -/
def EvalsBig (S : Array (Step K)) (ds : List (U64Expr K))
    (dv : ProverEnvironment K → List ℕ) : Prop :=
  (∀ env, (dv env).length = ds.length)
    ∧ (∀ env, Bounded (dv env))
    ∧ ∀ k (hk : k < ds.length), EvalsU S ds[k] (fun env => (dv env).getD k 0)

theorem EvalsBig.length_eq {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (env : ProverEnvironment K) : (dv env).length = ds.length :=
  h.1 env

theorem EvalsBig.bounded {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (env : ProverEnvironment K) : Bounded (dv env) := h.2.1 env

theorem EvalsBig.evals {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (k : ℕ) (hk : k < ds.length) :
    EvalsU S ds[k] (fun env => (dv env).getD k 0) := h.2.2 k hk

theorem EvalsBig.mono {S S' : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (hS : S.toList <+: S'.toList) : EvalsBig S' ds dv :=
  ⟨h.1, h.2.1, fun k hk => (h.2.2 k hk).mono hS⟩

theorem EvalsBig.congr {S : Array (Step K)} {ds : List (U64Expr K)} {dv dv'}
    (h : EvalsBig S ds dv) (hv : ∀ env, dv env = dv' env) : EvalsBig S ds dv' := by
  refine ⟨fun env => ?_, fun env => ?_, fun k hk => ?_⟩
  · rw [← hv env]; exact h.1 env
  · rw [← hv env]; exact h.2.1 env
  · exact (h.2.2 k hk).congr fun env => by rw [hv env]

/-! ## What a field-sorted expression computes

A witness program's *output* is field-sorted, and so is the way a limb leaves the digit
layer (`limbF`). `EvalsF` is the field analogue of `EvalsU`, and `EvalsV` the analogue
for the whole output vector; `EvalsV.lit` is what turns per-limb facts into a statement
about the vector a `witnessVectorProgram` site produces. -/

/-- The field-sorted expression `e` has value `val env` in every context extending `S`. -/
def EvalsF (S : Array (Step K)) (e : FExpr K) (val : ProverEnvironment K → K) : Prop :=
  ∀ (env : ProverEnvironment K) (steps : List (Step K)) (i : ℕ), S.toList <+: steps →
    FExpr.eval { env, locals := evalSteps env steps, idx := i } e = val env

theorem EvalsF.mono {S S' : Array (Step K)} {e : FExpr K} {val}
    (h : EvalsF S e val) (hS : S.toList <+: S'.toList) : EvalsF S' e val :=
  fun env steps i hsteps => h env steps i (hS.trans hsteps)

theorem EvalsF.congr {S : Array (Step K)} {e : FExpr K} {val val'}
    (h : EvalsF S e val) (hv : ∀ env, val env = val' env) : EvalsF S e val' :=
  fun env steps i hsteps => (h env steps i hsteps).trans (hv env)

theorem EvalsF.eval {S : Array (Step K)} {e : FExpr K} {val} (h : EvalsF S e val)
    (env : ProverEnvironment K) :
    FExpr.eval { env, locals := evalSteps env S.toList } e = val env :=
  h env S.toList 0 (List.prefix_refl _)

/-- The vector output `out` has value `val env` in every context extending `S`. -/
def EvalsV {n : ℕ} (S : Array (Step K)) (out : VExpr K n)
    (val : ProverEnvironment K → Vector K n) : Prop :=
  ∀ (env : ProverEnvironment K) (steps : List (Step K)) (i : ℕ), S.toList <+: steps →
    VExpr.eval { env, locals := evalSteps env steps, idx := i } out = val env

theorem EvalsV.eval {n : ℕ} {S : Array (Step K)} {out : VExpr K n} {val}
    (h : EvalsV S out val) (env : ProverEnvironment K) :
    VExpr.eval { env, locals := evalSteps env S.toList } out = val env :=
  h env S.toList 0 (List.prefix_refl _)

theorem EvalsV.congr {n : ℕ} {S : Array (Step K)} {out : VExpr K n} {val val'}
    (h : EvalsV S out val) (hv : ∀ env, val env = val' env) : EvalsV S out val' :=
  fun env steps i hs => (h env steps i hs).trans (hv env)

/-- A literal output vector, from a fact per entry. Big-integer gadgets assemble their
outputs limb by limb (`limbF`), so this is the last step of every bridge lemma. -/
theorem EvalsV.lit {n : ℕ} {S : Array (Step K)} {es : Vector (FExpr K) n}
    {val : ProverEnvironment K → Vector K n}
    (h : ∀ (k : ℕ) (hk : k < n), EvalsF S es[k] (fun env => (val env)[k])) :
    EvalsV S (.lit es) val := by
  intro env steps i hs
  ext k hk
  simp only [VExpr.eval, Vector.getElem_map]
  exact h k hk env steps i hs

/-! ## Builder programs

`Computes Ev S p val` is the compositional statement about a `Witgen.M` program: run
from state `S` it only *appends* steps, and its result satisfies `Ev` at the final
state. `Ev` is a parameter so that one set of monadic lemmas serves every sort: a digit
program chains `U64Expr`s, returns a `List (U64Expr K)`, and the top-level witness site
returns a `VExpr`. -/

/-- A builder program `p`, started at state `S`, only appends steps, and the IR object
it returns computes `val` (in the sense of `Ev`) at its final state. -/
def Computes (Ev : Array (Step K) → α → (ProverEnvironment K → β) → Prop)
    (S : Array (Step K)) (p : M K α) (val : ProverEnvironment K → β) : Prop :=
  S.toList <+: (p S).2.toList ∧ Ev (p S).2 (p S).1 val

@[inherit_doc Computes]
abbrev ComputesU (S : Array (Step K)) (p : M K (U64Expr K))
    (val : ProverEnvironment K → ℕ) : Prop := Computes EvalsU S p val

@[inherit_doc Computes]
abbrev ComputesBig (S : Array (Step K)) (p : M K (List (U64Expr K)))
    (dv : ProverEnvironment K → List ℕ) : Prop := Computes EvalsBig S p dv

@[inherit_doc Computes]
abbrev ComputesF (S : Array (Step K)) (p : M K (FExpr K))
    (val : ProverEnvironment K → K) : Prop := Computes EvalsF S p val

@[inherit_doc Computes]
abbrev ComputesV {n : ℕ} (S : Array (Step K)) (p : M K (VExpr K n))
    (val : ProverEnvironment K → Vector K n) : Prop := Computes EvalsV S p val

variable {Ev : Array (Step K) → α → (ProverEnvironment K → β) → Prop}
  {Ev' : Array (Step K) → γ → (ProverEnvironment K → δ) → Prop}

omit [FiniteField K] in
/-- `pure` appends nothing, so it computes whatever its argument evaluates to. -/
theorem Computes.pure {S : Array (Step K)} {a : α} {val} (h : Ev S a val) :
    Computes Ev S (Pure.pure a) val :=
  ⟨List.prefix_refl _, h⟩

omit [FiniteField K] in
/-- **The composition lemma.** The continuation is handed the intermediate state `S'`,
the proof that it extends `S` (so earlier `Evals*` facts lift through `Evals*.mono`),
and the fact that the bound value computes `pv` at `S'`. -/
theorem Computes.bind {S : Array (Step K)} {p : M K α} {f : α → M K γ}
    {pv : ProverEnvironment K → β} {fv : ProverEnvironment K → δ}
    (hp : Computes Ev S p pv)
    (hf : ∀ (S' : Array (Step K)) (a : α), S.toList <+: S'.toList → Ev S' a pv →
      Computes Ev' S' (f a) fv) :
    Computes Ev' S (p >>= f) fv := by
  obtain ⟨hgrow, hres⟩ := hp
  obtain ⟨hgrow', hres'⟩ := hf (p S).2 (p S).1 hgrow hres
  exact ⟨hgrow.trans hgrow', hres'⟩

theorem ComputesU.congr {S : Array (Step K)} {p : M K (U64Expr K)} {val val'}
    (h : ComputesU S p val) (hv : ∀ env, val env = val' env) : ComputesU S p val' :=
  ⟨h.1, h.2.congr hv⟩

theorem ComputesV.congr {n : ℕ} {S : Array (Step K)} {p : M K (VExpr K n)} {val val'}
    (h : ComputesV S p val) (hv : ∀ env, val env = val' env) : ComputesV S p val' :=
  ⟨h.1, h.2.congr hv⟩

theorem ComputesBig.congr {S : Array (Step K)} {p : M K (List (U64Expr K))} {dv dv'}
    (h : ComputesBig S p dv) (hv : ∀ env, dv env = dv' env) : ComputesBig S p dv' :=
  ⟨h.1, h.2.congr hv⟩

/-- Binding a u64 value as a shared step: the returned `localVar` computes it. This is
the only way a digit ever enters the program, which is what keeps a program's term size
linear in its step count. -/
theorem ComputesU.letU {S : Array (Step K)} {e : U64Expr K} {val}
    (h : EvalsU S e val) : ComputesU S (Witgen.letU e) val := by
  refine ⟨?_, ?_⟩
  · show S.toList <+: (S.push (Step.letU e)).toList
    rw [Array.toList_push]
    exact List.prefix_append _ _
  · show EvalsU (S.push (Step.letU e)) (.localVar S.size) val
    intro env steps i hsteps
    rw [Array.toList_push] at hsteps
    obtain ⟨rest, hrest⟩ := hsteps
    subst hrest
    rw [List.append_assoc, List.singleton_append, eval_localVar_push_letU]
    exact h.eval env

/-- `Witgen.M.toIR` of a vector program that computes `val`: this is the bridge lemma
for a `Circuit.witnessVectorProgram` site. -/
theorem ComputesV.toIR {n : ℕ} {p : M K (VExpr K n)} {val} (h : ComputesV #[] p val)
    (env : ProverEnvironment K) : p.toIR.eval env = val env :=
  h.2.eval env

/-! ## Leaf expressions

One lemma per u64 operation, each carrying the explicit non-wrap bound where the
operation could wrap. Proved once here (through the `UInt64.toNat_*` lemmas) so that no
digit program ever has to look at `UInt64` again. -/

/-- A `UInt64` constant. Every constant written in this file goes through `uc` instead,
but a caller using the `OfNat` sugar (`(0 : U64Expr _)`) lands on this shape. -/
theorem EvalsU.const {S : Array (Step K)} (c : UInt64) :
    EvalsU S (.const c) (fun _ => c.toNat) := fun _ _ _ _ => rfl

/-- A ℕ constant as a u64-sorted expression. -/
def uc (n : ℕ) : U64Expr K := .const (UInt64.ofNat n)

theorem EvalsU.uc {S : Array (Step K)} (n : ℕ) (hn : n < 2 ^ 64) :
    EvalsU S (uc n) (fun _ => n) := fun env steps i hs => by
  simp only [WitgenBigNat.uc, U64Expr.eval, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem EvalsU.add {S : Array (Step K)} {x y : U64Expr K} {xv yv}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) (hb : ∀ env, xv env + yv env < 2 ^ 64) :
    EvalsU S (.add x y) (fun env => xv env + yv env) := fun env steps i hs => by
  simp only [U64Expr.eval, UInt64.toNat_add, hx env steps i hs, hy env steps i hs]
  exact Nat.mod_eq_of_lt (hb env)

theorem EvalsU.mul {S : Array (Step K)} {x y : U64Expr K} {xv yv}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) (hb : ∀ env, xv env * yv env < 2 ^ 64) :
    EvalsU S (.mul x y) (fun env => xv env * yv env) := fun env steps i hs => by
  simp only [U64Expr.eval, UInt64.toNat_mul, hx env steps i hs, hy env steps i hs]
  exact Nat.mod_eq_of_lt (hb env)

theorem EvalsU.div {S : Array (Step K)} {x y : U64Expr K} {xv yv}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) :
    EvalsU S (.div x y) (fun env => xv env / yv env) := fun env steps i hs => by
  simp only [U64Expr.eval, UInt64.toNat_div, hx env steps i hs, hy env steps i hs]

theorem EvalsU.mod {S : Array (Step K)} {x y : U64Expr K} {xv yv}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) :
    EvalsU S (.mod x y) (fun env => xv env % yv env) := fun env steps i hs => by
  simp only [U64Expr.eval, UInt64.toNat_mod, hx env steps i hs, hy env steps i hs]

theorem EvalsU.shiftR {S : Array (Step K)} {x y : U64Expr K} {xv yv}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) (hy64 : ∀ env, yv env < 64) :
    EvalsU S (.shiftR x y) (fun env => xv env / 2 ^ yv env) := fun env steps i hs => by
  simp only [U64Expr.eval, UInt64.toNat_shiftRight, hx env steps i hs, hy env steps i hs,
    Nat.mod_eq_of_lt (hy64 env), Nat.shiftRight_eq_div_pow]

theorem EvalsU.shiftL {S : Array (Step K)} {x y : U64Expr K} {xv yv}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) (hy64 : ∀ env, yv env < 64)
    (hb : ∀ env, xv env * 2 ^ yv env < 2 ^ 64) :
    EvalsU S (.shiftL x y) (fun env => xv env * 2 ^ yv env) := fun env steps i hs => by
  simp only [U64Expr.eval, UInt64.toNat_shiftLeft, hx env steps i hs, hy env steps i hs,
    Nat.mod_eq_of_lt (hy64 env), Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (hb env)

/-- A comparison branch. Carries and borrows are exactly this shape: two comparisons,
never a division by the base. -/
theorem EvalsU.iteLt {S : Array (Step K)} {x y t e : U64Expr K} {xv yv tv ev}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) (ht : EvalsU S t tv) (he : EvalsU S e ev) :
    EvalsU S (.ite (.lt x y) t e) (fun env => if xv env < yv env then tv env else ev env) :=
  fun env steps i hs => by
  simp only [U64Expr.eval, BExpr.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
    hx env steps i hs, hy env steps i hs]
  split
  · exact ht env steps i hs
  · exact he env steps i hs

/-- An equality branch (`BExpr.neq` is u64 *equality*, despite the constructor name). -/
theorem EvalsU.iteEq {S : Array (Step K)} {x y t e : U64Expr K} {xv yv tv ev}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) (ht : EvalsU S t tv) (he : EvalsU S e ev) :
    EvalsU S (.ite (.neq x y) t e) (fun env => if xv env = yv env then tv env else ev env) :=
  fun env steps i hs => by
  simp only [U64Expr.eval, BExpr.eval, decide_eq_true_eq, UInt64.eq_iff_toNat_eq,
    hx env steps i hs, hy env steps i hs]
  split
  · exact ht env steps i hs
  · exact he env steps i hs

/-- Bit `i` of a circuit expression's field value, as a `0`/`1` u64 expression. A limb
is far wider than 64 bits, so this (not `U64Expr.val`, which truncates) is the only way
a big value is read out of the field. -/
theorem EvalsU.bit {S : Array (Step K)} (e : Expression K) (i : ℕ) :
    EvalsU S (.ite (.bit (.expr e) i) (WitgenBigNat.uc 1) (WitgenBigNat.uc 0))
      (fun env => FiniteField.val (Expression.eval env.toEnvironment e) / 2 ^ i % 2) :=
  fun env steps j hs => by
  simp only [U64Expr.eval, BExpr.eval, FExpr.eval]
  rw [← Nat.toNat_testBit]
  rcases Bool.eq_false_or_eq_true
      ((FiniteField.val (Expression.eval env.toEnvironment e)).testBit i) with h | h <;>
    simp [h, WitgenBigNat.uc, U64Expr.eval]

/-- `x - y` in the u64 sort, which has no subtraction: `(2^64 - 1) · y` is `-y` modulo
`2^64`, so a wrapping add lands on the difference whenever `y ≤ x`. -/
def usub (x y : U64Expr K) : U64Expr K := .add x (.mul (uc (2 ^ 64 - 1)) y)

private theorem usub_key (P x y : ℕ) (hP : 0 < P) (hle : y ≤ x) :
    x + (P - 1) * y = x - y + P * y := by
  have h : (P - 1) * y + y = P * y := by
    rw [Nat.sub_mul, Nat.one_mul]
    have : y ≤ P * y := Nat.le_mul_of_pos_left _ hP
    omega
  omega

theorem EvalsU.usub {S : Array (Step K)} {x y : U64Expr K} {xv yv}
    (hx : EvalsU S x xv) (hy : EvalsU S y yv) (hle : ∀ env, yv env ≤ xv env) :
    EvalsU S (WitgenBigNat.usub x y) (fun env => xv env - yv env) := fun env steps i hs => by
  have hxlt := hx.lt env
  have hP : 0 < 2 ^ 64 := Nat.two_pow_pos 64
  simp only [WitgenBigNat.usub, WitgenBigNat.uc, U64Expr.eval, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.toNat_ofNat', hx env steps i hs, hy env steps i hs,
    Nat.mod_eq_of_lt (show 2 ^ 64 - 1 < 2 ^ 64 by omega), Nat.add_mod_mod, usub_key _ _ _ hP (hle env), Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-! ### Field-sorted leaves -/

theorem EvalsF.const {S : Array (Step K)} (c : K) : EvalsF S (.const c) (fun _ => c) :=
  fun _ _ _ _ => rfl

theorem EvalsF.expr {S : Array (Step K)} (e : Expression K) :
    EvalsF S (.expr e) (fun env => Expression.eval env.toEnvironment e) := fun _ _ _ _ => rfl

theorem EvalsF.add {S : Array (Step K)} {x y : FExpr K} {xv yv}
    (hx : EvalsF S x xv) (hy : EvalsF S y yv) :
    EvalsF S (.add x y) (fun env => xv env + yv env) := fun env steps i hs => by
  simp only [FExpr.eval, hx env steps i hs, hy env steps i hs]

theorem EvalsF.mul {S : Array (Step K)} {x y : FExpr K} {xv yv}
    (hx : EvalsF S x xv) (hy : EvalsF S y yv) :
    EvalsF S (.mul x y) (fun env => xv env * yv env) := fun env steps i hs => by
  simp only [FExpr.eval, hx env steps i hs, hy env steps i hs]

/-- The u64-to-field bridge. Note this is `FiniteField.fromNat`, not `Nat.cast`: on a
binary field the two differ, which is why the limb assembly below is stated on `F p`. -/
theorem EvalsF.ofU64 {S : Array (Step K)} {x : U64Expr K} {xv} (h : EvalsU S x xv) :
    EvalsF S (.ofU64 x) (fun env => FiniteField.fromNat (xv env)) :=
  fun env steps i hs => by simp only [FExpr.eval, h env steps i hs]

/-! ### Lists of field expressions -/

/-- What a list of field expressions computes, entry by entry. Out of range the list
reads as the constant `0`, so the value function is total. -/
def EvalsFL (S : Array (Step K)) (es : List (FExpr K))
    (val : ProverEnvironment K → ℕ → K) : Prop :=
  ∀ k, EvalsF S (es.getD k (.const 0)) (fun env => val env k)

@[inherit_doc Computes]
abbrev ComputesFL (S : Array (Step K)) (p : M K (List (FExpr K)))
    (val : ProverEnvironment K → ℕ → K) : Prop := Computes EvalsFL S p val

theorem EvalsFL.congr {S : Array (Step K)} {es : List (FExpr K)} {val val'}
    (h : EvalsFL S es val) (hv : ∀ env k, val env k = val' env k) : EvalsFL S es val' :=
  fun k => (h k).congr fun env => hv env k

theorem ComputesFL.congr {S : Array (Step K)} {p : M K (List (FExpr K))} {val val'}
    (h : ComputesFL S p val) (hv : ∀ env k, val env k = val' env k) : ComputesFL S p val' :=
  ⟨h.1, h.2.congr hv⟩

theorem EvalsFL.nil {S : Array (Step K)} {val} (hv : ∀ env k, val env k = 0) :
    EvalsFL S ([] : List (FExpr K)) val :=
  fun k => (EvalsF.const 0).congr fun env => (hv env k).symm

theorem EvalsFL.cons {S : Array (Step K)} {e : FExpr K} {es : List (FExpr K)} {val}
    (h : EvalsF S e (fun env => val env 0))
    (ht : EvalsFL S es (fun env k => val env (k + 1))) : EvalsFL S (e :: es) val := by
  intro k
  cases k with
  | zero => exact h
  | succ k => exact ht k

theorem EvalsFL.mono {S S' : Array (Step K)} {es : List (FExpr K)} {val}
    (h : EvalsFL S es val) (hS : S.toList <+: S'.toList) : EvalsFL S' es val :=
  fun k => (h k).mono hS

/-- A literal output vector read off a computed list: the shape of every witness site
whose entries are produced by a recursion. -/
theorem EvalsV.ofFL {n : ℕ} {S : Array (Step K)} {es : List (FExpr K)} {val}
    (h : EvalsFL S es val) :
    EvalsV S (.lit (Vector.ofFn fun k : Fin n => es.getD k.val (.const 0)))
      (fun env => Vector.ofFn fun k : Fin n => val env k.val) :=
  EvalsV.lit fun k hk => by
    simpa only [Vector.getElem_ofFn] using h k

/-! ## Digit lists: cons, tail, and indexed access

The IR digit programs recurse on the *expression* list, whose shape is known, while the
ℕ digit list they denote is a function of the environment and so cannot be matched on.
These lemmas move between the two: an expression list that is a `cons` forces its value
to be a `cons` too, with `headD`/`tail` naming the pieces. -/

private theorem getD_zero (l : List ℕ) : l.getD 0 0 = l.headD 0 := by cases l <;> rfl

private theorem getD_succ (l : List ℕ) (k : ℕ) : l.getD (k + 1) 0 = l.tail.getD k 0 := by
  cases l <;> rfl

private theorem eq_headD_cons_tail {l : List ℕ} (h : l ≠ []) : l = l.headD 0 :: l.tail := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

theorem getD_of_lt {σ : Type} {l : List σ} {k : ℕ} (d : σ) (hk : k < l.length) :
    l.getD k d = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dif_pos hk]

theorem getD_of_ge {σ : Type} {l : List σ} {k : ℕ} (d : σ) (hk : l.length ≤ k) :
    l.getD k d = d := by
  rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dif_neg (by omega)]

theorem EvalsBig.nil {S : Array (Step K)} : EvalsBig S [] (fun _ => []) :=
  ⟨fun _ => rfl, fun _ => Bounded.nil, fun k hk => absurd hk (by simp)⟩

theorem EvalsBig.cons {S : Array (Step K)} {e : U64Expr K} {es : List (U64Expr K)}
    {hv : ProverEnvironment K → ℕ} {tv : ProverEnvironment K → List ℕ}
    (he : EvalsU S e hv) (hb : ∀ env, hv env < base) (ht : EvalsBig S es tv) :
    EvalsBig S (e :: es) (fun env => hv env :: tv env) := by
  refine ⟨fun env => by simp [ht.length_eq env],
    fun env => Bounded.cons (hb env) (ht.bounded env), fun k hk => ?_⟩
  cases k with
  | zero =>
    simp only [List.getElem_cons_zero, List.getD_cons_zero]
    exact he
  | succ k =>
    simp only [List.getElem_cons_succ, List.getD_cons_succ]
    exact ht.evals k (by simpa using hk)

theorem EvalsBig.eq_nil {S : Array (Step K)} {dv} (h : EvalsBig S ([] : List (U64Expr K)) dv)
    (env : ProverEnvironment K) : dv env = [] :=
  List.eq_nil_of_length_eq_zero (by simpa using h.length_eq env)

theorem EvalsBig.head {S : Array (Step K)} {e : U64Expr K} {es : List (U64Expr K)} {dv}
    (h : EvalsBig S (e :: es) dv) : EvalsU S e (fun env => (dv env).headD 0) := by
  have h0 := h.evals 0 (by simp)
  simp only [List.getElem_cons_zero] at h0
  exact h0.congr fun env => getD_zero _

theorem EvalsBig.tail {S : Array (Step K)} {e : U64Expr K} {es : List (U64Expr K)} {dv}
    (h : EvalsBig S (e :: es) dv) : EvalsBig S es (fun env => (dv env).tail) := by
  refine ⟨fun env => ?_, fun env => bounded_tail (h.bounded env), fun k hk => ?_⟩
  · have hl := h.length_eq env
    simp only [List.length_cons] at hl
    rw [List.length_tail, hl]
    omega
  · have hs := h.evals (k + 1) (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_succ] at hs
    exact hs.congr fun env => getD_succ _ _

/-- A `cons` of expressions forces its value to be a `cons`; this is how a program's
digit recursion is matched with the `WitgenNat` function's. -/
theorem EvalsBig.cons_eq {S : Array (Step K)} {e : U64Expr K} {es : List (U64Expr K)} {dv}
    (h : EvalsBig S (e :: es) dv) (env : ProverEnvironment K) :
    dv env = (dv env).headD 0 :: (dv env).tail :=
  eq_headD_cons_tail (by
    intro hc
    have hl := h.length_eq env
    rw [hc] at hl
    simp at hl)

theorem EvalsBig.headD_lt {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (env : ProverEnvironment K) : (dv env).headD 0 < base :=
  WitgenNat.headD_lt (h.bounded env)

/-- The head of a digit list, zero-padded: the second operand of a subtraction may be
shorter than the first, exactly as in `WitgenNat.subb`. -/
theorem EvalsBig.headD {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) : EvalsU S (ds.headD (uc 0)) (fun env => (dv env).headD 0) := by
  cases ds with
  | nil => exact (EvalsU.uc 0 (by norm_num)).congr fun env => by rw [h.eq_nil env]; rfl
  | cons e es => exact h.head

theorem EvalsBig.tail' {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) : EvalsBig S ds.tail (fun env => (dv env).tail) := by
  cases ds with
  | nil => exact EvalsBig.nil.congr fun env => by rw [h.eq_nil env]; rfl
  | cons e es => exact h.tail

/-- Digit `k`, zero past the end. -/
theorem EvalsBig.getD {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (k : ℕ) :
    EvalsU S (ds.getD k (uc 0)) (fun env => (dv env).getD k 0) := by
  by_cases hk : k < ds.length
  · rw [getD_of_lt _ hk]
    exact h.evals k hk
  · rw [getD_of_ge _ (by omega)]
    refine (EvalsU.uc 0 (by norm_num)).congr fun env => ?_
    rw [getD_of_ge _ (by rw [h.length_eq env]; omega)]

/-- A prover environment always exists (a constantly-zero assignment will do). That is
all the length arguments below need: an `EvalsBig` fact pins the *expression* list's
length to the denoted digit list's length at every environment, so one environment is
enough to compare two expression lists. -/
private def someEnv (K : Type) [FiniteField K] : ProverEnvironment K where
  get _ := 0
  data _ _ := #[]
  hint := default

/-- Two digit lists whose denoted lengths agree have the same number of expressions.
`selectP` needs exactly this, and cannot get it any other way: its two branches are
produced by two different subprograms, and `Computes.bind` hands the continuation an
*arbitrary* result object, so no lemma about a particular program's output applies. -/
theorem EvalsBig.length_expr {S S' : Array (Step K)} {ds ds' : List (U64Expr K)} {dv dv'}
    (h : EvalsBig S ds dv) (h' : EvalsBig S' ds' dv')
    (hlen : ∀ env, (dv env).length = (dv' env).length) : ds.length = ds'.length := by
  rw [← h.length_eq (someEnv K), ← h'.length_eq (someEnv K), hlen]

/-- The expression count of a register whose value is written in canonical form. -/
theorem EvalsBig.length_ofNat {S : Array (Step K)} {ds : List (U64Expr K)}
    {V : ProverEnvironment K → ℕ} {len : ℕ}
    (h : EvalsBig S ds (fun env => ofNat (V env) len)) : ds.length = len := by
  have := h.length_eq (someEnv K); simpa using this.symm

/-! ## Expression-level readers and writers

None of these appends a single step: they are pure expressions over the operands, so a
reader costs nothing in program size. -/

/-- `len` digits, digit `k` given by `f k`. A `map` over `List.range` rather than a
recursion, so length and elements reduce by `simp`. -/
def ofFnDigits (f : ℕ → U64Expr K) (len : ℕ) : List (U64Expr K) := (List.range len).map f

omit [FiniteField K] in
@[simp] theorem length_ofFnDigits (f : ℕ → U64Expr K) (len : ℕ) :
    (ofFnDigits f len).length = len := by simp [ofFnDigits]

omit [FiniteField K] in
@[simp] theorem getElem_ofFnDigits (f : ℕ → U64Expr K) (len k : ℕ)
    (hk : k < (ofFnDigits f len).length) : (ofFnDigits f len)[k] = f k := by
  simp [ofFnDigits]

theorem evalsBig_ofFnDigits {S : Array (Step K)} {f : ℕ → U64Expr K} {len : ℕ}
    {dv : ProverEnvironment K → List ℕ}
    (hlen : ∀ env, (dv env).length = len) (hbd : ∀ env, Bounded (dv env))
    (hf : ∀ k, k < len → EvalsU S (f k) (fun env => (dv env).getD k 0)) :
    EvalsBig S (ofFnDigits f len) dv :=
  ⟨fun env => by rw [hlen env, length_ofFnDigits], hbd,
   fun k hk => by rw [getElem_ofFnDigits]; exact hf k (by simpa using hk)⟩

/-- `Σ_{i<w} 2^i · f (lo + i)` as a u64 expression: a Horner fold over bit positions, so
the term is linear in `w` and, with every `f` valued in `{0, 1}`, stays below `2^w`. -/
def bitsToDigit (f : ℕ → U64Expr K) (lo : ℕ) : ℕ → U64Expr K
  | 0 => uc 0
  | w + 1 => .add (f lo) (.mul (bitsToDigit f (lo + 1) w) (uc 2))

theorem evalsU_bitsToDigit {S : Array (Step K)} {f : ℕ → U64Expr K}
    {g : ProverEnvironment K → ℕ → ℕ}
    (hf : ∀ j, EvalsU S (f j) (fun env => g env j)) (hg : ∀ env j, g env j < 2) :
    ∀ (w lo : ℕ), w ≤ 62 →
      EvalsU S (bitsToDigit f lo w) (fun env => bitWindow (g env) lo w) := by
  intro w
  induction w with
  | zero =>
    intro lo _
    exact (EvalsU.uc 0 (by norm_num)).congr fun env => by simp [bitWindow]
  | succ w ih =>
    intro lo hw
    have hbnd : ∀ env, bitWindow (g env) (lo + 1) w * 2 < 2 ^ 64 := by
      intro env
      have h1 : bitWindow (g env) (lo + 1) w < 2 ^ w := bitWindow_lt (hg env) _ _
      have h3 : (2 : ℕ) ^ (w + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc bitWindow (g env) (lo + 1) w * 2 < 2 ^ w * 2 := by omega
        _ = 2 ^ (w + 1) := (pow_succ 2 w).symm
        _ ≤ 2 ^ 64 := h3
    refine (EvalsU.add (hf lo)
      (EvalsU.mul (ih (lo + 1) (by omega)) (EvalsU.uc 2 (by norm_num)) hbnd) ?_).congr ?_
    · intro env
      have := hbnd env
      have := hg env lo
      omega
    · intro env
      simp only [bitWindow]
      omega

/-- Bit `j` of `e`'s `nbits`-wide low window shifted up by `off`, as a u64 expression:
`BExpr.bit` reads the bit straight off the field element (a limb is far wider than 64
bits, so `U64Expr.val` would truncate), and positions outside the window are literal
zeros. -/
def winBit (e : Expression K) (off nbits j : ℕ) : U64Expr K :=
  if off ≤ j ∧ j < off + nbits then .ite (.bit (.expr e) (j - off)) (uc 1) (uc 0) else uc 0

theorem evalsU_winBit {S : Array (Step K)} (e : Expression K) (off nbits j : ℕ) :
    EvalsU S (winBit e off nbits j)
      (fun env => if off ≤ j ∧ j < off + nbits
        then FiniteField.val (Expression.eval env.toEnvironment e) / 2 ^ (j - off) % 2
        else 0) := by
  rw [winBit]
  split
  · exact EvalsU.bit e (j - off)
  · exact EvalsU.uc 0 (by norm_num)

/-- The digits of `e`'s `nbits`-wide low window, shifted up by `off` bits. -/
def readBitsAt (e : Expression K) (off nbits : ℕ) : List (U64Expr K) :=
  ofFnDigits (fun k => bitsToDigit (winBit e off nbits) (W * k) W) (numChunks (off + nbits))

theorem evalsBig_readBitsAt {S : Array (Step K)} (e : Expression K) (off nbits : ℕ) :
    EvalsBig S (readBitsAt e off nbits)
      (fun env => ofNat
        (FiniteField.val (Expression.eval env.toEnvironment e) % 2 ^ nbits * 2 ^ off)
        (numChunks (off + nbits))) := by
  refine evalsBig_ofFnDigits (fun _ => length_ofNat _ _) (fun _ => bounded_ofNat _ _)
    (fun k hk => ?_)
  refine (evalsU_bitsToDigit (evalsU_winBit e off nbits) ?_ W (W * k) (by rw [W]; omega)).congr ?_
  · intro env j
    split
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
  · intro env
    have hbits : (fun j => if off ≤ j ∧ j < off + nbits
          then FiniteField.val (Expression.eval env.toEnvironment e) / 2 ^ (j - off) % 2
          else 0)
        = fun j => FiniteField.val (Expression.eval env.toEnvironment e) % 2 ^ nbits
            * 2 ^ off / 2 ^ j % 2 := by
      funext j; rw [bit_shifted_window]
    rw [hbits, bitWindow_bits, getD_ofNat _ _ _ hk, base_pow, base]

/-- A literal big value as digits. -/
def constDigits (v len : ℕ) : List (U64Expr K) :=
  ofFnDigits (fun k => uc (v / base ^ k % base)) len

theorem evalsBig_constDigits {S : Array (Step K)} (v len : ℕ) :
    EvalsBig S (constDigits v len) (fun _ => ofNat v len) :=
  evalsBig_ofFnDigits (fun _ => length_ofNat _ _) (fun _ => bounded_ofNat _ _)
    (fun k hk => (EvalsU.uc _ (lt_trans (Nat.mod_lt _ base_pos) base_lt)).congr
      fun _ => (getD_ofNat v len k hk).symm)

omit [FiniteField K] in
@[simp] theorem length_constDigits (v len : ℕ) :
    (constDigits v len : List (U64Expr K)).length = len := by
  simp [constDigits]

private theorem mod_W_lt_pow (i : ℕ) : i % W < 2 ^ 64 :=
  lt_trans (show i % W < 64 by rw [W]; omega) (by norm_num)

/-- Bit `i` of a digit list, as a u64 expression: one digit read, one shift, one mask. -/
def bitAtE (ds : List (U64Expr K)) (i : ℕ) : U64Expr K :=
  .mod (.shiftR (ds.getD (i / W) (uc 0)) (uc (i % W))) (uc 2)

theorem evalsU_bitAtE {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (i : ℕ) :
    EvalsU S (bitAtE ds i) (fun env => bitAt (dv env) i) := by
  refine (EvalsU.mod (EvalsU.shiftR (h.getD (i / W)) (EvalsU.uc (i % W) (mod_W_lt_pow i))
    (fun _ => by rw [W]; omega)) (EvalsU.uc 2 (by norm_num))).congr fun env => ?_
  rw [bitAt, digitAt]

/-- A digit list shifted right by `lo` bits and cut to `len` digits, as pure
expressions: every digit is a bit-sum of bit reads, so this costs no steps at all.
With `lo = 0` it is a *resize* (`resizeDigits`), which is how every program's result is
brought back to the canonical `ofNat v len` shape the next program wants. -/
def shiftDigits (ds : List (U64Expr K)) (lo len : ℕ) : List (U64Expr K) :=
  ofFnDigits (fun k => bitsToDigit (bitAtE ds) (lo + W * k) W) len

omit [FiniteField K] in
@[simp] theorem length_shiftDigits (ds : List (U64Expr K)) (lo len : ℕ) :
    (shiftDigits ds lo len).length = len := by simp [shiftDigits]

theorem evalsBig_shiftDigits {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (lo len : ℕ) :
    EvalsBig S (shiftDigits ds lo len) (fun env => ofNat (lval (dv env) / 2 ^ lo) len) := by
  refine evalsBig_ofFnDigits (fun _ => length_ofNat _ _) (fun _ => bounded_ofNat _ _)
    fun k hk => ?_
  refine (evalsU_bitsToDigit (f := bitAtE ds) (g := fun env j => lval (dv env) / 2 ^ j % 2)
    (fun j => (evalsU_bitAtE h j).congr fun env => lval_bitAt _ (h.bounded env) j)
    (fun _ _ => Nat.mod_lt _ (by norm_num)) W (lo + W * k) (by rw [W]; omega)).congr fun env => ?_
  rw [bitWindow_bits, getD_ofNat _ _ _ hk, base_pow, base, pow_add, ← Nat.div_div_eq_div_mul]

/-- Cut a digit list to `len` digits without shifting: the canonical form. -/
def resizeDigits (ds : List (U64Expr K)) (len : ℕ) : List (U64Expr K) := shiftDigits ds 0 len

omit [FiniteField K] in
@[simp] theorem length_resizeDigits (ds : List (U64Expr K)) (len : ℕ) :
    (resizeDigits ds len).length = len := by simp [resizeDigits]

theorem evalsBig_resizeDigits {S : Array (Step K)} {ds : List (U64Expr K)} {dv}
    (h : EvalsBig S ds dv) (len : ℕ) :
    EvalsBig S (resizeDigits ds len) (fun env => ofNat (lval (dv env)) len) :=
  (evalsBig_shiftDigits h 0 len).congr fun env => by rw [pow_zero, Nat.div_one]

/-- One `B`-bit limb of a digit list, as a field expression. A limb does not fit a u64
once `B` exceeds 64 (an RSA limb is 121 bits), so it is assembled from `W`-bit chunks and
the chunks are combined *in the field*, where `2^W` is just a constant. -/
def limbFChunks (ds : List (U64Expr K)) (lo B : ℕ) : ℕ → FExpr K
  | 0 => .const 0
  | c + 1 => .add (.ofU64 (bitsToDigit (bitAtE ds) lo (min W B)))
      (.mul (.const (FiniteField.fromNat (2 ^ W))) (limbFChunks ds (lo + W) (B - W) c))

@[inherit_doc limbFChunks]
def limbF (ds : List (U64Expr K)) (lo B : ℕ) : FExpr K := limbFChunks ds lo B (numChunks B)

section Prime
variable {p : ℕ} [Fact p.Prime]

theorem evalsF_limbFChunks {S : Array (Step (F p))} {ds : List (U64Expr (F p))} {dv}
    (h : EvalsBig S ds dv) :
    ∀ (c lo B : ℕ), EvalsF S (limbFChunks ds lo B c)
      (fun env => ((winChunks (lval (dv env)) lo B c : ℕ) : F p)) := by
  intro c
  induction c with
  | zero =>
    intro lo B
    exact (EvalsF.const 0).congr fun env => by simp [winChunks]
  | succ c ih =>
    intro lo B
    have hpiece : EvalsU S (bitsToDigit (bitAtE ds) lo (min W B))
        (fun env => lval (dv env) / 2 ^ lo % 2 ^ min W B) :=
      (evalsU_bitsToDigit (f := bitAtE ds) (g := fun env j => lval (dv env) / 2 ^ j % 2)
        (fun j => (evalsU_bitAtE h j).congr fun env => lval_bitAt _ (h.bounded env) j)
        (fun _ _ => Nat.mod_lt _ (by norm_num)) (min W B) lo
        (le_trans (min_le_left _ _) (by rw [W]; omega))).congr
        fun env => bitWindow_bits _ _ _
    refine (EvalsF.add (EvalsF.ofU64 hpiece)
      (EvalsF.mul (EvalsF.const _) (ih (lo + W) (B - W)))).congr fun env => ?_
    simp only [FiniteField.fromNat_F, winChunks]
    push_cast
    ring

/-- `evalsBig_readBitsAt` on a prime field, spelled with `ZMod.val`: this is the shape a
gadget's `h_env` hypotheses come in, `FiniteField.val` on `F p` being `ZMod.val`. -/
theorem evalsBig_readBitsAt_F {S : Array (Step (F p))} (e : Expression (F p)) (off nbits : ℕ) :
    EvalsBig S (readBitsAt e off nbits)
      (fun env => ofNat ((Expression.eval env.toEnvironment e).val % 2 ^ nbits * 2 ^ off)
        (numChunks (off + nbits))) :=
  evalsBig_readBitsAt e off nbits

/-- The limb a `limbF` expression reads: bits `[lo, lo + B)` of the value the digits
denote. No bound on `B` relative to `p` is needed: every chunk is cast into the field
separately and the chunks are recombined there, so the identity is the ℕ one. -/
theorem evalsF_limbF {S : Array (Step (F p))} {ds : List (U64Expr (F p))} {dv}
    (h : EvalsBig S ds dv) (lo B : ℕ) :
    EvalsF S (limbF ds lo B) (fun env => ((lval (dv env) / 2 ^ lo % 2 ^ B : ℕ) : F p)) :=
  (evalsF_limbFChunks h (numChunks B) lo B).congr fun env => by
    rw [winChunks_eq _ _ _ _ (le_numChunks B)]

end Prime

/-! ## Digit programs

Each program is a `Witgen.M` computation that appends `letU` steps and returns the digit
expressions, and each is proved against the corresponding `WitgenNat` function. Three
rules shape them, all of them costs paid once here rather than in every gadget:

* every intermediate value that is used more than once is bound by a `letU`, so a
  program's *term* size is linear in its step count (an unbound carry would be
  duplicated by the next step's comparison, doubling the term per digit);
* carries and borrows are comparisons (`BExpr.lt`), never a division by the base;
* digits leave through `.mod`, because the u64 sort has no subtraction. -/

/-- The digit base, as a u64 constant. -/
def baseE : U64Expr K := uc base

theorem evalsU_baseE {S : Array (Step K)} : EvalsU S (baseE : U64Expr K) (fun _ => base) :=
  EvalsU.uc base base_lt

/-- The carry out of one addition step: two comparisons. -/
def addCarryE (s : U64Expr K) : U64Expr K :=
  .ite (.lt s baseE) (uc 0) (.ite (.lt s (uc (2 * base))) (uc 1) (uc 2))

theorem evalsU_addCarryE {S : Array (Step K)} {s : U64Expr K} {sv} (hs : EvalsU S s sv) :
    EvalsU S (addCarryE s) (fun env => addCarry (sv env)) :=
  (EvalsU.iteLt hs evalsU_baseE (EvalsU.uc 0 (by norm_num))
    (EvalsU.iteLt hs (EvalsU.uc (2 * base) two_base_lt) (EvalsU.uc 1 (by norm_num))
      (EvalsU.uc 2 (by norm_num)))).congr fun env => by rw [addCarry]

/-- The digit of an addition step, prefixed onto the digits the rest of the pass
produced. Shared by the four cases of `addP`. -/
private theorem addP_cons {S : Array (Step K)} {s : U64Expr K} {sv}
    {rest : List (U64Expr K)} {rv}
    (hs : EvalsU S s sv) (hb : ∀ env, sv env < 3 * base) (hrest : EvalsBig S rest rv) :
    EvalsBig S (.mod s baseE :: rest) (fun env => addDigit (sv env) :: rv env) :=
  EvalsBig.cons ((EvalsU.mod hs evalsU_baseE).congr fun env => (addDigit_eq_mod (hb env)).symm)
    (fun env => addDigit_lt (hb env)) hrest

/-- Add two digit lists with an incoming carry. The result is one digit longer than the
longer operand, so nothing is ever lost off the top. -/
def addP : List (U64Expr K) → List (U64Expr K) → U64Expr K → M K (List (U64Expr K))
  | [], [], c => Pure.pure [c]
  | [], y :: ys, c => do
      let s ← letU (.add y c)
      let c' ← letU (addCarryE s)
      let rest ← addP [] ys c'
      Pure.pure (.mod s baseE :: rest)
  | x :: xs, [], c => do
      let s ← letU (.add x c)
      let c' ← letU (addCarryE s)
      let rest ← addP xs [] c'
      Pure.pure (.mod s baseE :: rest)
  | x :: xs, y :: ys, c => do
      let s ← letU (.add (.add x y) c)
      let c' ← letU (addCarryE s)
      let rest ← addP xs ys c'
      Pure.pure (.mod s baseE :: rest)

theorem computesBig_addP (a : List (U64Expr K)) :
    ∀ (b : List (U64Expr K)) {S : Array (Step K)} (c : U64Expr K) {av bv cv},
      EvalsBig S a av → EvalsBig S b bv → EvalsU S c cv → (∀ env, cv env < base) →
      ComputesBig S (addP a b c) (fun env => addc (av env) (bv env) (cv env)) := by
  induction a with
  | nil =>
    intro b
    induction b with
    | nil =>
      intro S c av bv cv ha hb hc hcb
      rw [addP]
      refine Computes.pure ((EvalsBig.cons hc hcb EvalsBig.nil).congr fun env => ?_)
      rw [ha.eq_nil env, hb.eq_nil env, addc]
    | cons y ys ihb =>
      intro S c av bv cv ha hb hc hcb
      rw [addP]
      have hyh := hb.head
      have hbnd : ∀ env, (bv env).headD 0 + cv env < 3 * base := fun env => by
        have := hb.headD_lt env; have := hcb env; have := base_pos; omega
      refine Computes.bind (ComputesU.letU (EvalsU.add hyh hc
        (fun env => by have := hbnd env; have := three_base_lt; omega))) ?_
      intro S1 s hS1 hs
      refine Computes.bind (ComputesU.letU (evalsU_addCarryE hs)) ?_
      intro S2 c' hS2 hc'
      refine Computes.bind (ihb c' (ha.mono (hS1.trans hS2)) (hb.tail.mono (hS1.trans hS2)) hc'
        (fun env => addCarry_lt)) ?_
      intro S3 rest hS3 hrest
      refine Computes.pure ((addP_cons (hs.mono (hS2.trans hS3))
        (fun env => hbnd env) hrest).congr fun env => ?_)
      conv_rhs => rw [ha.eq_nil env, hb.cons_eq env]
      rw [addc, ha.eq_nil env]
  | cons x xs iha =>
    intro b
    cases b with
    | nil =>
      intro S c av bv cv ha hb hc hcb
      rw [addP]
      have hxh := ha.head
      have hbnd : ∀ env, (av env).headD 0 + cv env < 3 * base := fun env => by
        have := ha.headD_lt env; have := hcb env; have := base_pos; omega
      refine Computes.bind (ComputesU.letU (EvalsU.add hxh hc
        (fun env => by have := hbnd env; have := three_base_lt; omega))) ?_
      intro S1 s hS1 hs
      refine Computes.bind (ComputesU.letU (evalsU_addCarryE hs)) ?_
      intro S2 c' hS2 hc'
      refine Computes.bind (iha [] c' (ha.tail.mono (hS1.trans hS2)) (hb.mono (hS1.trans hS2)) hc'
        (fun env => addCarry_lt)) ?_
      intro S3 rest hS3 hrest
      refine Computes.pure ((addP_cons (hs.mono (hS2.trans hS3))
        (fun env => hbnd env) hrest).congr fun env => ?_)
      conv_rhs => rw [ha.cons_eq env, hb.eq_nil env]
      rw [addc, hb.eq_nil env]
    | cons y ys =>
      intro S c av bv cv ha hb hc hcb
      rw [addP]
      have hxh := ha.head
      have hyh := hb.head
      have hbnd : ∀ env, (av env).headD 0 + (bv env).headD 0 + cv env < 3 * base := fun env => by
        have := ha.headD_lt env; have := hb.headD_lt env; have := hcb env; omega
      refine Computes.bind (ComputesU.letU (EvalsU.add (EvalsU.add hxh hyh
        (fun env => by have := ha.headD_lt env; have := hb.headD_lt env
                       have := three_base_lt; omega)) hc
        (fun env => by have := hbnd env; have := three_base_lt; omega))) ?_
      intro S1 s hS1 hs
      refine Computes.bind (ComputesU.letU (evalsU_addCarryE hs)) ?_
      intro S2 c' hS2 hc'
      refine Computes.bind (iha ys c' (ha.tail.mono (hS1.trans hS2))
        (hb.tail.mono (hS1.trans hS2)) hc' (fun env => addCarry_lt)) ?_
      intro S3 rest hS3 hrest
      refine Computes.pure ((addP_cons (hs.mono (hS2.trans hS3))
        (fun env => hbnd env) hrest).congr fun env => ?_)
      conv_rhs => rw [ha.cons_eq env, hb.cons_eq env]
      rw [addc]

/-- Shift a digit list left by one bit, with `c` shifted in at the bottom. The digit
falling off the top is dropped, exactly as `WitgenNat.shl1` does. -/
def shl1P : List (U64Expr K) → U64Expr K → M K (List (U64Expr K))
  | [], _ => Pure.pure []
  | d :: ds, c => do
      let s ← letU (.add (.mul d (uc 2)) c)
      let c' ← letU (.ite (.lt s baseE) (uc 0) (uc 1))
      let rest ← shl1P ds c'
      Pure.pure (.mod s baseE :: rest)

theorem computesBig_shl1P (ds : List (U64Expr K)) :
    ∀ {S : Array (Step K)} (c : U64Expr K) {dv cv}, EvalsBig S ds dv → EvalsU S c cv →
      (∀ env, cv env < 2) →
      ComputesBig S (shl1P ds c) (fun env => shl1 (dv env) (cv env)) := by
  induction ds with
  | nil =>
    intro S c dv cv hd hc hcb
    exact Computes.pure (EvalsBig.nil.congr fun env => by rw [hd.eq_nil env, shl1])
  | cons d ds ih =>
    intro S c dv cv hd hc hcb
    have hbnd : ∀ env, 2 * (dv env).headD 0 + cv env < 2 * base := fun env => by
      have := hd.headD_lt env; have := hcb env; omega
    have hs0 : EvalsU S (.add (.mul d (uc 2)) c)
        (fun env => 2 * (dv env).headD 0 + cv env) :=
      (EvalsU.add (EvalsU.mul hd.head (EvalsU.uc 2 (by norm_num))
        (fun env => by have := hd.headD_lt env; have := two_base_lt; omega)) hc
        (fun env => by have := hbnd env; have := two_base_lt; omega)).congr
        fun env => by ring
    refine Computes.bind (ComputesU.letU hs0) ?_
    intro S1 s hS1 hs
    refine Computes.bind (ComputesU.letU (EvalsU.iteLt hs evalsU_baseE
      (EvalsU.uc 0 (by norm_num)) (EvalsU.uc 1 (by norm_num)))) ?_
    intro S2 c' hS2 hc'
    replace hc' : EvalsU S2 c' (fun env => dblCarry (2 * (dv env).headD 0 + cv env)) :=
      hc'.congr fun env => by rw [dblCarry]
    refine Computes.bind (ih c' (hd.tail.mono (hS1.trans hS2)) hc'
      (fun env => dblCarry_lt_two)) ?_
    intro S3 rest hS3 hrest
    refine Computes.pure ((EvalsBig.cons
      ((EvalsU.mod (hs.mono (hS2.trans hS3)) evalsU_baseE).congr
        fun env => (dblDigit_eq_mod (hbnd env)).symm)
      (fun env => dblDigit_lt (hbnd env)) hrest).congr fun env => ?_)
    conv_rhs => rw [hd.cons_eq env]
    rw [shl1]

/-- `b · x + c`, one pass over `b`'s digits. The carry here really is a division by the
base; that is harmless, because the pathological shape is `(x + base) / base`, whose
guard reduces structurally over the literal. -/
def mulAddP : List (U64Expr K) → U64Expr K → U64Expr K → M K (List (U64Expr K))
  | [], _, c => Pure.pure [c]
  | y :: ys, x, c => do
      let s ← letU (.add (.mul y x) c)
      let c' ← letU (.div s baseE)
      let rest ← mulAddP ys x c'
      Pure.pure (.mod s baseE :: rest)

theorem computesBig_mulAddP (b : List (U64Expr K)) :
    ∀ {S : Array (Step K)} (x c : U64Expr K) {bv xv cv}, EvalsBig S b bv → EvalsU S x xv →
      EvalsU S c cv → (∀ env, xv env < base) → (∀ env, cv env < base) →
      ComputesBig S (mulAddP b x c) (fun env => mulAdd (bv env) (xv env) (cv env)) := by
  induction b with
  | nil =>
    intro S x c bv xv cv hb hx hc hxb hcb
    refine Computes.pure ((EvalsBig.cons hc hcb EvalsBig.nil).congr fun env => ?_)
    rw [hb.eq_nil env, mulAdd]
  | cons y ys ih =>
    intro S x c bv xv cv hb hx hc hxb hcb
    have hbnd : ∀ env, (bv env).headD 0 * xv env + cv env < 2 ^ 64 := fun env =>
      digit_mul_add_lt (hb.headD_lt env) (hxb env) (hcb env)
    have hcarry : ∀ env, ((bv env).headD 0 * xv env + cv env) / base < base := fun env =>
      (Nat.div_lt_iff_lt_mul base_pos).mpr (by have := hbnd env; rw [base_mul_base]; omega)
    refine Computes.bind (ComputesU.letU (EvalsU.add
      (EvalsU.mul hb.head hx (fun env => by have := hbnd env; omega)) hc hbnd)) ?_
    intro S1 s hS1 hs
    refine Computes.bind (ComputesU.letU (EvalsU.div hs evalsU_baseE)) ?_
    intro S2 c' hS2 hc'
    refine Computes.bind (ih x c' (hb.tail.mono (hS1.trans hS2)) (hx.mono (hS1.trans hS2)) hc'
      (fun env => hxb env) hcarry) ?_
    intro S3 rest hS3 hrest
    refine Computes.pure ((EvalsBig.cons
      (EvalsU.mod (hs.mono (hS2.trans hS3)) evalsU_baseE)
      (fun _ => Nat.mod_lt _ base_pos) hrest).congr fun env => ?_)
    conv_rhs => rw [hb.cons_eq env]
    rw [mulAdd]

/-- Schoolbook multiplication: one `mulAddP` pass per digit of the left operand. -/
def mulP : List (U64Expr K) → List (U64Expr K) → M K (List (U64Expr K))
  | [], _ => Pure.pure []
  | x :: xs, b => do
      let pr ← mulAddP b x (uc 0)
      let rest ← mulP xs b
      addP pr (uc 0 :: rest) (uc 0)

theorem computesBig_mulP (a : List (U64Expr K)) :
    ∀ {S : Array (Step K)} (b : List (U64Expr K)) {av bv}, EvalsBig S a av →
      EvalsBig S b bv → ComputesBig S (mulP a b) (fun env => mul (av env) (bv env)) := by
  induction a with
  | nil =>
    intro S b av bv ha hb
    exact Computes.pure (EvalsBig.nil.congr fun env => by rw [ha.eq_nil env, mul])
  | cons x xs ih =>
    intro S b av bv ha hb
    refine Computes.bind (computesBig_mulAddP b x (uc 0) hb ha.head (EvalsU.uc 0 (by norm_num))
      (fun env => ha.headD_lt env) (fun _ => base_pos)) ?_
    intro S1 pr hS1 hpr
    refine Computes.bind (ih b (ha.tail.mono hS1) (hb.mono hS1)) ?_
    intro S2 rest hS2 hrest
    refine (computesBig_addP pr (uc 0 :: rest) (uc 0) (hpr.mono hS2)
      (EvalsBig.cons (EvalsU.uc 0 (by norm_num)) (fun _ => base_pos) hrest)
      (EvalsU.uc 0 (by norm_num)) (fun _ => base_pos)).congr fun env => ?_
    conv_rhs => rw [ha.cons_eq env]
    rw [mul]

/-! ### Subtraction, which also answers the comparison

`subbOut` is `1` exactly when what was subtracted exceeded the minuend, so the borrow
out of a pass *is* the comparison: the division loop needs no separate one. -/

/-- Digits plus the borrow they produced. Digits and borrow-out are separate `WitgenNat`
functions (a pair-valued recursive definition duplicates the recursive call in its
equation lemma), so the pair predicate pairs two separate ℕ functions. -/
def EvalsBigU (S : Array (Step K)) (r : List (U64Expr K) × U64Expr K)
    (v : ProverEnvironment K → List ℕ × ℕ) : Prop :=
  EvalsBig S r.1 (fun env => (v env).1) ∧ EvalsU S r.2 (fun env => (v env).2)

@[inherit_doc Computes]
abbrev ComputesBigU (S : Array (Step K)) (p : M K (List (U64Expr K) × U64Expr K))
    (v : ProverEnvironment K → List ℕ × ℕ) : Prop := Computes EvalsBigU S p v

theorem EvalsBigU.congr {S : Array (Step K)} {r : List (U64Expr K) × U64Expr K} {v v'}
    (h : EvalsBigU S r v) (hv : ∀ env, v env = v' env) : EvalsBigU S r v' :=
  ⟨h.1.congr fun env => by rw [hv env], h.2.congr fun env => by rw [hv env]⟩

theorem ComputesBigU.congr {S : Array (Step K)} {p : M K (List (U64Expr K) × U64Expr K)} {v v'}
    (h : ComputesBigU S p v) (hv : ∀ env, v env = v' env) : ComputesBigU S p v' :=
  ⟨h.1, h.2.congr hv⟩

/-- Subtract `ys` from `xs` with an incoming borrow, returning the digits and the borrow
out. The subtrahend is read through `headD`/`tail`, so a shorter one is zero-padded. -/
def subP : List (U64Expr K) → List (U64Expr K) → U64Expr K →
    M K (List (U64Expr K) × U64Expr K)
  | [], _, b => Pure.pure ([], b)
  | x :: xs, ys, b => do
      let yb ← letU (.add (ys.headD (uc 0)) b)
      let b' ← letU (.ite (.lt x yb) (uc 1) (uc 0))
      let d ← letU (.mod (usub (.add x baseE) yb) baseE)
      let r ← subP xs ys.tail b'
      Pure.pure (d :: r.1, r.2)

theorem computesBigU_subP (xs : List (U64Expr K)) :
    ∀ {S : Array (Step K)} (ys : List (U64Expr K)) (b : U64Expr K) {xv yv bv},
      EvalsBig S xs xv → EvalsBig S ys yv → EvalsU S b bv → (∀ env, bv env < 2) →
      ComputesBigU S (subP xs ys b)
        (fun env => (subb (xv env) (yv env) (bv env),
          subbOut (xv env) (yv env) (bv env))) := by
  induction xs with
  | nil =>
    intro S ys b xv yv bv hx hy hb hbb
    rw [subP]
    refine Computes.pure ⟨EvalsBig.nil.congr fun env => ?_, hb.congr fun env => ?_⟩
    · show [] = subb (xv env) (yv env) (bv env)
      rw [hx.eq_nil env, subb]
    · show bv env = subbOut (xv env) (yv env) (bv env)
      rw [hx.eq_nil env, subbOut]
  | cons x xs ih =>
    intro S ys b xv yv bv hx hy hb hbb
    have hyhb : ∀ env, (yv env).headD 0 < base := fun env => hy.headD_lt env
    have hxhb : ∀ env, (xv env).headD 0 < base := fun env => hx.headD_lt env
    -- the subtrahend digit plus the incoming borrow, bound once and used three times
    refine Computes.bind (ComputesU.letU (EvalsU.add hy.headD hb
      (fun env => by have := hyhb env; have := hbb env; have := two_base_lt; omega))) ?_
    intro S1 yb hS1 hyb
    refine Computes.bind (ComputesU.letU (EvalsU.iteLt (hx.head.mono hS1) hyb
      (EvalsU.uc 1 (by norm_num)) (EvalsU.uc 0 (by norm_num)))) ?_
    intro S2 b' hS2 hb'
    replace hb' : EvalsU S2 b'
        (fun env => subBorrow ((xv env).headD 0) ((yv env).headD 0) (bv env)) :=
      hb'.congr fun env => by rw [subBorrow]; split_ifs <;> omega
    have hxb : EvalsU S2 (.add x baseE) (fun env => (xv env).headD 0 + base) :=
      EvalsU.add (hx.head.mono (hS1.trans hS2)) evalsU_baseE
        (fun env => by have := hxhb env; have := two_base_lt; omega)
    have hdig : EvalsU S2 (.mod (usub (.add x baseE) yb) baseE)
        (fun env => subDigit ((xv env).headD 0) ((yv env).headD 0) (bv env)) :=
      (EvalsU.mod (EvalsU.usub hxb (hyb.mono hS2)
        (fun env => by have := hxhb env; have := hyhb env; have := hbb env; omega))
        evalsU_baseE).congr fun env => by
          rw [subDigit_eq_mod (hxhb env) (hyhb env) (hbb env)]
          congr 1
          omega
    refine Computes.bind (ComputesU.letU hdig) ?_
    intro S3 d hS3 hd
    refine Computes.bind (ih ys.tail b' (hx.tail.mono ((hS1.trans hS2).trans hS3))
      (hy.tail'.mono ((hS1.trans hS2).trans hS3)) (hb'.mono hS3)
      (fun env => subBorrow_lt _ _ _)) ?_
    intro S4 r hS4 hr
    refine Computes.pure (EvalsBigU.congr (v := fun env =>
        (subDigit ((xv env).headD 0) ((yv env).headD 0) (bv env) :: (
          subb ((xv env).tail) ((yv env).tail)
            (subBorrow ((xv env).headD 0) ((yv env).headD 0) (bv env))),
         subbOut ((xv env).tail) ((yv env).tail)
            (subBorrow ((xv env).headD 0) ((yv env).headD 0) (bv env))))
      ⟨EvalsBig.cons (hd.mono hS4)
        (fun env => subDigit_lt (hxhb env) (hyhb env) (hbb env)) hr.1, hr.2⟩ fun env => ?_)
    conv_rhs => rw [hx.cons_eq env]
    rw [subb, subbOut]

/-- Select between two digit lists of the same length: `a` when `c` is nonzero, `b`
otherwise. -/
def selectP (c : U64Expr K) : List (U64Expr K) → List (U64Expr K) → M K (List (U64Expr K))
  | [], _ => Pure.pure []
  | _, [] => Pure.pure []
  | a :: as, b :: bs => do
      let d ← letU (.ite (.neq c (uc 0)) b a)
      let rest ← selectP c as bs
      Pure.pure (d :: rest)

theorem computesBig_selectP (a : List (U64Expr K)) :
    ∀ {S : Array (Step K)} (c : U64Expr K) (b : List (U64Expr K)) {av bv cv},
      EvalsBig S a av → EvalsBig S b bv → EvalsU S c cv → a.length = b.length →
      ComputesBig S (selectP c a b) (fun env => if cv env = 0 then bv env else av env) := by
  induction a with
  | nil =>
    intro S c b av bv cv ha hb hc hlen
    have hbnil : b = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst hbnil
    exact Computes.pure (EvalsBig.nil.congr fun env => by
      rw [ha.eq_nil env, hb.eq_nil env]; split <;> rfl)
  | cons x xs ih =>
    intro S c b av bv cv ha hb hc hlen
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      refine Computes.bind (ComputesU.letU
        (EvalsU.iteEq hc (EvalsU.uc 0 (by norm_num)) hb.head ha.head)) ?_
      intro S1 d hS1 hd
      refine Computes.bind (ih c ys (ha.tail.mono hS1) (hb.tail.mono hS1) (hc.mono hS1)
        (by simpa using hlen)) ?_
      intro S2 rest hS2 hrest
      refine Computes.pure ((EvalsBig.cons (hd.mono hS2)
        (fun env => by
          by_cases hz : cv env = 0
          · rw [if_pos hz]; exact hb.headD_lt env
          · rw [if_neg hz]; exact ha.headD_lt env) hrest).congr fun env => ?_)
      conv_rhs => rw [ha.cons_eq env, hb.cons_eq env]
      split <;> rfl

/-! ## The division loop -/

/-- Two digit lists at once: the quotient and remainder registers. -/
def EvalsPair (S : Array (Step K)) (st : List (U64Expr K) × List (U64Expr K))
    (v : ProverEnvironment K → List ℕ × List ℕ) : Prop :=
  EvalsBig S st.1 (fun env => (v env).1) ∧ EvalsBig S st.2 (fun env => (v env).2)

@[inherit_doc Computes]
abbrev ComputesPair (S : Array (Step K)) (p : M K (List (U64Expr K) × List (U64Expr K)))
    (v : ProverEnvironment K → List ℕ × List ℕ) : Prop := Computes EvalsPair S p v

theorem EvalsPair.congr {S : Array (Step K)} {st : List (U64Expr K) × List (U64Expr K)} {v v'}
    (h : EvalsPair S st v) (hv : ∀ env, v env = v' env) : EvalsPair S st v' :=
  ⟨h.1.congr fun env => by rw [hv env], h.2.congr fun env => by rw [hv env]⟩

theorem ComputesPair.congr {S : Array (Step K)}
    {p : M K (List (U64Expr K) × List (U64Expr K))} {v v'}
    (h : ComputesPair S p v) (hv : ∀ env, v env = v' env) : ComputesPair S p v' :=
  ⟨h.1, h.2.congr hv⟩

/-- One step of binary long division. -/
def divStepP (n : List (U64Expr K)) (bit : U64Expr K) (q r : List (U64Expr K)) :
    M K (List (U64Expr K) × List (U64Expr K)) := do
  let r' ← shl1P r bit
  let db ← subP r' n (uc 0)
  let qbit ← letU (.ite (.neq db.2 (uc 0)) (uc 1) (uc 0))
  let q' ← shl1P q qbit
  let r'' ← selectP db.2 r' db.1
  Pure.pure (q', r'')

theorem computesPair_divStepP (n : List (U64Expr K)) {S : Array (Step K)}
    {bit : U64Expr K} {q r : List (U64Expr K)} {nv qv rv bitv}
    (hn : EvalsBig S n nv) (hq : EvalsBig S q qv) (hr : EvalsBig S r rv)
    (hbit : EvalsU S bit bitv) (hb2 : ∀ env, bitv env < 2) :
    ComputesPair S (divStepP n bit q r)
      (fun env => divStep (nv env) (bitv env) (qv env, rv env)) := by
  refine Computes.bind (computesBig_shl1P r bit hr hbit hb2) ?_
  intro S1 r' hS1 hr'
  refine Computes.bind (computesBigU_subP r' n (uc 0) hr' (hn.mono hS1)
    (EvalsU.uc 0 (by norm_num)) (fun _ => by norm_num)) ?_
  intro S2 db hS2 hdb
  have hd1 : EvalsBig S2 db.1
      (fun env => subb (shl1 (rv env) (bitv env)) (nv env) 0) := hdb.1
  have hd2 : EvalsU S2 db.2
      (fun env => subbOut (shl1 (rv env) (bitv env)) (nv env) 0) := hdb.2
  refine Computes.bind (ComputesU.letU (EvalsU.iteEq hd2 (EvalsU.uc 0 (by norm_num))
    (EvalsU.uc 1 (by norm_num)) (EvalsU.uc 0 (by norm_num)))) ?_
  intro S3 qbit hS3 hqbit
  refine Computes.bind (computesBig_shl1P q qbit (hq.mono ((hS1.trans hS2).trans hS3)) hqbit
    (fun env => by split <;> norm_num)) ?_
  intro S4 q' hS4 hq'
  refine Computes.bind (computesBig_selectP r' (db.2) db.1
    (hr'.mono ((hS2.trans hS3).trans hS4)) (hd1.mono (hS3.trans hS4))
    (hd2.mono (hS3.trans hS4))
    (hr'.length_expr hd1 fun env => (length_subb _ _ _).symm)) ?_
  intro S5 r'' hS5 hr''
  refine Computes.pure (EvalsPair.congr (v := fun env =>
      (shl1 (qv env) (if subbOut (shl1 (rv env) (bitv env)) (nv env) 0 = 0 then 1 else 0),
        if subbOut (shl1 (rv env) (bitv env)) (nv env) 0 = 0
          then subb (shl1 (rv env) (bitv env)) (nv env) 0
          else shl1 (rv env) (bitv env)))
    ⟨hq'.mono hS5, hr''⟩ fun env => ?_)
  rw [divStep]
  split_ifs <;> rfl


/-- The division loop: `j` steps, consuming the dividend's top `j` bits. Structural in
the step count (never in a list index), exactly as `WitgenNat.divIter`. -/
def divIterP (n x : List (U64Expr K)) (bits : ℕ) (q r : List (U64Expr K)) :
    ℕ → M K (List (U64Expr K) × List (U64Expr K))
  | 0 => Pure.pure (q, r)
  | j + 1 => do
      let st ← divIterP n x bits q r j
      divStepP n (bitAtE x (bits - 1 - j)) st.1 st.2

theorem computesPair_divIterP (n x : List (U64Expr K)) (bits : ℕ) :
    ∀ (j : ℕ) {S : Array (Step K)} {q r : List (U64Expr K)} {nv xv qv rv},
      EvalsBig S n nv → EvalsBig S x xv → EvalsBig S q qv → EvalsBig S r rv →
      ComputesPair S (divIterP n x bits q r j)
        (fun env => divIter (nv env) (xv env) bits (qv env) (rv env) j) := by
  intro j
  induction j with
  | zero => intro S q r nv xv qv rv _ _ hq hr; exact Computes.pure ⟨hq, hr⟩
  | succ j ih =>
    intro S q r nv xv qv rv hn hx hq hr
    refine Computes.bind (ih hn hx hq hr) ?_
    intro S1 st hS1 hst
    exact ComputesPair.congr
      (computesPair_divStepP n (hn.mono hS1) hst.1 hst.2
        (evalsU_bitAtE (hx.mono hS1) (bits - 1 - j)) (fun env => bitAt_lt_two _ _))
      fun env => by rw [divIter, Prod.mk.eta]

/-- Quotient and remainder as digit lists: the loop run to completion, both registers
starting at zero. -/
def divmodP (n x : List (U64Expr K)) (qlen rlen bits : ℕ) :
    M K (List (U64Expr K) × List (U64Expr K)) :=
  divIterP n x bits (constDigits 0 qlen) (constDigits 0 rlen) bits

/-- Unconditional: `WitgenNat.divmod` is total, and the arithmetic meaning (that the
registers really hold `x / n` and `x % n`) is `divmod_spec`, applied at the use site. -/
theorem computesPair_divmodP (n x : List (U64Expr K)) (qlen rlen bits : ℕ)
    {S : Array (Step K)} {nv xv} (hn : EvalsBig S n nv) (hx : EvalsBig S x xv) :
    ComputesPair S (divmodP n x qlen rlen bits)
      (fun env => divmod (nv env) (xv env) qlen rlen bits) :=
  ComputesPair.congr
    (computesPair_divIterP n x bits bits hn hx
      (evalsBig_constDigits 0 qlen) (evalsBig_constDigits 0 rlen))
    fun env => by rw [divmod, ofNat_zero, ofNat_zero]

/-! ## Modular multiplication -/

/-- A value below the modulus is carried faithfully by an `rlen`-digit register. This is
exactly what the `n.length < rlen` hypothesis buys, and it is how a caller turns the
canonical `ofNat` form every program below returns back into a plain `lval` equation. -/
theorem lval_ofNat_lt_modulus {S : Array (Step K)} {n : List (U64Expr K)} {nv}
    (hn : EvalsBig S n nv) {rlen : ℕ} (hnlen : n.length < rlen)
    {v : ℕ} {env : ProverEnvironment K} (hv : v < lval (nv env)) :
    lval (ofNat v rlen) = v := by
  have h1 : lval (nv env) < base ^ n.length := by
    have := lval_lt (hn.bounded env); rwa [hn.length_eq env] at this
  have h2 : base ^ n.length ≤ base ^ rlen := Nat.pow_le_pow_right base_pos (by omega)
  exact lval_ofNat_of_lt (by omega)


/-- `a * b % n`: multiply, divide, keep the remainder register. -/
def mulModP (n a b : List (U64Expr K)) (qlen rlen bits : ℕ) : M K (List (U64Expr K)) := do
  let pr ← mulP a b
  let qr ← divmodP n pr qlen rlen bits
  Pure.pure qr.2

/-- The remainder register is `Bounded` and `rlen` digits wide, so by `eq_ofNat` it *is*
the canonical digit list of `a * b % n`. Stating the result in that form is what lets
one `mulModP` feed the next. -/
theorem computesBig_mulModP (n a b : List (U64Expr K)) (qlen rlen bits : ℕ)
    {S : Array (Step K)} {nv av bv}
    (hn : EvalsBig S n nv) (ha : EvalsBig S a av) (hb : EvalsBig S b bv)
    (hnpos : ∀ env, 0 < lval (nv env)) (hnlen : n.length < rlen)
    (hab : ∀ env, lval (av env) * lval (bv env) < 2 ^ bits)
    (hqbig : 2 ^ bits ≤ base ^ qlen) :
    ComputesBig S (mulModP n a b qlen rlen bits)
      (fun env => ofNat (lval (av env) * lval (bv env) % lval (nv env)) rlen) := by
  refine Computes.bind (computesBig_mulP a b ha hb) ?_
  intro S1 pr hS1 hpr
  refine Computes.bind (computesPair_divmodP n pr qlen rlen bits (hn.mono hS1) hpr) ?_
  intro S2 qr hS2 hqr
  refine Computes.pure (hqr.2.congr fun env => ?_)
  have hnl : (nv env).length = n.length := hn.length_eq env
  obtain ⟨-, h2, -, h4, -, h6⟩ :=
    divmod_spec (nv env) (mul (av env) (bv env)) bits qlen rlen (hn.bounded env)
      (bounded_mul _ _ (ha.bounded env) (hb.bounded env)) (hnpos env) (by omega)
      (by rw [lval_mul]; exact hab env) hqbig
  rw [eq_ofNat h2, h4, h6, lval_mul]

/-- The arithmetic reading of `computesBig_mulModP`: the register the program leaves
really denotes `a * b % n`. The `Bounded` and length facts come for free out of
`EvalsBig` (`bounded_ofNat`, `length_ofNat`). -/
theorem lval_mulModP {S : Array (Step K)} {n : List (U64Expr K)} {nv}
    (hn : EvalsBig S n nv) {rlen : ℕ} (hnlen : n.length < rlen)
    (hnpos : ∀ env, 0 < lval (nv env)) (a b : ℕ) (env : ProverEnvironment K) :
    lval (ofNat (a * b % lval (nv env)) rlen) = a * b % lval (nv env) :=
  lval_ofNat_lt_modulus hn hnlen (Nat.mod_lt _ (hnpos env))


/-! ## Modular exponentiation and the Fermat inverse -/

/-- Square-and-multiply: one `mulModP` per bit, plus one more per set bit. The base `x`
is a list of already-bound expressions, so referring to it in the multiply step costs
nothing; the recursion is on the exponent's bit list, least-significant bit first,
using `x ^ (2e + b) = (x ^ e)² · x ^ b`. -/
def powModP (n : List (U64Expr K)) (qlen rlen bits : ℕ) :
    List Bool → List (U64Expr K) → M K (List (U64Expr K))
  | [], _ => Pure.pure (constDigits 1 rlen)
  | b :: bs, x => do
      let r ← powModP n qlen rlen bits bs x
      let sq ← mulModP n r r qlen rlen bits
      if b then mulModP n sq x qlen rlen bits else Pure.pure sq

/-- Correctness of `powModP`. The side conditions are stated once, on the modulus and
the widths: every intermediate is reduced mod `n`, so `n.length < rlen` keeps a
register wide enough and `base ^ (2 * n.length) ≤ 2 ^ bits` keeps every product inside
the division loop's dividend width. -/
theorem computesBig_powModP (n : List (U64Expr K)) (qlen rlen bits : ℕ)
    (hnlen : n.length < rlen) (hbits : base ^ (2 * n.length) ≤ 2 ^ bits)
    (hqbig : 2 ^ bits ≤ base ^ qlen) :
    ∀ (bs : List Bool) {S : Array (Step K)} {x : List (U64Expr K)} {nv xv},
      EvalsBig S n nv → EvalsBig S x xv → (∀ env, 1 < lval (nv env)) →
      (∀ env, lval (xv env) < lval (nv env)) →
      ComputesBig S (powModP n qlen rlen bits bs x)
        (fun env => ofNat (lval (xv env) ^ ofBitsLE bs % lval (nv env)) rlen) := by
  have hple : base ^ n.length ≤ base ^ rlen := Nat.pow_le_pow_right base_pos (by omega)
  have hsq : base ^ n.length * base ^ n.length = base ^ (2 * n.length) := by
    rw [← pow_add, two_mul]
  intro bs
  induction bs with
  | nil =>
    intro S x nv xv hn hx hn1 hxr
    refine Computes.pure ((evalsBig_constDigits 1 rlen).congr fun env => ?_)
    rw [ofBitsLE, pow_zero, Nat.mod_eq_of_lt (hn1 env)]
  | cons b bs ih =>
    intro S x nv xv hn hx hn1 hxr
    -- the modulus bounds every reduced intermediate
    have hnlt : ∀ env, lval (nv env) < base ^ n.length := fun env => by
      have := lval_lt (hn.bounded env); rwa [hn.length_eq env] at this
    -- a value reduced mod `n` is faithfully carried by an `rlen`-digit register
    have hred : ∀ (env : ProverEnvironment K) (v : ℕ), v < lval (nv env) →
        lval (ofNat v rlen) = v := fun _ _ hv => lval_ofNat_lt_modulus hn hnlen hv
    have hredlt : ∀ (env : ProverEnvironment K) (v w : ℕ),
        v < lval (nv env) → w < lval (nv env) → v * w < 2 ^ bits := by
      intro env v w hv hw
      have := hnlt env
      calc v * w < base ^ n.length * base ^ n.length :=
            Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
        _ = base ^ (2 * n.length) := hsq
        _ ≤ 2 ^ bits := hbits
    have hmod : ∀ (env : ProverEnvironment K) (v : ℕ), v % lval (nv env) < lval (nv env) :=
      fun env v => Nat.mod_lt _ (by have := hn1 env; omega)
    refine Computes.bind (ih hn hx hn1 hxr) ?_
    intro S1 r hS1 hr
    have hrlt : ∀ env, lval (ofNat (lval (xv env) ^ ofBitsLE bs % lval (nv env)) rlen)
        < lval (nv env) := fun env => by
      rw [hred env _ (hmod env _)]; exact hmod env _
    refine Computes.bind (computesBig_mulModP n r r qlen rlen bits (hn.mono hS1) hr hr
      (fun env => by have := hn1 env; omega) hnlen
      (fun env => hredlt env _ _ (hrlt env) (hrlt env)) hqbig) ?_
    intro S2 sq hS2 hsq'
    replace hsq' : EvalsBig S2 sq
        (fun env => ofNat (lval (xv env) ^ (2 * ofBitsLE bs) % lval (nv env)) rlen) :=
      hsq'.congr fun env => by
        rw [hred env _ (hmod env _), sq_mod_pow]
    have hsqlt : ∀ env, lval (ofNat (lval (xv env) ^ (2 * ofBitsLE bs) % lval (nv env)) rlen)
        < lval (nv env) := fun env => by
      rw [hred env _ (hmod env _)]; exact hmod env _
    cases b
    · refine Computes.pure (hsq'.congr fun env => ?_)
      rw [ofBitsLE, if_neg (by simp), Nat.add_zero]
    · refine ComputesBig.congr (computesBig_mulModP n sq x qlen rlen bits
        (hn.mono (hS1.trans hS2)) hsq' (hx.mono (hS1.trans hS2))
        (fun env => by have := hn1 env; omega) hnlen
        (fun env => hredlt env _ _ (hsqlt env) (hxr env)) hqbig) fun env => ?_
      rw [ofBitsLE, if_pos rfl, hred env _ (hmod env _), mul_mod_pow_succ]

/-- The modular inverse in `ZMod q` by Fermat: `x ^ (q - 2) % q`, with the exponent's
`len` low bits driving the square-and-multiply chain. The modulus is a literal, so it
enters as `constDigits`. -/
def invModP (q nlen qlen rlen bits len : ℕ) (x : List (U64Expr K)) : M K (List (U64Expr K)) :=
  powModP (constDigits q nlen) qlen rlen bits (bitsLE len (q - 2)) x

/-- Correctness of `invModP`. Unconditional in the *value* of `x` in the sense that
matters: a zero input gives `0`, matching `(0 : ZMod q)⁻¹ = 0`. `x` must still be
reduced (`lval x < q`), which is what keeps the multiply step's product inside the
dividend width; every caller normalizes its emulated-field operands anyway. -/
theorem computesBig_invModP {q : ℕ} [Fact q.Prime] (hq : 2 < q) (nlen qlen rlen bits len : ℕ)
    (hqn : q < base ^ nlen) (hnlen : nlen < rlen)
    (hbits : base ^ (2 * nlen) ≤ 2 ^ bits) (hqbig : 2 ^ bits ≤ base ^ qlen)
    (hlen : q - 2 < 2 ^ len)
    {S : Array (Step K)} {x : List (U64Expr K)} {xv}
    (hx : EvalsBig S x xv) (hxr : ∀ env, lval (xv env) < q) :
    ComputesBig S (invModP q nlen qlen rlen bits len x)
      (fun env => ofNat (((lval (xv env) : ZMod q)⁻¹).val) rlen) := by
  have hlv : lval (ofNat q nlen) = q := lval_ofNat_of_lt hqn
  have hn : EvalsBig S (constDigits q nlen) (fun _ : ProverEnvironment K => ofNat q nlen) :=
    evalsBig_constDigits q nlen
  refine ComputesBig.congr (computesBig_powModP (constDigits q nlen) qlen rlen bits
    (by rw [length_constDigits]; exact hnlen)
    (by rw [length_constDigits]; exact hbits) hqbig (bitsLE len (q - 2)) hn hx
    (fun _ => by rw [hlv]; omega) (fun env => by rw [hlv]; exact hxr env)) fun env => ?_
  rw [hlv, ofBitsLE_bitsLE _ _ hlen, pow_sub_two_mod_eq_inv_val hq]

/-! ## Big values held as a vector of field limbs

A gadget's big integer lives in the circuit as `m` field cells, limb `j` holding bits
`[B·j, B·(j+1))`. Reading it into the digit layer costs **no steps at all**: the limbs
occupy disjoint bit windows, so bit `i` of the value is bit `i % B` of limb `i / B`, and
a `W`-bit digit is just the bit-sum of `W` such reads. Nothing is ever carried, and the
digit count is chosen freely by the caller rather than forced by the operands.

The value the reader lands on is `limbsVal`, which truncates each limb to its `B` bits.
That keeps the statement unconditional: a caller whose limbs really are normalized
(every gadget's `Assumptions` say so) rewrites `limbsVal` to the plain Horner value with
`limbsVal_eq_foldr`.
-/

section Limbs
variable {p : ℕ} [Fact p.Prime]

/-- The ℕ values of a list of circuit expressions under a prover environment. -/
def limbVals (x : List (Expression (F p))) (env : ProverEnvironment (F p)) : List ℕ :=
  x.map fun e => (Expression.eval env.toEnvironment e).val

/-- Base-`2^B` value of a limb list, each limb truncated to its `B` bits. -/
def limbsVal (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => v % 2 ^ B + 2 ^ B * limbsVal B vs

/-- Bit `i` of a limb list: bit `i % B` of limb `i / B`. -/
def limbBitN (B : ℕ) (vs : List ℕ) (i : ℕ) : ℕ := vs.getD (i / B) 0 / 2 ^ (i % B) % 2

theorem limbBitN_lt_two (B : ℕ) (vs : List ℕ) (i : ℕ) : limbBitN B vs i < 2 :=
  Nat.mod_lt _ (by norm_num)

private theorem mod_pow_div_mod_two {v B i : ℕ} (hi : i < B) :
    v % 2 ^ B / 2 ^ i % 2 = v / 2 ^ i % 2 := by
  have hsplit : (2 : ℕ) ^ B = 2 ^ i * 2 ^ (B - i) := by
    rw [← pow_add]; congr 1; omega
  have hdvd : (2 : ℕ) ∣ 2 ^ (B - i) := dvd_pow_self 2 (by omega)
  rw [hsplit, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]

private theorem add_pow_div_mod_two (a R : ℕ) {B i : ℕ} (hi : i < B) :
    (a + 2 ^ B * R) / 2 ^ i % 2 = a / 2 ^ i % 2 := by
  have hpow : (0 : ℕ) < 2 ^ i := Nat.two_pow_pos i
  have hsplit : (2 : ℕ) ^ B = 2 ^ i * (2 * 2 ^ (B - i - 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc, Nat.add_mul_div_left _ _ hpow,
    show 2 * 2 ^ (B - i - 1) * R = 2 * (2 ^ (B - i - 1) * R) by ring,
    Nat.add_mul_mod_self_left]

theorem limbsVal_bit (B : ℕ) (hB : 0 < B) :
    ∀ (vs : List ℕ) (i : ℕ), limbsVal B vs / 2 ^ i % 2 = limbBitN B vs i := by
  intro vs
  induction vs with
  | nil => intro i; simp [limbsVal, limbBitN]
  | cons v vs ih =>
    intro i
    have hpow : (0 : ℕ) < 2 ^ i := Nat.two_pow_pos i
    by_cases hi : i < B
    · rw [limbsVal, limbBitN, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, List.getD_cons_zero,
        add_pow_div_mod_two _ _ hi, mod_pow_div_mod_two hi]
    · have hle : B ≤ i := by omega
      have ha : v % 2 ^ B / 2 ^ B = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos B))
      have hsplit : (2 : ℕ) ^ i = 2 ^ B * 2 ^ (i - B) := by
        rw [← pow_add]; congr 1; omega
      have hdiv : i / B = (i - B) / B + 1 := Nat.div_eq_sub_div hB hle
      have hmod : i % B = (i - B) % B := Nat.mod_eq_sub_mod hle
      rw [limbsVal, limbBitN, hdiv, hmod, List.getD_cons_succ, hsplit,
        ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos B), ha, Nat.zero_add,
        ← limbBitN, ← ih (i - B)]

/-! ### The IR side -/

/-- Bit `i` of a limb list held as circuit expressions: bit `i % B` of limb `i / B`. -/
def limbBitE (B : ℕ) (x : List (Expression (F p))) (i : ℕ) : U64Expr (F p) :=
  .ite (.bit (.expr (x.getD (i / B) (Expression.const 0))) (i % B)) (uc 1) (uc 0)

theorem getD_limbVals (env : ProverEnvironment (F p)) :
    ∀ (x : List (Expression (F p))) (k : ℕ),
      (Expression.eval env.toEnvironment (x.getD k (Expression.const 0))).val
        = (limbVals x env).getD k 0 := by
  intro x
  induction x with
  | nil => intro k; simp [limbVals, Expression.eval]
  | cons e es ih =>
    intro k
    cases k with
    | zero => simp [limbVals]
    | succ k => simpa [limbVals] using ih k

theorem evalsU_limbBitE {S : Array (Step (F p))} (B : ℕ) (x : List (Expression (F p))) (i : ℕ) :
    EvalsU S (limbBitE B x i) (fun env => limbBitN B (limbVals x env) i) :=
  (EvalsU.bit _ (i % B)).congr fun env => by
    rw [limbBitN, FiniteField.val_F, getD_limbVals]

/-- The digits of the value a limb list denotes: `len` digits, no steps at all. Each
digit is a `W`-bit window of the value, and each bit of the value is one bit of one
limb, so nothing has to be carried. -/
def limbsDigits (B : ℕ) (x : List (Expression (F p))) (len : ℕ) : List (U64Expr (F p)) :=
  ofFnDigits (fun k => bitsToDigit (limbBitE B x) (W * k) W) len

@[simp] theorem length_limbsDigits (B : ℕ) (x : List (Expression (F p))) (len : ℕ) :
    (limbsDigits B x len).length = len := by simp [limbsDigits]

theorem evalsBig_limbsDigits {S : Array (Step (F p))} {B : ℕ} (hB : 0 < B)
    (x : List (Expression (F p))) (len : ℕ) :
    EvalsBig S (limbsDigits B x len)
      (fun env => ofNat (limbsVal B (limbVals x env)) len) := by
  refine evalsBig_ofFnDigits (fun _ => length_ofNat _ _) (fun _ => bounded_ofNat _ _)
    (fun k hk => ?_)
  refine (evalsU_bitsToDigit (fun j => evalsU_limbBitE B x j)
    (fun env j => limbBitN_lt_two B _ j) W (W * k) (by rw [W]; omega)).congr fun env => ?_
  have hbits : limbBitN B (limbVals x env)
      = fun j => limbsVal B (limbVals x env) / 2 ^ j % 2 := by
    funext j; rw [limbsVal_bit B hB]
  rw [hbits, bitWindow_bits, getD_ofNat _ _ _ hk, base_pow, base]

/-! ### Arithmetic of `limbsVal` -/

theorem limbsVal_lt (B : ℕ) : ∀ vs : List ℕ, limbsVal B vs < 2 ^ (B * vs.length)
  | [] => by simp [limbsVal]
  | v :: vs => by
      have ih := limbsVal_lt B vs
      have hv : v % 2 ^ B < 2 ^ B := Nat.mod_lt _ (Nat.two_pow_pos B)
      have hsplit : (2 : ℕ) ^ (B * (vs.length + 1)) = 2 ^ B * 2 ^ (B * vs.length) := by
        rw [← pow_add]; congr 1; ring
      rw [limbsVal, List.length_cons, hsplit]
      calc v % 2 ^ B + 2 ^ B * limbsVal B vs
          < 2 ^ B + 2 ^ B * limbsVal B vs := by omega
        _ = 2 ^ B * (limbsVal B vs + 1) := by ring
        _ ≤ 2 ^ B * 2 ^ (B * vs.length) := Nat.mul_le_mul_left _ ih

/-- On limbs that really are `B`-bit values the truncating `limbsVal` is the plain
little-endian Horner value the solution's `BigInt.value` is defined by. -/
theorem limbsVal_eq_foldr (B : ℕ) : ∀ vs : List ℕ, (∀ v ∈ vs, v < 2 ^ B) →
    limbsVal B vs = vs.foldr (fun v acc => v + acc * 2 ^ B) 0
  | [], _ => rfl
  | v :: vs, h => by
      rw [limbsVal, List.foldr_cons, ← limbsVal_eq_foldr B vs (fun w hw => h w (by simp [hw])),
        Nat.mod_eq_of_lt (h v (by simp))]
      ring

/-! ### The output side: limbs of a digit list -/

/-- The `n` limbs of `B` bits each of the value a digit list denotes, as a literal
output vector. This is what a big-integer witness site returns. -/
def limbsOut (ds : List (U64Expr (F p))) (B n : ℕ) : VExpr (F p) n :=
  .lit (Vector.ofFn fun j : Fin n => limbF ds (B * j.val) B)

theorem evalsV_limbsOut {S : Array (Step (F p))} {ds : List (U64Expr (F p))} {dv}
    (h : EvalsBig S ds dv) (B n : ℕ) :
    EvalsV S (limbsOut ds B n)
      (fun env => Vector.ofFn fun j : Fin n =>
        ((lval (dv env) / 2 ^ (B * j.val) % 2 ^ B : ℕ) : F p)) :=
  EvalsV.lit fun k hk => by
    simpa only [Vector.getElem_ofFn] using evalsF_limbF h (B * k) B

end Limbs

end WitgenBigNat
end Solution.Secp256k1ScalarMulFixedBase
