import Clean.Circuit

/-!
# Structured witness generation (the witness-IR obligation)

Witness generators in Clean are `WitgenIR` programs with two constructors:

- `.ir steps out` — the deep-embedded **witness IR**: a straight-line list of
  scalar `let`-steps followed by a vector-shaped output expression. Plain data,
  hence serializable, exportable to an external prover, and re-interpretable
  outside Lean.
- `.native f` — an arbitrary Lean closure. The migration escape hatch: not data,
  not serializable, not exportable.

A solution that generates its witnesses with `.native` closures is only a proof
artifact: nothing outside Lean can reproduce its assignment. This file defines the
trusted obligation that rules the escape hatch out, `Challenge.WitgenIR.witgenIsIR`,
together with the compositional lemmas that make proving it mechanical.

## The property

`witgenIsIR main` says: for every symbolic input and every offset, **every** witness
operation reachable from `main input` — including the ones inside subcircuits — is
an `.ir` program. It is a purely structural, environment-free statement: there are
no hypotheses on the input, and the values a generator computes are irrelevant.

It is morally the sibling of `Challenge.CostR1CS.isR1CS`: a shape claim about the
operation list that is proved by walking the circuit's `do`-block with the
combinators below, never by reducing a whole flattened operation list.

## Proving it

Mirror the `IsR1CSCirc` proofs in a solution's `Cost.lean`: one `UsesIRCirc` lemma
per gadget, composed with `UsesIRCirc.bind` / `.forEach` / `.foldlRange` /
`.subcircuit`, where every non-witness operation is discharged by `trivial` and every
witness site is discharged by the entry point it was built with (`witnessVector`,
`witnessField`, `witnessIR`, `witnessProgram`, ...). Higher-level gadgets consume the
lower ones' lemmas through `UsesIRCirc.subcircuit`; they never unfold a child gadget.

## Scope

The obligation covers witness *operations*. Prover-only *inputs* (`Unconstrained` /
`UnconstrainedNative` hints) are inputs of the circuit family, not operations, so
they are outside its reach; an instance that admits hints has to constrain them in
its interface.

An `.ir` program is finite data, but two of its leaves are still nondeterministic
reads: `FExpr.dataGet` and `FExpr.hintGet` fetch prover-supplied rows rather than
computing anything. This obligation accepts them — what rules them out is
`computableWitness`, whose `AgreesBelow` hypothesis constrains only
`ProverEnvironment.get`, so two environments may differ in their `data`/`hint` while
agreeing below the offset, and a generator reading either one cannot be shown to
agree on both. The two obligations are therefore complementary: `witgenIsIR` forces
the generator to be data, `computableWitness` forces that data to be a function of
the circuit input and the witnesses already allocated.
-/

namespace Challenge.WitgenIR

variable {F : Type} [FiniteField F] {α β : Type}

/-! ## The structural predicate -/

/-- A single witness generator is IR-backed: a structured witness-IR program
(`.ir steps out`), not an opaque Lean closure (`.native f`). -/
def IsIR {m : ℕ} : Witgen.WitgenIR F m → Prop
  | .native _ => False
  | .ir _ _ => True

omit [FiniteField F] in
@[simp] theorem isIR_ir {m : ℕ} (steps : List (Witgen.Step F))
    (out : Witgen.VExpr F m) : IsIR (.ir steps out) := trivial

omit [FiniteField F] in
@[simp] theorem not_isIR_native {m : ℕ} (f : ProverEnvironment F → Vector F m) :
    ¬ IsIR (.native f) := id

/-- Every witness generator in a **fully flattened** operation list is IR-backed. -/
def flatOperationsUseIR : List (FlatOperation F) → Prop
  | [] => True
  | .witness _ c :: ops => IsIR c ∧ flatOperationsUseIR ops
  | .assert _ :: ops | .lookup _ :: ops | .interact _ :: ops => flatOperationsUseIR ops

/-- Every witness generator in a (nested) operation list is IR-backed: the shallow
witnesses directly, and each subcircuit through `flatOperationsUseIR` on its
flattened body. By `operationsUseIR_iff_toFlat` this is exactly
`flatOperationsUseIR` on the fully flattened operations. -/
def operationsUseIR : Operations F → Prop
  | [] => True
  | .witness _ c :: ops => IsIR c ∧ operationsUseIR ops
  | .assert _ :: ops | .lookup _ :: ops | .interact _ :: ops => operationsUseIR ops
  | .subcircuit s :: ops => flatOperationsUseIR s.ops.toFlat ∧ operationsUseIR ops

/-- A circuit generates all of its witnesses through the IR, at every offset. -/
def UsesIRCirc (c : Circuit F α) : Prop :=
  ∀ n, operationsUseIR (c.operations n)

/-- **The trusted obligation.** A circuit family (the `main` of a formal circuit)
generates every witness — its own and those of every subcircuit it calls — through
the witness IR, for every symbolic input and at every offset. -/
def witgenIsIR {Input : TypeMap} [ProvableType Input]
    (main : Var Input F → Circuit F α) : Prop :=
  ∀ input : Var Input F, UsesIRCirc (main input)

/-! ## Traversal lemmas -/

omit [FiniteField F] in
@[simp] theorem flatOperationsUseIR_nil :
    flatOperationsUseIR ([] : List (FlatOperation F)) = True := rfl

@[simp] theorem operationsUseIR_nil :
    operationsUseIR ([] : Operations F) = True := rfl

omit [FiniteField F] in
theorem flatOperationsUseIR_append (ops₁ ops₂ : List (FlatOperation F)) :
    flatOperationsUseIR (ops₁ ++ ops₂) ↔
      flatOperationsUseIR ops₁ ∧ flatOperationsUseIR ops₂ := by
  induction ops₁ with
  | nil => simp [flatOperationsUseIR]
  | cons op ops ih => cases op <;> simp [flatOperationsUseIR, ih, and_assoc]

theorem operationsUseIR_append (ops₁ ops₂ : Operations F) :
    operationsUseIR (ops₁ ++ ops₂) ↔
      operationsUseIR ops₁ ∧ operationsUseIR ops₂ := by
  induction ops₁ with
  | nil => simp [operationsUseIR]
  | cons op ops ih => cases op <;> simp [operationsUseIR, ih, and_assoc]

/-- The nested certificate equals the flat certificate on the flattened operations:
`toFlat` inlines every subcircuit, and `flatOperationsUseIR` checks exactly the same
witness generators. -/
theorem operationsUseIR_iff_toFlat (ops : Operations F) :
    operationsUseIR ops ↔ flatOperationsUseIR ops.toFlat := by
  induction ops with
  | nil => simp [operationsUseIR, Operations.toFlat]
  | cons op ops ih =>
      cases op <;>
        simp [operationsUseIR, flatOperationsUseIR, Operations.toFlat,
          flatOperationsUseIR_append, ih]

theorem operationsUseIR_flatten_ofFn {m : ℕ} (g : Fin m → Operations F)
    (h : ∀ i, operationsUseIR (g i)) :
    operationsUseIR (List.ofFn g).flatten := by
  induction m with
  | zero => simp [List.ofFn_zero, List.flatten_nil]
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons, operationsUseIR_append]
      exact ⟨h 0, ih (fun i => g i.succ) (fun i => h i.succ)⟩

/-- A subcircuit's flattened body is the flattening of its `main`'s operations. -/
private theorem subcircuit_ops_toFlat_eq {name : String} {n : ℕ} (ops : Operations F)
    (s : Subcircuit F n) (h : s.ops = .nested ⟨name, ops.toNested⟩) :
    s.ops.toFlat = ops.toFlat := by
  rw [h, Operations.toNested_toFlat]

/-! ## Structural lemmas: monadic skeleton -/

theorem UsesIRCirc.pure (a : α) : UsesIRCirc (pure a : Circuit F α) := by
  intro n; rw [Circuit.pure_operations_eq]; trivial

theorem UsesIRCirc.bind {f : Circuit F α} {g : α → Circuit F β}
    (hf : UsesIRCirc f) (hg : ∀ a, UsesIRCirc (g a)) : UsesIRCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, operationsUseIR_append]
  exact ⟨hf n, hg _ _⟩

theorem UsesIRCirc.map {f : Circuit F α} {g : α → β} (hf : UsesIRCirc f) :
    UsesIRCirc (g <$> f) := by
  intro n; rw [Circuit.map_operations_eq]; exact hf n

/-! ## Structural lemmas: witness entry points

Each IR-backed entry point is accepted; `witnessNative` / `witnessVectorNative` are
refuted below. -/

theorem UsesIRCirc.witnessVar (ir : Witgen.WitgenIR F 1) (h : IsIR ir) :
    UsesIRCirc (Circuit.witnessVar ir) := by
  intro n; exact ⟨h, trivial⟩

theorem UsesIRCirc.witnessField (e : Witgen.FExpr F) :
    UsesIRCirc (Circuit.witnessField e) := by
  intro n; exact ⟨trivial, trivial⟩

theorem UsesIRCirc.witnessVector (m : ℕ) (out : Witgen.VExpr F m) :
    UsesIRCirc (Circuit.witnessVector m out) := by
  intro n; exact ⟨trivial, trivial⟩

theorem UsesIRCirc.witnessIR (M : TypeMap) [ProvableType M] (ir : Witgen.WitgenIR F (size M))
    (h : IsIR ir) : UsesIRCirc (_root_.witnessIR M ir) := by
  intro n; exact ⟨h, trivial⟩

theorem UsesIRCirc.witnessVectorProgram (m : ℕ) (program : Witgen.M F (Witgen.VExpr F m)) :
    UsesIRCirc (witnessVectorProgram m program) := by
  intro n; exact ⟨trivial, trivial⟩

/-- `witnessProgram` on the generic `Witnessable F M (Var M)` instance: the payload is
`Witgen.M.toIRLiteral`, which is an `.ir` program by construction. -/
theorem UsesIRCirc.witnessProgram {M : TypeMap} [ProvableType M]
    (program : Witgen.M F (M (Witgen.FExpr F))) :
    UsesIRCirc (witnessProgram (value := M) (var := Var M) program) := by
  intro n; exact ⟨trivial, trivial⟩

/-- Struct-valued `witness` on the generic `Witnessable F M (Var M)` instance: the
payload is `Witgen.WitgenIR.ofFExprs`, which is an `.ir` program. -/
theorem UsesIRCirc.witnessValue {M : TypeMap} [ProvableType M]
    (xs : M (Witgen.FExpr F)) :
    UsesIRCirc (witness (F := F) (value := M) (var := Var M) xs) := by
  intro n; exact ⟨trivial, trivial⟩

/-- Scalar `witness` on the `Witnessable F field Expression` instance. -/
theorem UsesIRCirc.witnessFieldValue (e : Witgen.FExpr F) :
    UsesIRCirc (witness (F := F) (value := field) (var := Expression) e) := by
  intro n; exact ⟨trivial, trivial⟩

/-- Vector `witness` on the `Witnessable F (fields m) (Var (fields m))` instance. -/
theorem UsesIRCirc.witnessVectorValue {m : ℕ} (xs : fields m (Witgen.FExpr F)) :
    UsesIRCirc (witness (F := F) (value := fields m) (var := Var (fields m)) xs) := by
  intro n; exact ⟨trivial, trivial⟩

/-! ## Structural lemmas: non-witness operations -/

theorem UsesIRCirc.assertZero (e : Expression F) :
    UsesIRCirc (Circuit.assertZero e) := by
  intro n; trivial

theorem UsesIRCirc.lookup {Row : TypeMap} [ProvableType Row] (table : Table F Row)
    (entry : Row (Expression F)) : UsesIRCirc (Circuit.lookup table entry) := by
  intro n; trivial

/-! ## Structural lemmas: subcircuits -/

/-- Invoking a `FormalCircuit` as a subcircuit is IR-backed when its `main` is. -/
theorem UsesIRCirc.subcircuit {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuit F Input Output} {b : Var Input F}
    (h : ∀ n, operationsUseIR ((circuit.main b).operations n)) :
    UsesIRCirc (_root_.subcircuit circuit b) := by
  intro n
  show operationsUseIR [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsUseIR (circuit.toSubcircuit n b).ops.toFlat
  rw [subcircuit_ops_toFlat_eq ((circuit.main b).operations n) _ rfl]
  exact (operationsUseIR_iff_toFlat _).mp (h n)

/-- Same as `UsesIRCirc.subcircuit`, for a `GeneralFormalCircuit`. -/
theorem UsesIRCirc.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F}
    (h : ∀ n, operationsUseIR ((circuit.main b).operations n)) :
    UsesIRCirc (subcircuitWithAssertion circuit b) := by
  intro n
  show operationsUseIR [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsUseIR (circuit.toSubcircuit n b).ops.toFlat
  rw [subcircuit_ops_toFlat_eq ((circuit.main b).operations n) _ rfl]
  exact (operationsUseIR_iff_toFlat _).mp (h n)

/-- Same as `UsesIRCirc.subcircuit`, for a `FormalAssertion`. -/
theorem UsesIRCirc.assertion {Input : TypeMap} [ProvableType Input]
    {circuit : FormalAssertion F Input} {b : Var Input F}
    (h : ∀ n, operationsUseIR ((circuit.main b).operations n)) :
    UsesIRCirc (_root_.assertion circuit b) := by
  intro n
  show operationsUseIR [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsUseIR (circuit.toSubcircuit n b).ops.toFlat
  rw [subcircuit_ops_toFlat_eq ((circuit.main b).operations n) _ rfl]
  exact (operationsUseIR_iff_toFlat _).mp (h n)

/-! ## Structural lemmas: loops -/

theorem UsesIRCirc.forEach {m : ℕ} [Inhabited α] {xs : Vector α m} {body : α → Circuit F Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ a n, operationsUseIR ((body a).operations n)) :
    UsesIRCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsUseIR_flatten_ofFn _ (fun i => h _ _)

theorem UsesIRCirc.mapFinRange {m : ℕ} [NeZero m] {body : Fin m → Circuit F β}
    {constant : Circuit.ConstantLength body}
    (h : ∀ i n, operationsUseIR ((body i).operations n)) :
    UsesIRCirc (Circuit.mapFinRange m body constant) := by
  intro n
  rw [Circuit.mapFinRange.operations_eq]
  exact operationsUseIR_flatten_ofFn _ (fun i => h _ _)

theorem UsesIRCirc.foldlRange {m : ℕ} [Inhabited β] {init : β} {body : β → Fin m → Circuit F β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2}
    (h : ∀ s i n, operationsUseIR ((body s i).operations n)) :
    UsesIRCirc (Circuit.foldlRange m init body constant) := by
  intro n
  rw [Circuit.foldlRange.operations_eq]
  exact operationsUseIR_flatten_ofFn _ (fun i => h _ _ _)

/-! ## Teeth: the escape hatch is refuted

These are the lemmas that make the obligation non-vacuous: a solution that keeps a
single closure-backed witness generator cannot prove `witgenIsIR`. -/

theorem not_usesIRCirc_witnessVectorNative (m : ℕ) (c : ProverEnvironment F → Vector F m) :
    ¬ UsesIRCirc (witnessVectorNative m c) := by
  intro h
  exact (h 0).1

theorem not_usesIRCirc_witnessNative {M : TypeMap} [ProvableType M]
    (c : ProverEnvironment F → M F) :
    ¬ UsesIRCirc (witnessNative (var := Var M) c) := by
  intro h
  exact (h 0).1

theorem not_usesIRCirc_witnessFieldNative (c : ProverEnvironment F → F) :
    ¬ UsesIRCirc (witnessNative (value := field) (var := Expression) c) := by
  intro h
  exact (h 0).1

end Challenge.WitgenIR
