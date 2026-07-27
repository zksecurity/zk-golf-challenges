import Challenge.Utils.CostR1CS

/-!
# Generic row-predicate R1CS certification

The compositional `isR1CS` machinery, meaning the circuit-level certificate and its
combinators (`bind`, `subcircuit`, `forEach`, …), only appends and splits
operation lists; it does not care *which* per-row predicate it enforces. This
file abstracts all of it over a row predicate `P : Expression F → Prop`.

`isR1CS` is then the `P := isR1CSRow` instance (bridged here by
`operationsRow_isR1CSRow_iff`), and the canonical (C = identity) certificate is
the `P := isCidentityRow` instance (see `CostR1CSCanonical`). Every combinator is
proved once here; an instance adds only its row predicate, its `assertZero`
builder and, via `IsRowCirc.mono`, a row-level refinement to `isR1CSRow`.
-/

namespace Challenge.CostR1CS

variable {F : Type} {α β : Type}

/-! ### Row-predicate certificates over flat / nested operation lists -/

def flatOperationsRow (P : Expression F → Prop) : List (FlatOperation F) → Prop
  | [] => True
  | .witness _ _ :: ops => flatOperationsRow P ops
  | .assert e :: ops => P e ∧ flatOperationsRow P ops
  | .lookup _ :: _ => False
  | .interact _ :: _ => False

def operationsRow (P : Expression F → Prop) [Field F] : Operations F → Prop
  | [] => True
  | .witness _ _ :: ops => operationsRow P ops
  | .assert e :: ops => P e ∧ operationsRow P ops
  | .lookup _ :: _ => False
  | .interact _ :: _ => False
  | .subcircuit s :: ops => flatOperationsRow P s.ops.toFlat ∧ operationsRow P ops

/-! ### Monotonicity in the row predicate -/

theorem flatOperationsRow_mono {P Q : Expression F → Prop} (hPQ : ∀ e, P e → Q e)
    {ops : List (FlatOperation F)} (h : flatOperationsRow P ops) : flatOperationsRow Q ops := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | witness => exact ih h
    | assert e => exact ⟨hPQ _ h.1, ih h.2⟩
    | lookup => exact h.elim
    | interact => exact h.elim

theorem operationsRow_mono [Field F] {P Q : Expression F → Prop} (hPQ : ∀ e, P e → Q e)
    {ops : Operations F} (h : operationsRow P ops) : operationsRow Q ops := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | witness => exact ih h
    | assert e => exact ⟨hPQ _ h.1, ih h.2⟩
    | lookup => exact h.elim
    | interact => exact h.elim
    | subcircuit s => exact ⟨flatOperationsRow_mono hPQ h.1, ih h.2⟩

/-! ### Append / flatten / toFlat -/

theorem flatOperationsRow_append (P : Expression F → Prop) (ops₁ ops₂ : List (FlatOperation F)) :
    flatOperationsRow P (ops₁ ++ ops₂) ↔ flatOperationsRow P ops₁ ∧ flatOperationsRow P ops₂ := by
  induction ops₁ with
  | nil => simp [flatOperationsRow]
  | cons op ops ih => cases op <;> simp [flatOperationsRow, ih, and_assoc]

theorem operationsRow_append [Field F] (P : Expression F → Prop) (ops₁ ops₂ : Operations F) :
    operationsRow P (ops₁ ++ ops₂) ↔ operationsRow P ops₁ ∧ operationsRow P ops₂ := by
  induction ops₁ with
  | nil => simp [operationsRow]
  | cons op ops ih => cases op <;> simp [operationsRow, ih, and_assoc]

theorem operationsRow_iff_toFlat [Field F] (P : Expression F → Prop) (ops : Operations F) :
    operationsRow P ops ↔ flatOperationsRow P ops.toFlat := by
  induction ops with
  | nil => simp [operationsRow, flatOperationsRow, Operations.toFlat]
  | cons op ops ih =>
    cases op <;> simp [operationsRow, flatOperationsRow, Operations.toFlat,
      flatOperationsRow_append, ih]

theorem operationsRow_flatten_ofFn {m : ℕ} [Field F] (P : Expression F → Prop)
    (g : Fin m → Operations F) (h : ∀ i, operationsRow P (g i)) :
    operationsRow P (List.ofFn g).flatten := by
  induction m with
  | zero => simp [List.ofFn_zero, List.flatten_nil, operationsRow]
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, operationsRow_append]
    exact ⟨h 0, ih (fun i => g i.succ) (fun i => h i.succ)⟩

/-! ### Circuit-level certificate + combinators -/

def IsRowCirc (P : Expression F → Prop) [Field F] (c : Circuit F α) : Prop :=
  ∀ n, operationsRow P (c.operations n)

section
variable [Field F] {P : Expression F → Prop}

theorem IsRowCirc.mono {Q : Expression F → Prop} (hPQ : ∀ e, P e → Q e)
    {c : Circuit F α} (h : IsRowCirc P c) : IsRowCirc Q c :=
  fun n => operationsRow_mono hPQ (h n)

theorem IsRowCirc.pure (a : α) : IsRowCirc P (pure a : Circuit F α) := by
  intro n; rw [Circuit.pure_operations_eq]; trivial

theorem IsRowCirc.bind {f : Circuit F α} {g : α → Circuit F β}
    (hf : IsRowCirc P f) (hg : ∀ a, IsRowCirc P (g a)) : IsRowCirc P (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, operationsRow_append]
  exact ⟨hf n, hg _ _⟩

theorem IsRowCirc.witnessVector (m : ℕ) (c : ProverEnvironment F → Vector F m) :
    IsRowCirc P (Circuit.witnessVector m c) := by intro n; trivial

theorem IsRowCirc.assertZero {e : Expression F} (h : P e) :
    IsRowCirc P (Circuit.assertZero e) := by
  intro n
  show operationsRow P [Operation.assert e]
  exact ⟨h, trivial⟩

theorem IsRowCirc.subcircuit {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuit F Input Output} {b : Var Input F}
    (h : ∀ n, operationsRow P ((circuit.main b).operations n)) :
    IsRowCirc P (subcircuit circuit b) := by
  intro n
  show operationsRow P [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsRow P (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (operationsRow_iff_toFlat _ _).mp (h n)

theorem IsRowCirc.bind_out {f : Circuit F α} {g : α → Circuit F β}
    (hf : IsRowCirc P f) (hg : ∀ n, IsRowCirc P (g (f.output n))) : IsRowCirc P (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, operationsRow_append]
  exact ⟨hf n, (hg n) (n + f.localLength n)⟩

theorem isRowCirc_forEach_mem {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit F Unit} {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsRow P ((body xs[i.val]).operations n)) :
    IsRowCirc P (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsRow_flatten_ofFn _ _ (fun i => h i _)

end

/-! ### `isR1CS` is the `P := isR1CSRow` instance -/

theorem flatOperationsRow_isR1CSRow_iff (ops : List (FlatOperation F)) :
    flatOperationsRow isR1CSRow ops ↔ flatOperationsIsR1CS ops := by
  induction ops with
  | nil => simp [flatOperationsRow, flatOperationsIsR1CS]
  | cons op ops ih => cases op <;> simp [flatOperationsRow, flatOperationsIsR1CS, ih]

theorem operationsRow_isR1CSRow_iff [Field F] (ops : Operations F) :
    operationsRow isR1CSRow ops ↔ operationsIsR1CS ops := by
  induction ops with
  | nil => simp [operationsRow, operationsIsR1CS]
  | cons op ops ih =>
    cases op <;>
      simp [operationsRow, operationsIsR1CS, ih, flatOperationsRow_isR1CSRow_iff]

theorem isRowCirc_isR1CSRow_iff [Field F] (c : Circuit F α) :
    IsRowCirc isR1CSRow c ↔ IsR1CSCirc c := by
  simp only [IsRowCirc, IsR1CSCirc, operationsRow_isR1CSRow_iff]

end Challenge.CostR1CS
