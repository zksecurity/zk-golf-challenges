import Clean.Circuit.Basic
import Clean.Circuit.Operations
import Clean.Circuit.Loops

/-!
# R1CS counting + single-row certification

Two small utilities for measuring the RSA circuit family:

* `circuitCount` — given a circuit, count witness **allocations** and **constraint**
  rows (one row per `assert`). It *assumes* every `assert` is a single R1CS row; it
  does not re-check that. The traversal is a worklist loop over the operation forest,
  so it runs on arbitrarily large circuits without tripping the `#eval`
  deep-recursion guard.

* `isR1CSRow` / `operationsIsR1CS` — the certification that the count's assumption
  holds, stated as a *positive* `Prop` (no violation lists). `isR1CSRow e` says an
  asserted expression is a single R1CS row: it has the shape `A*B - C` with `A, B, C`
  affine (one rank-1 product, `⟨A,z⟩·⟨B,z⟩ = ⟨C,z⟩`). `operationsIsR1CS ops` says
  every `assert` in `ops` is such a row and there are no lookups/interactions, with
  subcircuits certified by their flattened bodies. `isR1CS c` is the circuit-level
  statement `operationsIsR1CS (c.operations 0)`.

`isR1CSRow` is a *sound over-approximation*: it counts products syntactically
(modulo constant scalars), so `rank ≤ r1csProducts` always. It can over-reject — e.g.
`a*b + a*c = a*(b+c)` is genuinely rank 1 but is counted as `2` — but never
under-counts, so a true multi-row `assert` is never certified as a single row.
-/

namespace Challenge.CostR1CS

variable {F : Type}

/-! ## Single-row R1CS certification -/

/-- Structural multiplicative degree of an expression: an upper bound on its
polynomial degree (exact unless a product cancels, which only makes the check
conservative). `var` is degree 1, `const` degree 0, `add` takes the max, `mul`
adds. -/
def degree : Expression F → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add a b => max (degree a) (degree b)
  | .mul a b => degree a + degree b

/-- An expression is *affine* if its structural degree is at most 1. -/
def Affine (e : Expression F) : Prop := degree e ≤ 1

/-- Number of genuine degree-2 product terms along the top-level `add` spine, or
`none` if some summand is not a valid R1CS term. The `add` spine sums the counts,
so `a*b + c*d` reports `2`.

For a `mul` node we first look through any **constant** factor: a degree-0 factor
only *scales* the other side, adding no product and not raising the degree, so its
count is the count of the other factor. This is what lets a *negated* product such
as `(-1) * (A*B)` — which is how `a - b*c` desugars (`Sub`/`Neg` build
`add _ (mul (const (-1)) _)`) — still count as the single product it genuinely is.
With both factors non-constant, the node is one quadratic product exactly when both
are affine (degree ≤ 1); a factor of degree ≥ 2 means total degree ≥ 3, which is
not an R1CS row (`none`). -/
def r1csProducts : Expression F → Option ℕ
  | .const _ => some 0
  | .var _ => some 0
  | .add a b =>
    match r1csProducts a, r1csProducts b with
    | some m, some n => some (m + n)
    | _, _ => none
  | .mul a b =>
    if degree a = 0 then r1csProducts b
    else if degree b = 0 then r1csProducts a
    else if degree a ≤ 1 ∧ degree b ≤ 1 then some 1
    else none

/-- An expression is a single R1CS constraint iff, along its `add` spine, every
summand is affine plus at most one product of two affine forms — exactly the shape
`A * B - C` (one rank-1 row `⟨A,z⟩·⟨B,z⟩ = ⟨C,z⟩`). Pure-affine `A` is allowed (it
is `A · 1 = 0`). Rejected: degree ≥ 3, and two-or-more products such as `a*b + c*d`
(rank-2, which needs an auxiliary witness + a second row). -/
def isR1CSRow (e : Expression F) : Prop :=
  match r1csProducts e with
  | some k => k ≤ 1
  | none => False

/-- Positive R1CS certificate over a **fully flattened** operation list: every
`assert` is a single R1CS row, and there are no lookups or interactions. -/
def flatOperationsIsR1CS : List (FlatOperation F) → Prop
  | [] => True
  | .witness _ _ :: ops => flatOperationsIsR1CS ops
  | .assert e :: ops => isR1CSRow e ∧ flatOperationsIsR1CS ops
  | .lookup _ :: _ => False
  | .interact _ :: _ => False

/-- Positive R1CS certificate over a (nested) operation list: every shallow
`assert` is a single R1CS row, there are no lookups or interactions, and each
subcircuit is certified by `flatOperationsIsR1CS` on its flattened body. By
`operationsIsR1CS_iff_toFlat` this is exactly `flatOperationsIsR1CS` on the
fully flattened operations. -/
def operationsIsR1CS [Field F] : Operations F → Prop
  | [] => True
  | .witness _ _ :: ops => operationsIsR1CS ops
  | .assert e :: ops => isR1CSRow e ∧ operationsIsR1CS ops
  | .lookup _ :: _ => False
  | .interact _ :: _ => False
  | .subcircuit s :: ops => flatOperationsIsR1CS s.ops.toFlat ∧ operationsIsR1CS ops

/-- A circuit is single-row R1CS iff its operations (at offset 0) are. -/
def isR1CSCircuit {α : Type} [Field F] (c : Circuit F α) (offset : ℕ := 0) : Prop :=
  operationsIsR1CS (Circuit.operations c offset)

/-! ## Counting allocations and constraints (assuming R1CS form) -/

/-- Number of witness cells (`allocations`) and constraint rows (`constraints`) of a
circuit. Assumes every `assert` is a single R1CS row (certify separately with
`operationsIsR1CS`). -/
structure Count where
  allocations : ℕ
  constraints : ℕ
deriving Repr, DecidableEq, Inhabited

namespace Count

def zero : Count := ⟨0, 0⟩

def add (x y : Count) : Count :=
  ⟨x.allocations + y.allocations, x.constraints + y.constraints⟩

instance : Add Count where
  add := add

@[simp] theorem add_allocations (x y : Count) :
    (x + y).allocations = x.allocations + y.allocations := rfl

@[simp] theorem add_constraints (x y : Count) :
    (x + y).constraints = x.constraints + y.constraints := rfl

theorem zero_add (x : Count) : zero + x = x := by
  cases x with
  | mk allocations constraints =>
      change (⟨0 + allocations, 0 + constraints⟩ : Count) = ⟨allocations, constraints⟩
      rw [Nat.zero_add, Nat.zero_add]

theorem add_zero (x : Count) : x + zero = x := by
  cases x with
  | mk allocations constraints =>
      change (⟨allocations + 0, constraints + 0⟩ : Count) = ⟨allocations, constraints⟩
      rw [Nat.add_zero, Nat.add_zero]

theorem add_assoc (x y z : Count) : x + y + z = x + (y + z) := by
  cases x with
  | mk ax cx =>
      cases y with
      | mk ay cy =>
          cases z with
          | mk az cz =>
              change (⟨(ax + ay) + az, (cx + cy) + cz⟩ : Count) =
                ⟨ax + (ay + az), cx + (cy + cz)⟩
              rw [Nat.add_assoc, Nat.add_assoc]

end Count

def flatOperationCount : FlatOperation F → Count
  | .witness m _ => ⟨m, 0⟩
  | .assert _ => ⟨0, 1⟩
  | .lookup _ => Count.zero
  | .interact _ => Count.zero

def flatCount : List (FlatOperation F) → Count
  | [] => Count.zero
  | op :: ops => flatOperationCount op + flatCount ops

mutual
  def nestedCount : NestedOperations F → Count
    | .single op => flatOperationCount op
    | .nested (_, ops) => nestedListCount ops

  def nestedListCount : List (NestedOperations F) → Count
    | [] => Count.zero
    | op :: ops => nestedCount op + nestedListCount ops
end

def operationCount [Field F] : Operations F → Count
  | [] => Count.zero
  | .witness m c :: ops => flatOperationCount (.witness m c) + operationCount ops
  | .assert e :: ops => flatOperationCount (.assert e) + operationCount ops
  | .lookup l :: ops => flatOperationCount (.lookup l) + operationCount ops
  | .interact i :: ops => flatOperationCount (.interact i) + operationCount ops
  | .subcircuit s :: ops => nestedCount s.ops + operationCount ops

/-- Allocations and constraints of a circuit, assuming R1CS form. -/
def circuitCount {α : Type} [Field F] (c : Circuit F α) (n : ℕ := 0) : Count :=
  operationCount (Circuit.operations c n)

/-! ## Structural lemmas -/

namespace Lemmas

/-! ### R1CS certificate structure -/

@[simp] theorem flatOperationsIsR1CS_nil :
    flatOperationsIsR1CS ([] : List (FlatOperation F)) = True := rfl

@[simp] theorem operationsIsR1CS_nil [Field F] :
    operationsIsR1CS ([] : Operations F) = True := rfl

theorem flatOperationsIsR1CS_append (ops₁ ops₂ : List (FlatOperation F)) :
    flatOperationsIsR1CS (ops₁ ++ ops₂) ↔
      flatOperationsIsR1CS ops₁ ∧ flatOperationsIsR1CS ops₂ := by
  induction ops₁ with
  | nil => simp [flatOperationsIsR1CS]
  | cons op ops ih =>
      cases op <;> simp [flatOperationsIsR1CS, ih, and_assoc]

theorem operationsIsR1CS_append [Field F] (ops₁ ops₂ : Operations F) :
    operationsIsR1CS (ops₁ ++ ops₂) ↔
      operationsIsR1CS ops₁ ∧ operationsIsR1CS ops₂ := by
  induction ops₁ with
  | nil => simp [operationsIsR1CS]
  | cons op ops ih =>
      cases op <;> simp [operationsIsR1CS, ih, and_assoc]

/-- The nested certificate equals the flat certificate on the flattened
operations: `toFlat` already inlines every subcircuit, and
`flatOperationsIsR1CS` checks exactly the same asserts. -/
theorem operationsIsR1CS_iff_toFlat [Field F] (ops : Operations F) :
    operationsIsR1CS ops ↔ flatOperationsIsR1CS ops.toFlat := by
  induction ops with
  | nil => simp [operationsIsR1CS, Operations.toFlat]
  | cons op ops ih =>
      cases op <;>
        simp [operationsIsR1CS, flatOperationsIsR1CS, Operations.toFlat,
          flatOperationsIsR1CS_append, ih]

/-! ### Count traversal -/

theorem operationCount_append [Field F] (a b : Operations F) :
    operationCount (a ++ b) = operationCount a + operationCount b := by
  induction a using Operations.induct with
  | empty => simp only [List.nil_append, operationCount]; rw [Count.zero_add]
  | witness m c ops ih | assert e ops ih | lookup l ops ih | interact i ops ih
  | subcircuit s ops ih =>
      simp only [List.cons_append, operationCount, ih, Count.add_assoc]

theorem nestedListCount_append (xs ys : List (NestedOperations F)) :
    nestedListCount (xs ++ ys) = nestedListCount xs + nestedListCount ys := by
  induction xs with
  | nil => simp [nestedListCount, Count.zero_add]
  | cons x xs ih =>
      simp [nestedListCount, ih, Count.add_assoc]

theorem operationCount_toNested [Field F] (ops : Operations F) :
    nestedListCount ops.toNested = operationCount ops := by
  induction ops using Operations.induct with
  | empty =>
      simp [Operations.toNested, nestedListCount, operationCount]
  | witness m c ops ih =>
      simp [Operations.toNested, nestedListCount, nestedCount, operationCount, ih]
  | assert e ops ih =>
      simp [Operations.toNested, nestedListCount, nestedCount, operationCount, ih]
  | lookup l ops ih =>
      simp [Operations.toNested, nestedListCount, nestedCount, operationCount, ih]
  | interact i ops ih =>
      simp [Operations.toNested, nestedListCount, nestedCount, operationCount, ih]
  | subcircuit s ops ih =>
      simp [Operations.toNested, nestedListCount, operationCount, ih]

end Lemmas

/-! ## Compositional cost and R1CS certificates

`CostIs c K` / `IsR1CSCirc c` package the *offset-independent* facts that the
circuit `c` has operation count `K`, resp. that every assert in `c` is a single
R1CS row, at every offset. Both are preserved by the monad and loop combinators
and grounded at the leaves (`witnessVector`, `assertZero`, subcircuit/assertion
invocations), so a circuit's cost / R1CS certificate can be assembled by
structural recursion that mirrors the circuit's own shape — no `native_decide`
(which would pull the Lean compiler into the trusted base) and no unfolding of
the whole operation forest. -/

open Lemmas

variable [Field F] {α β : Type}

/-! ### `CostIs`: offset-independent operation count -/

/-- Count of a flattened `List.ofFn` whose pieces all have the same count `K`. -/
theorem operationCount_flatten_ofFn_const {m : ℕ} (g : Fin m → Operations F) (K : Count)
    (h : ∀ i, operationCount (g i) = K) :
    operationCount (List.ofFn g).flatten = ⟨m * K.allocations, m * K.constraints⟩ := by
  induction m with
  | zero =>
      simp only [List.ofFn_zero, List.flatten_nil, operationCount, Nat.zero_mul]
      rfl
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons, operationCount_append, h 0,
        ih (fun i => g i.succ) (fun i => h i.succ)]
      show (⟨K.allocations + k * K.allocations, K.constraints + k * K.constraints⟩ : Count) = _
      rw [Nat.add_comm K.allocations, Nat.add_comm K.constraints,
        ← Nat.succ_mul, ← Nat.succ_mul]

/-- `c` produces exactly `K` allocations/constraints at every offset. -/
def CostIs (c : Circuit F α) (K : Count) : Prop :=
  ∀ n, operationCount (c.operations n) = K

/-- A circuit family has fixed cost when every symbolic input instantiation has
the same offset-independent operation count. This is the proposition the trusted
challenge `mainCost` statements should expose. -/
def circuitCost {Input : TypeMap} [ProvableType Input]
    (main : Var Input F → Circuit F α) (K : Count) : Prop :=
  ∀ input : Var Input F, CostIs (main input) K

theorem CostIs.pure (a : α) : CostIs (pure a : Circuit F α) Count.zero := by
  intro n; rw [Circuit.pure_operations_eq]; rfl

theorem CostIs.bind {f : Circuit F α} {g : α → Circuit F β} {K₁ K₂ : Count}
    (hf : CostIs f K₁) (hg : ∀ a, CostIs (g a) K₂) :
    CostIs (f >>= g) (K₁ + K₂) := by
  intro n
  rw [Circuit.bind_operations_eq, operationCount_append, hf n, hg _ _]

theorem CostIs.map {f : Circuit F α} {g : α → β} {K : Count} (hf : CostIs f K) :
    CostIs (g <$> f) K := by
  intro n; rw [Circuit.map_operations_eq]; exact hf n

theorem CostIs.witnessVector (m : ℕ) (c : ProverEnvironment F → Vector F m) :
    CostIs (Circuit.witnessVector m c) ⟨m, 0⟩ := by
  intro n; rfl

theorem CostIs.witnessVar (c : ProverEnvironment F → F) :
    CostIs (Circuit.witnessVar c) ⟨1, 0⟩ := by
  intro n; rfl

theorem CostIs.witnessField (c : ProverEnvironment F → F) :
    CostIs (Circuit.witnessField c) ⟨1, 0⟩ :=
  CostIs.bind (CostIs.witnessVar c) (fun _ => CostIs.pure _)

theorem CostIs.assertZero (e : Expression F) : CostIs (Circuit.assertZero e) ⟨0, 1⟩ := by
  intro n; rfl

/-- Invoking a `FormalCircuit` as a subcircuit costs exactly its `main`'s count. -/
theorem CostIs.subcircuit {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuit F Input Output} {b : Var Input F} {K : Count}
    (h : ∀ n, operationCount ((circuit.main b).operations n) = K) :
    CostIs (subcircuit circuit b) K := by
  intro n
  show operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K
  have hz : operationCount [Operation.subcircuit (circuit.toSubcircuit n b)]
      = nestedCount (circuit.toSubcircuit n b).ops := by
    show nestedCount _ + operationCount ([] : Operations F) = nestedCount _
    rw [show operationCount ([] : Operations F) = Count.zero from rfl, Count.add_zero]
  rw [hz]
  show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩) = K
  rw [show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩)
        = nestedListCount ((circuit.main b).operations n).toNested from rfl,
      operationCount_toNested]
  exact h n

/-- Same as `CostIs.subcircuit`, for a `FormalAssertion`. -/
theorem CostIs.assertion {Input : TypeMap} [ProvableType Input]
    {circuit : FormalAssertion F Input} {b : Var Input F} {K : Count}
    (h : ∀ n, operationCount ((circuit.main b).operations n) = K) :
    CostIs (assertion circuit b) K := by
  intro n
  show operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K
  have hz : operationCount [Operation.subcircuit (circuit.toSubcircuit n b)]
      = nestedCount (circuit.toSubcircuit n b).ops := by
    show nestedCount _ + operationCount ([] : Operations F) = nestedCount _
    rw [show operationCount ([] : Operations F) = Count.zero from rfl, Count.add_zero]
  rw [hz]
  show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩) = K
  rw [show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩)
        = nestedListCount ((circuit.main b).operations n).toNested from rfl,
      operationCount_toNested]
  exact h n

theorem CostIs.forEach {m : ℕ} [Inhabited α] {xs : Vector α m} {body : α → Circuit F Unit}
    {constant : Circuit.ConstantLength body} {K : Count}
    (h : ∀ a n, operationCount ((body a).operations n) = K) :
    CostIs (Circuit.forEach xs body constant) ⟨m * K.allocations, m * K.constraints⟩ := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationCount_flatten_ofFn_const _ K (fun i => h _ _)

theorem CostIs.mapFinRange {m : ℕ} [NeZero m] {body : Fin m → Circuit F β}
    {constant : Circuit.ConstantLength body} {K : Count}
    (h : ∀ i n, operationCount ((body i).operations n) = K) :
    CostIs (Circuit.mapFinRange m body constant) ⟨m * K.allocations, m * K.constraints⟩ := by
  intro n
  rw [Circuit.mapFinRange.operations_eq]
  exact operationCount_flatten_ofFn_const _ K (fun i => h _ _)

theorem CostIs.foldlRange {m : ℕ} [Inhabited β] {init : β} {body : β → Fin m → Circuit F β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2} {K : Count}
    (h : ∀ s i n, operationCount ((body s i).operations n) = K) :
    CostIs (Circuit.foldlRange m init body constant) ⟨m * K.allocations, m * K.constraints⟩ := by
  intro n
  rw [Circuit.foldlRange.operations_eq]
  exact operationCount_flatten_ofFn_const _ K (fun i => h _ _ _)

/-- Bridge to `circuitCount`: an offset-independent count fixes `circuitCount`. -/
theorem circuitCount_eq_of_CostIs {c : Circuit F α} {K : Count} (h : CostIs c K) :
    circuitCount c = K := h 0

/-! ### `IsR1CSCirc`: every assert is a single R1CS row -/

/-- Flatten of a `List.ofFn` whose pieces are all single-row R1CS is single-row R1CS. -/
theorem operationsIsR1CS_flatten_ofFn {m : ℕ} (g : Fin m → Operations F)
    (h : ∀ i, operationsIsR1CS (g i)) :
    operationsIsR1CS (List.ofFn g).flatten := by
  induction m with
  | zero => simp [List.ofFn_zero, List.flatten_nil]
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons, operationsIsR1CS_append]
      exact ⟨h 0, ih (fun i => g i.succ) (fun i => h i.succ)⟩

/-- `c`'s operations are single-row R1CS at every offset. -/
def IsR1CSCirc (c : Circuit F α) : Prop :=
  ∀ n, operationsIsR1CS (c.operations n)

theorem IsR1CSCirc.pure (a : α) : IsR1CSCirc (pure a : Circuit F α) := by
  intro n; rw [Circuit.pure_operations_eq]; trivial

theorem IsR1CSCirc.bind {f : Circuit F α} {g : α → Circuit F β}
    (hf : IsR1CSCirc f) (hg : ∀ a, IsR1CSCirc (g a)) : IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, operationsIsR1CS_append]
  exact ⟨hf n, hg _ _⟩

theorem IsR1CSCirc.map {f : Circuit F α} {g : α → β} (hf : IsR1CSCirc f) :
    IsR1CSCirc (g <$> f) := by
  intro n; rw [Circuit.map_operations_eq]; exact hf n

theorem IsR1CSCirc.witnessVector (m : ℕ) (c : ProverEnvironment F → Vector F m) :
    IsR1CSCirc (Circuit.witnessVector m c) := by
  intro n; trivial

theorem IsR1CSCirc.witnessVar (c : ProverEnvironment F → F) :
    IsR1CSCirc (Circuit.witnessVar c) := by
  intro n; trivial

theorem IsR1CSCirc.witnessField (c : ProverEnvironment F → F) :
    IsR1CSCirc (Circuit.witnessField c) :=
  IsR1CSCirc.bind (IsR1CSCirc.witnessVar c) (fun _ => IsR1CSCirc.pure _)

theorem IsR1CSCirc.assertZero {e : Expression F} (h : isR1CSRow e) :
    IsR1CSCirc (Circuit.assertZero e) := by
  intro n
  show operationsIsR1CS [Operation.assert e]
  exact ⟨h, trivial⟩

/-- Invoking a `FormalCircuit` as a subcircuit is single-row R1CS when its
`main` is. -/
theorem IsR1CSCirc.subcircuit {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuit F Input Output} {b : Var Input F}
    (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n)) :
    IsR1CSCirc (subcircuit circuit b) := by
  intro n
  show operationsIsR1CS [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsR1CS (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (operationsIsR1CS_iff_toFlat _).mp (h n)

/-- Same as `IsR1CSCirc.subcircuit`, for a `FormalAssertion`. -/
theorem IsR1CSCirc.assertion {Input : TypeMap} [ProvableType Input]
    {circuit : FormalAssertion F Input} {b : Var Input F}
    (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n)) :
    IsR1CSCirc (assertion circuit b) := by
  intro n
  show operationsIsR1CS [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsR1CS (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (operationsIsR1CS_iff_toFlat _).mp (h n)

theorem IsR1CSCirc.forEach {m : ℕ} [Inhabited α] {xs : Vector α m} {body : α → Circuit F Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ a n, operationsIsR1CS ((body a).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h _ _)

theorem IsR1CSCirc.mapFinRange {m : ℕ} [NeZero m] {body : Fin m → Circuit F β}
    {constant : Circuit.ConstantLength body}
    (h : ∀ i n, operationsIsR1CS ((body i).operations n)) :
    IsR1CSCirc (Circuit.mapFinRange m body constant) := by
  intro n
  rw [Circuit.mapFinRange.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h _ _)

theorem IsR1CSCirc.foldlRange {m : ℕ} [Inhabited β] {init : β} {body : β → Fin m → Circuit F β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2}
    (h : ∀ s i n, operationsIsR1CS ((body s i).operations n)) :
    IsR1CSCirc (Circuit.foldlRange m init body constant) := by
  intro n
  rw [Circuit.foldlRange.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h _ _ _)

/-- A `Fin.foldl` preserves an invariant `P` on the accumulator. -/
theorem finFoldl_invariant {γ : Type*} {m : ℕ} (P : γ → Prop) :
    ∀ (f : γ → Fin m → γ) (init : γ), P init → (∀ acc i, P acc → P (f acc i)) →
      P (Fin.foldl m f init) := by
  induction m with
  | zero => intro f init h _; simpa using h
  | succ k ih =>
      intro f init hinit hf
      rw [Fin.foldl_succ]
      exact ih _ _ (hf init 0 hinit) (fun acc i h => hf acc i.succ h)

/-- Single-row R1CS of a `foldlRange`, threading an invariant `P` on the
accumulator (e.g. "the state is affine"). The body need only be R1CS for
accumulators satisfying `P`, and each step must preserve `P` on its output. -/
theorem IsR1CSCirc.foldlRange_inv {m : ℕ} [Inhabited β] {init : β} {body : β → Fin m → Circuit F β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2}
    (P : β → Prop) (hinit : P init)
    (hbody : ∀ s i, P s → IsR1CSCirc (body s i))
    (hstep : ∀ s (i : Fin m) n, P s → P ((body s i).output n)) :
    IsR1CSCirc (Circuit.foldlRange m init body constant) := by
  intro n
  rw [Circuit.foldlRange.operations_eq]
  apply operationsIsR1CS_flatten_ofFn
  intro i
  refine (hbody _ i ?_) _
  show P (Circuit.FoldlM.foldlAcc n (Vector.finRange m) body init i)
  rw [Circuit.FoldlM.foldlAcc]
  apply finFoldl_invariant P _ _ hinit
  intro acc j hacc
  exact hstep acc _ _ hacc

/-- A sequential R1CS bind where the continuation only needs to be R1CS for the
*actual* output of `f` (e.g. a `varFromOffset` witness vector), not for every
possible value. This is what lets us thread affineness of witnessed outputs. -/
theorem IsR1CSCirc.bind_out {f : Circuit F α} {g : α → Circuit F β}
    (hf : IsR1CSCirc f)
    (hg : ∀ n, IsR1CSCirc (g (f.output n))) :
    IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, operationsIsR1CS_append]
  exact ⟨hf n, (hg n) (n + f.localLength n)⟩

/-- Bridge to `isR1CSCircuit`: an offset-independent certificate gives the
offset-0 statement. -/
theorem isR1CSCircuit_of_IsR1CSCirc {c : Circuit F α} (h : IsR1CSCirc c) :
    isR1CSCircuit c := h 0

/-! ## Affine expressions and per-assert R1CS certificates

`Affine e` means `e` has structural degree ≤ 1 (no genuine degree-2 product).
The atoms of arithmetic circuits — witness variables, constants, and
field-scaled combinations of them — are affine, and affineness propagates through
`+`, `-`, constant scaling, and bounded folds. An assert built as `C - A*B`,
`C + A*B`, or `A*B` from affine `A, B, C` is then a single R1CS row — exactly the
`isR1CSRow e` hypothesis that `IsR1CSCirc.assertZero` consumes. These are the
reusable leaves used to discharge the per-assert obligations of any gadget. -/

omit [Field F] in
@[simp] theorem degree_var (v : Variable F) : degree (Expression.var v) = 1 := rfl
omit [Field F] in
@[simp] theorem degree_const (c : F) : degree (Expression.const c) = 0 := rfl

omit [Field F] in
theorem degree_add (a b : Expression F) : degree (a + b) = max (degree a) (degree b) := rfl
omit [Field F] in
theorem degree_mul (a b : Expression F) : degree (a * b) = degree a + degree b := rfl

theorem degree_neg (a : Expression F) : degree (-a) = degree a := by
  show degree (Expression.mul (Expression.const (-1)) a) = degree a
  simp only [degree, Nat.zero_add]

theorem degree_sub (a b : Expression F) : degree (a - b) = max (degree a) (degree b) := by
  show degree (a + -b) = _
  rw [degree_add, degree_neg]

omit [Field F] in
theorem degree_fconst_mul (c : F) (a : Expression F) : degree (c * a) = degree a := by
  show degree (Expression.mul (Expression.const c) a) = degree a
  simp only [degree, Nat.zero_add]

omit [Field F] in
theorem degree_mul_fconst (a : Expression F) (c : F) : degree (a * c) = degree a := by
  show degree (Expression.mul a (Expression.const c)) = degree a
  simp only [degree, Nat.add_zero]

omit [Field F] in
theorem Affine.const (c : F) : Affine (Expression.const c) := by simp [Affine]
omit [Field F] in
theorem Affine.var (v : Variable F) : Affine (Expression.var v) := by simp [Affine]
omit [Field F] in
theorem Affine.add {a b : Expression F} (ha : Affine a) (hb : Affine b) : Affine (a + b) := by
  simp only [Affine, degree_add, Nat.max_le]; exact ⟨ha, hb⟩
theorem Affine.neg {a : Expression F} (ha : Affine a) : Affine (-a) := by
  simp only [Affine, degree_neg]; exact ha
theorem Affine.sub {a b : Expression F} (ha : Affine a) (hb : Affine b) : Affine (a - b) := by
  simp only [Affine, degree_sub, Nat.max_le]; exact ⟨ha, hb⟩
omit [Field F] in
theorem Affine.fconst_mul (c : F) {a : Expression F} (ha : Affine a) : Affine (c * a) := by
  simp only [Affine, degree_fconst_mul]; exact ha
omit [Field F] in
theorem Affine.mul_fconst {a : Expression F} (c : F) (ha : Affine a) : Affine (a * c) := by
  simp only [Affine, degree_mul_fconst]; exact ha
theorem Affine.zero : Affine (0 : Expression F) := by
  show degree (Expression.const 0) ≤ 1; simp
omit [Field F] in
/-- A degree-≤1 form times a degree-0 (constant) form is affine. -/
theorem Affine.mul_deg0 {a b : Expression F} (ha : Affine a) (hb : degree b = 0) :
    Affine (a * b) := by
  simp only [Affine, degree_mul, hb, Nat.add_zero]; exact ha

omit [Field F] in
/-- Affineness is preserved by a `Fin.foldl` that adds an affine increment each step. -/
theorem affine_finFoldl (m : ℕ) :
    ∀ (step : Expression F → ℕ → Expression F) (init : Expression F),
    Affine init → (∀ acc i, Affine acc → Affine (step acc i)) →
    Affine (Fin.foldl m (fun acc (i : Fin m) => step acc i.val) init) := by
  induction m with
  | zero => intro step init hinit _; simpa using hinit
  | succ k ih =>
      intro step init hinit hstep
      rw [Fin.foldl_succ]
      exact ih (fun acc j => step acc (j + 1)) (step init 0) (hstep init 0 hinit)
        (fun acc i h => hstep acc (i + 1) h)

omit [Field F] in
/-- `Fin`-indexed version (the loop body may use the index's bound). -/
theorem affine_finFoldl' {m : ℕ} (step : Expression F → Fin m → Expression F) (init : Expression F)
    (hinit : Affine init) (hstep : ∀ acc i, Affine acc → Affine (step acc i)) :
    Affine (Fin.foldl m step init) := by
  have key := affine_finFoldl m (fun acc j => if h : j < m then step acc ⟨j, h⟩ else acc) init hinit
    (fun acc i h => by dsimp only; split
                       · exact hstep acc _ h
                       · exact h)
  convert key using 2
  funext acc i
  dsimp only
  rw [dif_pos i.isLt]

omit [Field F] in
/-- An affine expression carries no degree-2 products. -/
theorem r1csProducts_of_affine {e : Expression F} (h : Affine e) : r1csProducts e = some 0 := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add a b iha ihb =>
      simp only [Affine, degree, Nat.max_le] at h
      simp only [r1csProducts, iha h.1, ihb h.2]
  | mul a b iha ihb =>
      simp only [Affine, degree] at h ⊢
      simp only [r1csProducts]
      rcases Nat.eq_zero_or_pos (degree a) with ha0 | ha1
      · rw [if_pos ha0]; exact ihb (by simp only [Affine]; omega)
      · have hb0 : degree b = 0 := by omega
        rw [if_neg (by omega), if_pos hb0]; exact iha (by simp only [Affine]; omega)

omit [Field F] in
theorem r1csProducts_add (a b : Expression F) :
    r1csProducts (a + b) =
      (match r1csProducts a, r1csProducts b with
        | some m, some n => some (m + n) | _, _ => none) := rfl

theorem r1csProducts_neg (a : Expression F) : r1csProducts (-a) = r1csProducts a := rfl

omit [Field F] in
/-- The product of two affine forms is a single rank-1 row term. -/
theorem r1csProducts_mul_affine {a b : Expression F} (ha : Affine a) (hb : Affine b) :
    r1csProducts (a * b) = some 0 ∨ r1csProducts (a * b) = some 1 := by
  show r1csProducts (Expression.mul a b) = _ ∨ _
  simp only [r1csProducts]
  by_cases ha0 : degree a = 0
  · left; rw [if_pos ha0]; exact r1csProducts_of_affine hb
  · by_cases hb0 : degree b = 0
    · left; rw [if_neg ha0, if_pos hb0]; exact r1csProducts_of_affine ha
    · right; rw [if_neg ha0, if_neg hb0, if_pos ⟨ha, hb⟩]

omit [Field F] in
/-- Reduce an `isR1CSRow` goal to a bound on the product count. -/
theorem isR1CSRow_of_r1csProducts {e : Expression F} {k : ℕ}
    (h : r1csProducts e = some k) (hk : k ≤ 1) : isR1CSRow e := by
  unfold isR1CSRow; rw [h]; exact hk

omit [Field F] in
theorem isR1CSRow_of_affine {e : Expression F} (h : Affine e) : isR1CSRow e :=
  isR1CSRow_of_r1csProducts (r1csProducts_of_affine h) (by omega)

/-- `C - A*B` with all of `A, B, C` affine is a single R1CS row (`⟨A,z⟩·⟨B,z⟩ = ⟨C,z⟩`). -/
theorem isR1CSRow_sub_mul {C A B : Expression F}
    (hC : Affine C) (hA : Affine A) (hB : Affine B) : isR1CSRow (C - A * B) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (C + -(A * B)) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (C + -(A * B)) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)

omit [Field F] in
/-- `C + A*B` with all of `A, B, C` affine is a single R1CS row. -/
theorem isR1CSRow_add_mul {C A B : Expression F}
    (hC : Affine C) (hA : Affine A) (hB : Affine B) : isR1CSRow (C + A * B) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by rw [r1csProducts_add, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by rw [r1csProducts_add, r1csProducts_of_affine hC, h]) (by omega)

omit [Field F] in
/-- A bare product `A*B` of two affine forms is a single R1CS row (`A·B = 0`). -/
theorem isR1CSRow_mul {A B : Expression F} (hA : Affine A) (hB : Affine B) :
    isR1CSRow (A * B) := by
  rcases r1csProducts_mul_affine hA hB with h | h <;>
    exact isR1CSRow_of_r1csProducts h (by omega)

/-! ### Affineness of witness vectors and symbolic inputs -/

/-- Every flattened element of a symbolic circuit value is affine. This is the
right precondition for R1CS certification over arbitrary symbolic inputs, and the
right postcondition for circuit outputs: constants, variables, and linear forms
are accepted; quadratic expressions are not. -/
def AffineProvable {Input : TypeMap} [ProvableType Input] (input : Var Input F) : Prop :=
  ∀ i (hi : i < size Input),
    Affine ((toElements (M := Input) input)[i])

/-- The output of a circuit is affine at every offset. A circuit that returns a
nonlinear expression without constraining/witnessing it is not an R1CS circuit,
even if its operation list is empty. -/
def AffineOutput {Output : TypeMap} [ProvableType Output]
    (c : Circuit F (Var Output F)) : Prop :=
  ∀ n, AffineProvable (c.output n)

/-- A circuit family (the `main` of a formal circuit) is single-row R1CS when
every affine symbolic input instantiation has offset-independent single-row R1CS
operations and affine outputs. -/
def isR1CS {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (main : Var Input F → Circuit F (Var Output F)) : Prop :=
  ∀ input : Var Input F, AffineProvable input → IsR1CSCirc (main input) ∧ AffineOutput (main input)

theorem isR1CS_of_IsR1CSCirc {Input Output : TypeMap} [ProvableType Input]
    [ProvableType Output] {main : Var Input F → Circuit F (Var Output F)}
    (hops : ∀ input : Var Input F, AffineProvable input → IsR1CSCirc (main input))
    (hout : ∀ input : Var Input F, AffineProvable input → AffineOutput (main input)) :
    isR1CS main :=
  fun input hinput => ⟨hops input hinput, hout input hinput⟩

/-- Every entry of a `fields m` variable vector is affine (degree ≤ 1). All the
witness rows and symbolic inputs of arithmetic circuits satisfy this. -/
def AffineW {m : ℕ} (v : Var (fields m) F) : Prop := ∀ i (hi : i < m), Affine v[i]

omit [Field F] in
theorem AffineProvable.affineW {m : ℕ} {v : Var (fields m) F} (h : AffineProvable v) :
    AffineW v := by
  intro i hi
  simpa [AffineProvable, circuit_norm, explicit_provable_type] using h i hi

omit [Field F] in
theorem AffineW.affineProvable {m : ℕ} {v : Var (fields m) F} (h : AffineW v) :
    AffineProvable v := by
  intro i hi
  simpa [AffineProvable, circuit_norm, explicit_provable_type] using h i hi

omit [Field F] in
theorem affineProvable_unit (u : Var unit F) : AffineProvable u := by
  intro i hi
  have hsz : size unit = 0 := rfl
  have : False := by omega
  exact False.elim this

theorem affineOutput_unit (c : Circuit F (Var unit F)) : AffineOutput c :=
  fun _ => affineProvable_unit _

theorem affineOutput_of_affineW {m : ℕ} {c : Circuit F (Var (fields m) F)}
    (h : ∀ n, AffineW (c.output n)) : AffineOutput c :=
  fun n => (h n).affineProvable

omit [Field F] in
theorem AffineW.left_of_append {m n : ℕ}
    {a : fields m (Expression F)} {b : fields n (Expression F)}
    (h : AffineW (a ++ b : fields (m + n) (Expression F))) : AffineW a := by
  intro i hi
  have h' := h i (by omega)
  rw [Vector.getElem_append] at h'
  split at h'
  · exact h'
  · omega

omit [Field F] in
theorem AffineW.right_of_append {m n : ℕ}
    {a : fields m (Expression F)} {b : fields n (Expression F)}
    (h : AffineW (a ++ b : fields (m + n) (Expression F))) : AffineW b := by
  intro i hi
  have h' := h (m + i) (by omega)
  rw [Vector.getElem_append] at h'
  split at h'
  · omega
  · simpa [Nat.add_sub_cancel_left] using h'

/-- Every entry of a `fields m` variable vector is a *constant* (degree 0). -/
def ConstW {m : ℕ} (v : Var (fields m) F) : Prop := ∀ i (hi : i < m), degree v[i] = 0

omit [Field F] in
theorem ConstW.affineW {m : ℕ} {v : Var (fields m) F} (h : ConstW v) : AffineW v := by
  intro i hi; have := h i hi; simp only [Affine]; omega

omit [Field F] in
theorem affine_varFromOffset (m n i : ℕ) (hi : i < m) :
    Affine ((varFromOffset (fields m) n : Var (fields m) F)[i]) := by
  rw [show (varFromOffset (fields m) n : Var (fields m) F)[i] = Expression.var ⟨n + i⟩ from by
    simp only [varFromOffset, instProvableTypeFields, size, Vector.getElem_mapRange]]
  exact Affine.var _

/-- The fresh witness vector produced by `witnessVector m c` is affine at every offset. -/
theorem affineW_witnessVector_output (m : ℕ) (c : ProverEnvironment F → Vector F m) (n : ℕ) :
    AffineW ((Circuit.witnessVector m c).output n) :=
  fun i hi => affine_varFromOffset m n i hi

omit [Field F] in
theorem affineW_varFromOffset (m n : ℕ) :
    AffineW (varFromOffset (fields m) n : Var (fields m) F) :=
  fun i hi => affine_varFromOffset m n i hi

omit [Field F] in
theorem affineProvable_varFromOffset {Input : TypeMap} [ProvableType Input] (offset : ℕ) :
    AffineProvable (varFromOffset Input offset : Var Input F) := by
  intro i hi
  rw [show (toElements (M := Input)
        (varFromOffset Input offset : Var Input F))[i] =
        Expression.var ⟨offset + i⟩ from by
    simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]]
  exact Affine.var _

theorem affine_witnessField_output (c : ProverEnvironment F → F) (n : ℕ) :
    Affine ((Circuit.witnessField c).output n) := Affine.var _

omit [Field F] in
/-- A `mapRange` of bare variables is affine. -/
theorem affineW_mapRange_var {m : ℕ} (f : ℕ → ℕ) :
    AffineW (Vector.mapRange m (fun i => Expression.var ⟨f i⟩) : Var (fields m) F) := by
  intro j hj; rw [Vector.getElem_mapRange]; exact Affine.var _

end Challenge.CostR1CS
