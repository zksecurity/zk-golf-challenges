import Clean.Circuit

/-!
Reusable structural lemmas for `Circuit.ComputableWitnesses`.

These facts keep instance files focused on the witness generators that are
specific to the gadget, while the loop/subcircuit bookkeeping lives here.
-/

namespace Challenge.Utils.ComputableWitnessLemmas

variable {F : Type} [Field F]

namespace Condition

def onlySubcircuits (condition : Condition F) : Condition F where
  subcircuit n _ s := FlatOperation.forAll n condition s.ops.toFlat

end Condition

namespace Operations

theorem forAllFlat_of_forAll_ignoreSubcircuit_and_subcircuits
    {ops : Operations F} {n : ℕ} {condition : Condition F}
    (h_parent : ops.forAll n condition.ignoreSubcircuit)
    (h_subcircuits : ops.forAll n (Condition.onlySubcircuits condition)) :
    ops.forAllFlat n condition := by
  induction ops using Operations.induct generalizing n with
  | empty =>
    simp [Operations.forAllFlat, Operations.forAll]
  | witness m c ops ih =>
    unfold Operations.forAllFlat
    rw [Operations.forAll] at h_parent h_subcircuits ⊢
    exact ⟨h_parent.1, ih h_parent.2 h_subcircuits.2⟩
  | assert e ops ih =>
    unfold Operations.forAllFlat
    rw [Operations.forAll] at h_parent h_subcircuits ⊢
    exact ⟨h_parent.1, ih h_parent.2 h_subcircuits.2⟩
  | lookup l ops ih =>
    unfold Operations.forAllFlat
    rw [Operations.forAll] at h_parent h_subcircuits ⊢
    exact ⟨h_parent.1, ih h_parent.2 h_subcircuits.2⟩
  | interact i ops ih =>
    unfold Operations.forAllFlat
    rw [Operations.forAll] at h_parent h_subcircuits ⊢
    exact ⟨h_parent.1, ih h_parent.2 h_subcircuits.2⟩
  | subcircuit s ops ih =>
    unfold Operations.forAllFlat
    rw [Operations.forAll] at h_parent h_subcircuits ⊢
    exact ⟨h_subcircuits.1, ih h_parent.2 h_subcircuits.2⟩

end Operations

theorem eval_mem_varFromOffset_fields_of_agreesBelow {m offset k : ℕ}
    {env env' : ProverEnvironment F}
    (h_agree : env.AgreesBelow k env') (hk : offset + m ≤ k) :
    ∀ a ∈ (varFromOffset (fields m) offset : Var (fields m) F),
      Expression.eval env.toEnvironment a = Expression.eval env'.toEnvironment a := by
  intro a ha
  rw [ProvableType.varFromOffset_fields] at ha
  simp only [Vector.mem_iff_getElem] at ha
  rcases ha with ⟨i, hi, hget⟩
  rw [← hget]
  simp only [Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)

namespace FormalCircuitBase

def computableWitnessCondition {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) : Condition F where
  witness n _ compute :=
    env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env'

namespace FlatOperation

/--
Structural form of the computable-witness condition for flat operations.

This is intentionally shaped like `UsesLocalWitnessesCompleteness`: assertions,
lookups, and interactions are skipped definitionally, while witnesses produce the
only real proof obligation.
-/
@[circuit_norm]
def StructuralComputableWitnesses {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) (offset : ℕ) :
    List (FlatOperation F) → Prop
  | [] => True
  | .witness m compute :: ops =>
      (env.AgreesBelow offset env' → eval env input = eval env' input →
        compute env = compute env') ∧
      StructuralComputableWitnesses input env env' (m + offset) ops
  | .assert _ :: ops =>
      StructuralComputableWitnesses input env env' offset ops
  | .lookup _ :: ops =>
      StructuralComputableWitnesses input env env' offset ops
  | .interact _ :: ops =>
      StructuralComputableWitnesses input env env' offset ops

theorem forAll_of_structuralComputableWitnesses {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) :
    ∀ {ops : List (FlatOperation F)} {offset : ℕ},
      StructuralComputableWitnesses input env env' offset ops →
      FlatOperation.forAll offset (computableWitnessCondition input env env') ops
  | [], offset, h => by
      simp [FlatOperation.forAll]
  | .witness m compute :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, FlatOperation.forAll] at h ⊢
      exact ⟨h.1, forAll_of_structuralComputableWitnesses input env env' h.2⟩
  | .assert e :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, FlatOperation.forAll] at h ⊢
      exact ⟨trivial, forAll_of_structuralComputableWitnesses input env env' h⟩
  | .lookup l :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, FlatOperation.forAll] at h ⊢
      exact ⟨trivial, forAll_of_structuralComputableWitnesses input env env' h⟩
  | .interact i :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, FlatOperation.forAll] at h ⊢
      exact ⟨trivial, forAll_of_structuralComputableWitnesses input env env' h⟩

theorem structuralComputableWitnesses_iff_forAll {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) :
    ∀ {ops : List (FlatOperation F)} {offset : ℕ},
      StructuralComputableWitnesses input env env' offset ops ↔
        FlatOperation.forAll offset (computableWitnessCondition input env env') ops
  | [], offset => by
      simp [StructuralComputableWitnesses, FlatOperation.forAll]
  | .witness m compute :: ops, offset => by
      simp [StructuralComputableWitnesses, FlatOperation.forAll,
        computableWitnessCondition, structuralComputableWitnesses_iff_forAll input env env']
  | .assert e :: ops, offset => by
      simp [StructuralComputableWitnesses, FlatOperation.forAll,
        computableWitnessCondition, structuralComputableWitnesses_iff_forAll input env env']
  | .lookup l :: ops, offset => by
      simp [StructuralComputableWitnesses, FlatOperation.forAll,
        computableWitnessCondition, structuralComputableWitnesses_iff_forAll input env env']
  | .interact i :: ops, offset => by
      simp [StructuralComputableWitnesses, FlatOperation.forAll,
        computableWitnessCondition, structuralComputableWitnesses_iff_forAll input env env']

end FlatOperation

namespace Operations

/--
Structural computable-witness condition for nested operations.

It has the same witness obligation as `computableWitnessCondition`, but keeps
subcircuits as subgoals instead of flattening them immediately.
-/
@[circuit_norm]
def structuralComputableWitnessCondition {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) : Condition F where
  witness n _ compute :=
    env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env'
  subcircuit n _ s :=
    FlatOperation.StructuralComputableWitnesses input env env' n s.ops.toFlat

/--
Structural form of the computable-witness condition for nested operations.

This is the compositional predicate we want to prove about circuits. It is an
ordinary `Operations.forAll`, so the generic `append`, `bind`, and loop lemmas
can reduce it to smaller circuits.
-/
@[circuit_norm]
def StructuralComputableWitnesses {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) (offset : ℕ) :
    Operations F → Prop
  | [] => True
  | .witness m compute :: ops =>
      (env.AgreesBelow offset env' → eval env input = eval env' input →
        compute env = compute env') ∧
      StructuralComputableWitnesses input env env' (m + offset) ops
  | .assert _ :: ops =>
      StructuralComputableWitnesses input env env' offset ops
  | .lookup _ :: ops =>
      StructuralComputableWitnesses input env env' offset ops
  | .interact _ :: ops =>
      StructuralComputableWitnesses input env env' offset ops
  | .subcircuit s :: ops =>
      FlatOperation.StructuralComputableWitnesses input env env' offset s.ops.toFlat ∧
      StructuralComputableWitnesses input env env' (s.localLength + offset) ops

theorem structuralComputableWitnesses_iff_forAll
    {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) :
    ∀ {ops : Operations F} {offset : ℕ},
      StructuralComputableWitnesses input env env' offset ops ↔
        ops.forAll offset (structuralComputableWitnessCondition input env env')
  | [], offset => by
      simp [StructuralComputableWitnesses, Operations.forAll]
  | .witness m compute :: ops, offset => by
      simp [StructuralComputableWitnesses, structuralComputableWitnessCondition,
        Operations.forAll, structuralComputableWitnesses_iff_forAll input env env']
  | .assert e :: ops, offset => by
      simp [StructuralComputableWitnesses, structuralComputableWitnessCondition,
        Operations.forAll, structuralComputableWitnesses_iff_forAll input env env']
  | .lookup l :: ops, offset => by
      simp [StructuralComputableWitnesses, structuralComputableWitnessCondition,
        Operations.forAll, structuralComputableWitnesses_iff_forAll input env env']
  | .interact i :: ops, offset => by
      simp [StructuralComputableWitnesses, structuralComputableWitnessCondition,
        Operations.forAll, structuralComputableWitnesses_iff_forAll input env env']
  | .subcircuit s :: ops, offset => by
      simp [StructuralComputableWitnesses, structuralComputableWitnessCondition,
        Operations.forAll, structuralComputableWitnesses_iff_forAll input env env']

private theorem forAll_ignoreSubcircuit_of_structuralComputableWitnesses
    {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) :
    ∀ {ops : Operations F} {offset : ℕ},
      StructuralComputableWitnesses input env env' offset ops →
      ops.forAll offset (computableWitnessCondition input env env').ignoreSubcircuit
  | [], offset, h => by
      simp [Operations.forAll]
  | .witness m compute :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, computableWitnessCondition,
        Condition.ignoreSubcircuit, Operations.forAll] at h ⊢
      exact ⟨h.1, forAll_ignoreSubcircuit_of_structuralComputableWitnesses input env env' h.2⟩
  | .assert e :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, computableWitnessCondition,
        Condition.ignoreSubcircuit, Operations.forAll] at h ⊢
      exact ⟨trivial, forAll_ignoreSubcircuit_of_structuralComputableWitnesses input env env' h⟩
  | .lookup l :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, computableWitnessCondition,
        Condition.ignoreSubcircuit, Operations.forAll] at h ⊢
      exact ⟨trivial, forAll_ignoreSubcircuit_of_structuralComputableWitnesses input env env' h⟩
  | .interact i :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, computableWitnessCondition,
        Condition.ignoreSubcircuit, Operations.forAll] at h ⊢
      exact ⟨trivial, forAll_ignoreSubcircuit_of_structuralComputableWitnesses input env env' h⟩
  | .subcircuit s :: ops, offset, h => by
      simp only [StructuralComputableWitnesses, computableWitnessCondition,
        Condition.ignoreSubcircuit, Operations.forAll] at h ⊢
      exact ⟨trivial, forAll_ignoreSubcircuit_of_structuralComputableWitnesses input env env' h.2⟩

private theorem forAll_onlySubcircuits_of_structuralComputableWitnesses
    {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) :
    ∀ {ops : Operations F} {offset : ℕ},
      StructuralComputableWitnesses input env env' offset ops →
      ops.forAll offset (Condition.onlySubcircuits (computableWitnessCondition input env env'))
  | [], offset, h => by
      simp [Operations.forAll]
  | .witness m compute :: ops, offset, h => by
      simp only [StructuralComputableWitnesses,
        Condition.onlySubcircuits, Operations.forAll] at h ⊢
      exact ⟨trivial, forAll_onlySubcircuits_of_structuralComputableWitnesses input env env' h.2⟩
  | .assert e :: ops, offset, h => by
      simp only [StructuralComputableWitnesses,
        Condition.onlySubcircuits, Operations.forAll] at h ⊢
      exact ⟨trivial, forAll_onlySubcircuits_of_structuralComputableWitnesses input env env' h⟩
  | .lookup l :: ops, offset, h => by
      simp only [StructuralComputableWitnesses,
        Condition.onlySubcircuits, Operations.forAll] at h ⊢
      exact ⟨trivial, forAll_onlySubcircuits_of_structuralComputableWitnesses input env env' h⟩
  | .interact i :: ops, offset, h => by
      simp only [StructuralComputableWitnesses,
        Condition.onlySubcircuits, Operations.forAll] at h ⊢
      exact ⟨trivial, forAll_onlySubcircuits_of_structuralComputableWitnesses input env env' h⟩
  | .subcircuit s :: ops, offset, h => by
      simp only [StructuralComputableWitnesses,
        Condition.onlySubcircuits, Operations.forAll] at h ⊢
      exact ⟨
        FlatOperation.forAll_of_structuralComputableWitnesses input env env' h.1,
        forAll_onlySubcircuits_of_structuralComputableWitnesses input env env' h.2
      ⟩

theorem forAllFlat_of_structuralComputableWitnesses {Input : TypeMap} [CircuitType Input]
    (input : Var Input F) (env env' : ProverEnvironment F) :
    ∀ {ops : Operations F} {offset : ℕ},
      StructuralComputableWitnesses input env env' offset ops →
      ops.forAllFlat offset (computableWitnessCondition input env env')
  | ops, offset, h => by
      exact Operations.forAllFlat_of_forAll_ignoreSubcircuit_and_subcircuits
        (forAll_ignoreSubcircuit_of_structuralComputableWitnesses input env env' h)
        (forAll_onlySubcircuits_of_structuralComputableWitnesses input env env' h)

@[circuit_norm]
theorem structuralComputableWitnesses_append {Input : TypeMap} [CircuitType Input]
    {input : Var Input F} {env env' : ProverEnvironment F}
    {as bs : Operations F} {offset : ℕ} :
    StructuralComputableWitnesses input env env' offset (as ++ bs) ↔
      StructuralComputableWitnesses input env env' offset as ∧
      StructuralComputableWitnesses input env env' (as.localLength + offset) bs := by
  rw [structuralComputableWitnesses_iff_forAll, Operations.forAll_append,
    ← structuralComputableWitnesses_iff_forAll input env env',
    ← structuralComputableWitnesses_iff_forAll input env env']

end Operations

theorem computableWitnesses_forAllFlat {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuitBase F Input Output) (input : Var Input F) (n : ℕ)
    (hcircuit : circuit.ComputableWitnesses) :
    ∀ env env',
      (circuit.main input).operations n |>.forAllFlat n
        (computableWitnessCondition input env env') := by
  intro env env'
  change (circuit.main input).operations n |>.forAllFlat n
    { witness := fun n _ compute =>
        env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env' }
  exact hcircuit n input env env'

theorem compose_computableWitnesses_of_eq {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuitBase F Input Output) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ env env' : ProverEnvironment F,
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : ∀ n input env env',
      (circuit.main input).operations n |>.forAllFlat n
        (FormalCircuitBase.computableWitnessCondition input env env')) :
    ∀ env env',
      (circuit.main input).operations n |>.forAllFlat n
        (computableWitnessCondition parentInput env env') := by
  intro env env'
  have h_child := computableWitnesses_forAllFlat circuit input n hcircuit env env'
  unfold computableWitnessCondition at h_child ⊢
  rw [←Operations.forAll_toFlat_iff] at h_child
  rw [←Operations.forAll_toFlat_iff]
  generalize ((circuit.main input).operations n).toFlat = ops at *
  revert h_child
  apply FlatOperation.forAll_implies
  simp only [Condition.implies, Condition.ignoreSubcircuit, imp_self]
  induction ops using FlatOperation.induct generalizing n with
  | empty => trivial
  | assert | lookup | interact => simp_all [FlatOperation.forAll]
  | witness m c ops ih =>
    simp_all only [FlatOperation.forAll]
    constructor
    · intro h_witness h_agrees h_parent
      exact h_witness h_agrees (hinput env env' h_parent)
    · trivial

theorem compose_computableWitnesses_of_condition {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuitBase F Input Output) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment F),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
    ∀ env env',
      (circuit.main input).operations n |>.forAllFlat n
        (computableWitnessCondition parentInput env env') := by
  intro env env'
  have h_child := computableWitnesses_forAllFlat circuit input n hcircuit env env'
  unfold computableWitnessCondition at h_child ⊢
  rw [←Operations.forAll_toFlat_iff] at h_child
  rw [←Operations.forAll_toFlat_iff]
  generalize ((circuit.main input).operations n).toFlat = ops at *
  revert h_child
  apply FlatOperation.forAll_implies
  simp only [Condition.implies, Condition.ignoreSubcircuit, imp_self]
  induction ops using FlatOperation.induct generalizing n with
  | empty => trivial
  | assert e ops ih =>
    simp only [FlatOperation.forAll]
    exact ⟨trivial, ih n hinput⟩
  | lookup l ops ih =>
    simp only [FlatOperation.forAll]
    exact ⟨trivial, ih n hinput⟩
  | interact i ops ih =>
    simp only [FlatOperation.forAll]
    exact ⟨trivial, ih n hinput⟩
  | witness m c ops ih =>
    simp_all only [FlatOperation.forAll]
    constructor
    · intro h_witness h_agrees h_parent
      exact h_witness h_agrees (hinput n env env' (Nat.le_refl n) h_agrees h_parent)
    · exact ih (m + n) (by
        intro k env env' hle h_agree h_parent
        exact hinput k env env' (by omega) h_agree h_parent)

theorem computableWitnesses_implies {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuitBase F Input Output} :
    circuit.ComputableWitnesses → circuit.ComputableWitnesses' := by
  exact _root_.FormalCircuitBase.computableWitnesses_implies

end FormalCircuitBase

namespace Circuit

@[circuit_norm]
theorem pure_structuralComputableWitnesses_iff {Input : TypeMap} [CircuitType Input]
    {α : Type} (parentInput : Var Input F) (x : α) (n : ℕ)
    (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((pure x : Circuit F α).operations n) ↔ True := by
  simp [FormalCircuitBase.Operations.StructuralComputableWitnesses]

@[circuit_norm]
theorem witnessVector_structuralComputableWitnesses_iff {Input : TypeMap} [CircuitType Input]
    {m n : ℕ} (parentInput : Var Input F)
    (compute : ProverEnvironment F → Vector F m) (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((Circuit.witnessVector m compute).operations n) ↔
      (env.AgreesBelow n env' → eval env parentInput = eval env' parentInput →
        compute env = compute env') := by
  unfold Circuit.witnessVector
  simp [FormalCircuitBase.Operations.StructuralComputableWitnesses]

@[circuit_norm]
theorem witnessVar_structuralComputableWitnesses_iff {Input : TypeMap} [CircuitType Input]
    {n : ℕ} (parentInput : Var Input F)
    (compute : ProverEnvironment F → F) (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((Circuit.witnessVar compute).operations n) ↔
      (env.AgreesBelow n env' → eval env parentInput = eval env' parentInput →
        compute env = compute env') := by
  unfold Circuit.witnessVar
  simp [FormalCircuitBase.Operations.StructuralComputableWitnesses]

@[circuit_norm]
theorem assertZero_structuralComputableWitnesses_iff {Input : TypeMap} [CircuitType Input]
    (parentInput : Var Input F) (e : Expression F) (n : ℕ)
    (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((Circuit.assertZero e).operations n) ↔ True := by
  unfold Circuit.assertZero
  simp [FormalCircuitBase.Operations.StructuralComputableWitnesses]

@[circuit_norm]
theorem bind_structuralComputableWitnesses_iff {Input : TypeMap} [CircuitType Input]
    {α β : Type} {n : ℕ}
    (parentInput : Var Input F) (first : Circuit F α) (next : α → Circuit F β)
    (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        (((first >>= next) : Circuit F β).operations n) ↔
      FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        (first.operations n) ∧
      FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env'
        (n + first.localLength n)
        ((next (first.output n)).operations (n + first.localLength n)) := by
  rw [Circuit.bind_operations_eq]
  rw [FormalCircuitBase.Operations.structuralComputableWitnesses_append]
  simp [Circuit.localLength, Nat.add_comm]

@[circuit_norm]
theorem witnessField_structuralComputableWitnesses_iff {Input : TypeMap} [CircuitType Input]
    {n : ℕ} (parentInput : Var Input F)
    (compute : ProverEnvironment F → F) (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((Circuit.witnessField compute).operations n) ↔
      (env.AgreesBelow n env' → eval env parentInput = eval env' parentInput →
        compute env = compute env') := by
  unfold Circuit.witnessField
  simp only [bind_structuralComputableWitnesses_iff,
    witnessVar_structuralComputableWitnesses_iff,
    pure_structuralComputableWitnesses_iff, and_true]

@[circuit_norm]
theorem provableWitness_structuralComputableWitnesses_iff {Input Output : TypeMap}
    [CircuitType Input] [ProvableType Output] {n : ℕ}
    (parentInput : Var Input F)
    (compute : ProverEnvironment F → Output F) (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((ProvableType.witness (α := Output) compute).operations n) ↔
      (env.AgreesBelow n env' → eval env parentInput = eval env' parentInput →
        compute env = compute env') := by
  unfold ProvableType.witness
  simp only [FormalCircuitBase.Operations.StructuralComputableWitnesses]
  constructor
  · intro h h_agree h_input
    rw [ProvableType.ext_iff]
    intro i hi
    exact Vector.ext_iff.mp (h.1 h_agree h_input) i hi
  · intro h
    constructor
    · intro h_agree h_input
      exact congrArg toElements (h h_agree h_input)
    · trivial

@[circuit_norm]
theorem forEach_structuralComputableWitnesses_iff {α : Type} {Input : TypeMap} {m n : ℕ}
    [Inhabited α] [CircuitType Input] (parentInput : Var Input F)
    (xs : Vector α m) (body : α → Circuit F Unit)
    (constant : Circuit.ConstantLength body) (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((Circuit.forEach xs body constant).operations n) ↔
      ∀ i : Fin m,
        FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env'
          (n + i.val * (body default).localLength)
          ((body xs[i.val]).operations (n + i.val * (body default).localLength)) := by
  rw [FormalCircuitBase.Operations.structuralComputableWitnesses_iff_forAll]
  rw [Circuit.forEach.forAll]
  simp_rw [← FormalCircuitBase.Operations.structuralComputableWitnesses_iff_forAll parentInput env env']

@[circuit_norm]
theorem foldlRange_structuralComputableWitnesses_iff {β : Type} {Input : TypeMap} {m n : ℕ}
    [Inhabited β] [CircuitType Input] (parentInput : Var Input F)
    (init : β) (body : β → Fin m → Circuit F β)
    (constant : Circuit.ConstantLength fun x : β × Fin m => body x.1 x.2)
    (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((Circuit.foldlRange m init body constant).operations n) ↔
      ∀ i : Fin m,
        FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env'
          (n + i.val * (body default i).localLength)
          ((body (Circuit.FoldlM.foldlAcc n (Vector.finRange m) body init i) i).operations
            (n + i.val * (body default i).localLength)) := by
  rw [FormalCircuitBase.Operations.structuralComputableWitnesses_iff_forAll]
  rw [Circuit.foldlRange.forAll]
  simp_rw [← FormalCircuitBase.Operations.structuralComputableWitnesses_iff_forAll parentInput env env']

@[circuit_norm]
theorem mapFinRange_structuralComputableWitnesses_iff {β : Type} {Input : TypeMap} {m n : ℕ}
    [NeZero m] [CircuitType Input] (parentInput : Var Input F)
    (body : Fin m → Circuit F β)
    (constant : Circuit.ConstantLength body) (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((Circuit.mapFinRange m body constant).operations n) ↔
      ∀ i : Fin m,
        FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env'
          (n + i.val * (body 0).localLength)
          ((body i).operations (n + i.val * (body 0).localLength)) := by
  rw [FormalCircuitBase.Operations.structuralComputableWitnesses_iff_forAll]
  rw [Circuit.mapFinRange.forAll]
  simp_rw [← FormalCircuitBase.Operations.structuralComputableWitnesses_iff_forAll parentInput env env']

end Circuit

namespace FormalCircuit

@[circuit_norm]
theorem subcircuit_structuralComputableWitnesses_iff {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ) (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((subcircuit circuit input).operations n) ↔
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
        ((circuit.toSubcircuit n input).ops.toFlat) := by
  unfold subcircuit
  simp [FormalCircuitBase.Operations.StructuralComputableWitnesses]

theorem subcircuit_flatStructuralComputableWitnesses {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ env env' : ProverEnvironment F,
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
  ∀ env env',
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
        ((circuit.toSubcircuit n input).ops.toFlat) := by
  intro env env'
  unfold FormalCircuit.toSubcircuit
  rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll]
  rw [Operations.toNested_toFlat]
  rw [Operations.forAll_toFlat_iff]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.compose_computableWitnesses_of_eq
    circuit.base parentInput input n hinput hcircuit env env'

theorem subcircuit_flatStructuralComputableWitnesses_of_condition {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment F),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
  ∀ env env',
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
        ((circuit.toSubcircuit n input).ops.toFlat) := by
  intro env env'
  unfold FormalCircuit.toSubcircuit
  rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll]
  rw [Operations.toNested_toFlat]
  rw [Operations.forAll_toFlat_iff]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.compose_computableWitnesses_of_condition
    circuit.base parentInput input n hinput hcircuit env env'

end FormalCircuit

namespace GeneralFormalCircuit

theorem subcircuit_flatStructuralComputableWitnesses {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ env env' : ProverEnvironment F,
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.base.ComputableWitnesses) :
  ∀ env env',
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
        ((circuit.toSubcircuit n input).ops.toFlat) := by
  intro env env'
  unfold GeneralFormalCircuit.toSubcircuit GeneralFormalCircuit.toWithHint
    GeneralFormalCircuit.WithHint.toSubcircuit
  rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll]
  rw [Operations.toNested_toFlat]
  rw [Operations.forAll_toFlat_iff]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.compose_computableWitnesses_of_eq
    circuit.base parentInput input n hinput hcircuit env env'

theorem subcircuit_flatStructuralComputableWitnesses_of_condition {Parent Input Output : TypeMap}
    [CircuitType Parent] [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment F),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.base.ComputableWitnesses) :
    ∀ env env',
        FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
          ((circuit.toSubcircuit n input).ops.toFlat) := by
  intro env env'
  unfold GeneralFormalCircuit.toSubcircuit GeneralFormalCircuit.toWithHint
    GeneralFormalCircuit.WithHint.toSubcircuit
  rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll]
  rw [Operations.toNested_toFlat]
  rw [Operations.forAll_toFlat_iff]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.compose_computableWitnesses_of_condition
    circuit.base parentInput input n hinput hcircuit env env'

end GeneralFormalCircuit

namespace FormalAssertion

@[circuit_norm]
theorem assertion_structuralComputableWitnesses_iff {Parent Input : TypeMap}
    [CircuitType Parent] [ProvableType Input]
    (circuit : FormalAssertion F Input) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ) (env env' : ProverEnvironment F) :
    FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((assertion circuit input).operations n) ↔
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
        (((circuit.main input).operations n).toFlat) := by
  unfold assertion FormalAssertion.toSubcircuit
  simp [FormalCircuitBase.Operations.StructuralComputableWitnesses]
  rw [Operations.toNested_toFlat]

theorem assertion_flatStructuralComputableWitnesses {Parent Input : TypeMap}
    [CircuitType Parent] [ProvableType Input]
    (circuit : FormalAssertion F Input) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ env env' : ProverEnvironment F,
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
  ∀ env env',
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
        (((circuit.main input).operations n).toFlat) := by
  intro env env'
  rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll]
  rw [Operations.forAll_toFlat_iff]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.compose_computableWitnesses_of_eq
    circuit.base parentInput input n hinput hcircuit env env'

theorem assertion_flatStructuralComputableWitnesses_of_condition {Parent Input : TypeMap}
    [CircuitType Parent] [ProvableType Input]
    (circuit : FormalAssertion F Input) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment F),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
  ∀ env env',
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
        (((circuit.main input).operations n).toFlat) := by
  intro env env'
  rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll]
  rw [Operations.forAll_toFlat_iff]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.compose_computableWitnesses_of_condition
    circuit.base parentInput input n hinput hcircuit env env'

theorem subcircuit_flatStructuralComputableWitnesses_of_condition {Parent Input : TypeMap}
    [CircuitType Parent] [ProvableType Input]
    (circuit : FormalAssertion F Input) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment F),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
  ∀ env env',
      FormalCircuitBase.FlatOperation.StructuralComputableWitnesses parentInput env env' n
        ((circuit.toSubcircuit n input).ops.toFlat) := by
  intro env env'
  rw [FormalAssertion.toSubcircuit]
  simp only [Operations.toNested_toFlat]
  exact assertion_flatStructuralComputableWitnesses_of_condition
    circuit parentInput input n hinput hcircuit env env'

theorem assertion_structuralComputableWitnesses_of_condition {Parent Input : TypeMap}
    [CircuitType Parent] [ProvableType Input]
    (circuit : FormalAssertion F Input) (parentInput : Var Parent F)
    (input : Var Input F) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment F),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
  ∀ env env',
      FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' n
        ((assertion circuit input).operations n) := by
  intro env env'
  rw [assertion_structuralComputableWitnesses_iff]
  exact assertion_flatStructuralComputableWitnesses_of_condition
    circuit parentInput input n hinput hcircuit env env'

end FormalAssertion

end Challenge.Utils.ComputableWitnessLemmas
