import Challenge.Utils.CostR1CSRow
import Challenge.Utils.CostR1CSCanonicalSpec

/-!
# Canonical (C = identity) R1CS certification: machinery

**Nothing in this file needs semantic review**: the obligation itself is stated
in `CostR1CSCanonicalSpec.lean` (four definitions, flat-only); everything here
is kernel-checked scaffolding for *proving* it: an ops-level working
certificate (`operationsIsCid`) bridged to the trusted flat one by
`isCidCirc_iff_ops`, pin-aware append/flatten laws, and composition combinators.

The certificate threads a *pin counter* through the operation list: witnesses do
not advance it, each assert consumes one index, and a subcircuit advances it by
its constraint count. Composition works precisely for *balanced* circuits
because their constraint count and allocation offset advance together. The
reference proofs discharge each `Balanced` side condition locally from a
`CostIs` certificate and a `localLength` calculation.
-/

namespace Challenge.CostR1CS

-- The Spec seals its predicates; this file's definitional lemmas need them open.
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid

variable {F : Type} [Field F] {α β : Type}

/-- The constant-one expression is affine (the `B` of a canonical copy/sum row). -/
theorem Affine.one : Affine (1 : Expression F) := Affine.const 1

/-- Builder: a product row `var k − A·B` with `A, B` affine is canonical at `k`. -/
theorem isCidentityRowAt_var_sub_mul {k : ℕ} {A B : Expression F}
    (hA : Affine A) (hB : Affine B) :
    isCidentityRowAt k ((Expression.var ⟨k⟩ : Expression F) - A * B) :=
  ⟨A, B, hA, hB, rfl⟩

/-- A canonical row is in particular a single R1CS row. -/
theorem isCidentityRowAt.isR1CSRow {k : ℕ} {e : Expression F}
    (h : isCidentityRowAt k e) : isR1CSRow e := by
  rcases h with ⟨A, B, hA, hB, rfl⟩
  exact isR1CSRow_sub_mul (Affine.var _) hA hB

/-! ### Ops-level pin-counter certificate (derived machinery)

`flatOperationsIsCid` (the trusted one) lives in the Spec file; this ops-level
mirror is only a proof convenience; `operationsIsCid_iff_toFlat` below shows
they agree, so nothing here extends the trusted surface. -/

def operationsIsCid : ℕ → Operations F → Prop
  | _, [] => True
  | k, .witness _ _ :: ops => operationsIsCid k ops
  | k, .assert e :: ops => isCidentityRowAt k e ∧ operationsIsCid (k + 1) ops
  | _, .lookup _ :: _ => False
  | _, .interact _ :: _ => False
  | k, .subcircuit s :: ops =>
      flatOperationsIsCid k s.ops.toFlat ∧
        operationsIsCid (k + (nestedCount s.ops).constraints) ops

/-! ### Refinement to plain R1CS rows -/

theorem flatOperationsIsCid.flatOperationsIsR1CS {k : ℕ} {ops : List (FlatOperation F)}
    (h : flatOperationsIsCid k ops) : flatOperationsIsR1CS ops := by
  induction ops generalizing k with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | witness => exact ih h
    | assert e => exact ⟨h.1.isR1CSRow, ih h.2⟩
    | lookup => exact h.elim
    | interact => exact h.elim

theorem operationsIsCid.operationsIsR1CS {k : ℕ} {ops : Operations F}
    (h : operationsIsCid k ops) : operationsIsR1CS ops := by
  induction ops generalizing k with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | witness => exact ih h
    | assert e => exact ⟨h.1.isR1CSRow, ih h.2⟩
    | lookup => exact h.elim
    | interact => exact h.elim
    | subcircuit s => exact ⟨h.1.flatOperationsIsR1CS, ih h.2⟩

/-! ### Counting bridges (nested ↔ flat) -/

theorem flatCount_append (ops₁ ops₂ : List (FlatOperation F)) :
    flatCount (ops₁ ++ ops₂) = flatCount ops₁ + flatCount ops₂ := by
  induction ops₁ with
  | nil =>
      rw [List.nil_append]
      show _ = Count.zero + _
      rw [Count.zero_add]
  | cons op ops ih =>
      rw [List.cons_append]
      show flatOperationCount op + flatCount (ops ++ ops₂) = _ + _ + _
      rw [ih, Count.add_assoc]

mutual
theorem flatCount_toFlat_nested : ∀ nop : NestedOperations F,
    flatCount nop.toFlat = nestedCount nop
  | .single op => by
      simp only [NestedOperations.toFlat, flatCount, nestedCount, Count.add_zero]
  | .nested (name, lst) => by
      simp only [NestedOperations.toFlat, nestedCount]
      exact flatCount_toFlat_nestedList lst

theorem flatCount_toFlat_nestedList : ∀ l : List (NestedOperations F),
    flatCount (l.flatMap NestedOperations.toFlat) = nestedListCount l
  | [] => rfl
  | nop :: l => by
      rw [List.flatMap_cons, flatCount_append, flatCount_toFlat_nested nop,
        flatCount_toFlat_nestedList l]
      rfl
end

/-! ### Append / flatten / toFlat, pin-counter aware -/

theorem flatOperationsIsCid_append (k : ℕ) (ops₁ ops₂ : List (FlatOperation F)) :
    flatOperationsIsCid k (ops₁ ++ ops₂) ↔
      flatOperationsIsCid k ops₁ ∧
        flatOperationsIsCid (k + (flatCount ops₁).constraints) ops₂ := by
  induction ops₁ generalizing k with
  | nil => exact Iff.intro (fun h => ⟨trivial, h⟩) (fun h => h.2)
  | cons op ops ih =>
    cases op with
    | witness m c =>
        show flatOperationsIsCid k (ops ++ ops₂) ↔ _ ∧
          flatOperationsIsCid (k + ((⟨m, 0⟩ : Count) + flatCount ops).constraints) ops₂
        rw [ih k, Count.add_constraints, Nat.zero_add]
        rfl
    | assert e =>
        show isCidentityRowAt k e ∧ flatOperationsIsCid (k + 1) (ops ++ ops₂) ↔
          (isCidentityRowAt k e ∧ _) ∧
            flatOperationsIsCid (k + ((⟨0, 1⟩ : Count) + flatCount ops).constraints) ops₂
        rw [ih (k + 1), Count.add_constraints,
          show k + (1 + (flatCount ops).constraints) = k + 1 + (flatCount ops).constraints
            by omega]
        exact and_assoc.symm
    | lookup l => exact iff_of_false id (fun h => h.1)
    | interact i => exact iff_of_false id (fun h => h.1)

theorem operationsIsCid_append (k : ℕ) (ops₁ ops₂ : Operations F) :
    operationsIsCid k (ops₁ ++ ops₂) ↔
      operationsIsCid k ops₁ ∧
        operationsIsCid (k + (operationCount ops₁).constraints) ops₂ := by
  induction ops₁ generalizing k with
  | nil => exact Iff.intro (fun h => ⟨trivial, h⟩) (fun h => h.2)
  | cons op ops ih =>
    cases op with
    | witness m c =>
        show operationsIsCid k (ops ++ ops₂) ↔ _ ∧
          operationsIsCid (k + ((⟨m, 0⟩ : Count) + operationCount ops).constraints) ops₂
        rw [ih k, Count.add_constraints, Nat.zero_add]
        rfl
    | assert e =>
        show isCidentityRowAt k e ∧ operationsIsCid (k + 1) (ops ++ ops₂) ↔
          (isCidentityRowAt k e ∧ _) ∧
            operationsIsCid (k + ((⟨0, 1⟩ : Count) + operationCount ops).constraints) ops₂
        rw [ih (k + 1), Count.add_constraints,
          show k + (1 + (operationCount ops).constraints) = k + 1 + (operationCount ops).constraints
            by omega]
        exact and_assoc.symm
    | lookup l => exact iff_of_false id (fun h => h.1)
    | interact i => exact iff_of_false id (fun h => h.1)
    | subcircuit s =>
        show flatOperationsIsCid k s.ops.toFlat ∧
            operationsIsCid (k + (nestedCount s.ops).constraints) (ops ++ ops₂) ↔
          (_ ∧ _) ∧
            operationsIsCid (k + (nestedCount s.ops + operationCount ops : Count).constraints) ops₂
        rw [ih (k + (nestedCount s.ops).constraints), Count.add_constraints,
          show k + ((nestedCount s.ops).constraints + (operationCount ops).constraints)
              = k + (nestedCount s.ops).constraints + (operationCount ops).constraints by omega]
        exact and_assoc.symm

theorem operationsIsCid_iff_toFlat (k : ℕ) (ops : Operations F) :
    operationsIsCid k ops ↔ flatOperationsIsCid k ops.toFlat := by
  induction ops generalizing k with
  | nil => exact iff_of_true trivial trivial
  | cons op ops ih =>
    cases op with
    | witness m c => exact ih k
    | assert e => exact and_congr Iff.rfl (ih (k + 1))
    | lookup l => exact Iff.rfl
    | interact i => exact Iff.rfl
    | subcircuit s =>
        show flatOperationsIsCid k s.ops.toFlat ∧
            operationsIsCid (k + (nestedCount s.ops).constraints) ops ↔
          flatOperationsIsCid k (s.ops.toFlat ++ Operations.toFlat ops)
        rw [flatOperationsIsCid_append, flatCount_toFlat_nested s.ops,
          ih (k + (nestedCount s.ops).constraints)]

/-- Flatten of a `List.ofFn` whose piece `i` starts its pins at `k + i·L` and
contributes exactly `L` constraints. -/
theorem operationsIsCid_flatten_ofFn {m : ℕ} {g : Fin m → Operations F} {k L : ℕ}
    (hL : ∀ i, (operationCount (g i)).constraints = L)
    (h : ∀ i : Fin m, operationsIsCid (k + i.val * L) (g i)) :
    operationsIsCid k (List.ofFn g).flatten := by
  induction m generalizing k with
  | zero => rw [List.ofFn_zero, List.flatten_nil]; exact trivial
  | succ mm ih =>
    rw [List.ofFn_succ, List.flatten_cons, operationsIsCid_append, hL 0]
    refine ⟨by simpa using h 0, ?_⟩
    refine ih (g := fun i => g i.succ) (fun i => hL i.succ) fun i => ?_
    rw [show k + L + i.val * L = k + (i.val + 1) * L by ring]
    simpa [Fin.val_succ] using h i.succ

/-! ### Circuit-level combinators (via the flat ↔ ops bridge) -/

/-- The trusted flat-level `IsCidCirc` (Spec file) is equivalent to the
ops-level working certificate; all combinators go through this bridge. -/
theorem isCidCirc_iff_ops {c : Circuit F α} :
    IsCidCirc c ↔ ∀ n, operationsIsCid n (c.operations n) :=
  forall_congr' fun n => (operationsIsCid_iff_toFlat n _).symm

theorem IsCidCirc.of_ops {c : Circuit F α}
    (h : ∀ n, operationsIsCid n (c.operations n)) : IsCidCirc c :=
  isCidCirc_iff_ops.mpr h

theorem IsCidCirc.ops {c : Circuit F α} (h : IsCidCirc c) (n : ℕ) :
    operationsIsCid n (c.operations n) :=
  isCidCirc_iff_ops.mp h n

theorem IsCidCirc.isR1CSCirc {c : Circuit F α} (h : IsCidCirc c) : IsR1CSCirc c :=
  fun n => (h.ops n).operationsIsR1CS

/-- A circuit is *balanced* when it emits exactly as many constraints as its
`localLength` (= allocations), the lockstep that lets pins and offsets advance
together across a `bind`. Discharged from a `CostIs` certificate. -/
def Balanced (c : Circuit F α) : Prop :=
  ∀ n, (operationCount (c.operations n)).constraints = c.localLength n

theorem Balanced.of_costIs {c : Circuit F α} {K : Count} (hc : CostIs c K)
    (hL : ∀ n, c.localLength n = K.constraints) : Balanced c :=
  fun n => by rw [hc n, hL n]

/-- The constraints component of a cost certificate, as a `ℕ` equation. -/
theorem CostIs.constraints {c : Circuit F α} {K : Count} (h : CostIs c K) (n : ℕ) :
    (operationCount (c.operations n)).constraints = K.constraints :=
  congrArg Count.constraints (h n)

theorem IsCidCirc.pure (a : α) : IsCidCirc (pure a : Circuit F α) :=
  IsCidCirc.of_ops fun n => by rw [Circuit.pure_operations_eq]; trivial

theorem IsCidCirc.witnessVector (m : ℕ) (c : ProverEnvironment F → Vector F m) :
    IsCidCirc (Circuit.witnessVector m c) :=
  IsCidCirc.of_ops fun n => by trivial

/-- `pure` with the pin counter and the offset decoupled (they differ mid-block;
unifying them through large closures times out `whnf`). -/
theorem operationsIsCid_pure (a : α) (k n : ℕ) :
    operationsIsCid k ((pure a : Circuit F α).operations n) := by
  rw [Circuit.pure_operations_eq]; trivial

/-- `witnessVector` with pin counter and offset decoupled. -/
theorem operationsIsCid_witnessVector (m : ℕ) (c : ProverEnvironment F → Vector F m)
    (k n : ℕ) : operationsIsCid k ((Circuit.witnessVector m c).operations n) := by
  trivial

theorem IsCidCirc.bind {f : Circuit F α} {g : α → Circuit F β}
    (hf : IsCidCirc f) (hbal : Balanced f) (hg : ∀ a, IsCidCirc (g a)) :
    IsCidCirc (f >>= g) :=
  IsCidCirc.of_ops fun n => by
    rw [Circuit.bind_operations_eq, operationsIsCid_append, hbal n]
    exact ⟨hf.ops n, (hg _).ops _⟩

/-- `bind` whose continuation is certified at the first circuit's output offset. -/
theorem IsCidCirc.bind_out {f : Circuit F α} {g : α → Circuit F β}
    (hf : IsCidCirc f) (hbal : Balanced f) (hg : ∀ n, IsCidCirc (g (f.output n))) :
    IsCidCirc (f >>= g) :=
  IsCidCirc.of_ops fun n => by
    rw [Circuit.bind_operations_eq, operationsIsCid_append, hbal n]
    exact ⟨hf.ops n, (hg n).ops (n + f.localLength n)⟩

theorem IsCidCirc.subcircuit {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuit F Input Output} {b : Var Input F}
    (h : ∀ n, operationsIsCid n ((circuit.main b).operations n)) :
    IsCidCirc (subcircuit circuit b) := by
  refine IsCidCirc.of_ops fun n => ?_
  show operationsIsCid n [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsCid n (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (operationsIsCid_iff_toFlat n _).mp (h n)

/-! ### Top-level helpers (the predicate itself is in the Spec file) -/

theorem isR1CS_Cidentity_of_IsCidCirc {Input Output : TypeMap} [ProvableType Input]
    [ProvableType Output] {main : Var Input F → Circuit F (Var Output F)}
    (hops : ∀ input : Var Input F, AffineProvable input → IsCidCirc (main input))
    (hout : ∀ input : Var Input F, AffineProvable input → AffineOutput (main input)) :
    isR1CS_Cidentity main :=
  fun input hinput => ⟨hops input hinput, hout input hinput⟩

/-- A canonical certificate implies the ordinary R1CS certificate. -/
theorem isR1CS_Cidentity.isR1CS {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {main : Var Input F → Circuit F (Var Output F)} (h : isR1CS_Cidentity main) : isR1CS main :=
  fun input hinput => ⟨(h input hinput).1.isR1CSCirc, (h input hinput).2⟩

-- Seal the ops-level mirror too (same blow-up guard as the Spec's predicates);
-- gadget certificate proofs re-enable all three locally.
attribute [irreducible] operationsIsCid

end Challenge.CostR1CS
