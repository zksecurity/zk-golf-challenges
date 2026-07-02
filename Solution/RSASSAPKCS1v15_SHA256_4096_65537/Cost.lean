import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExp
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.LessThan
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.EqViaCarries
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesToBigInt
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.PadDigest
import Challenge.Utils.CostR1CS
import Clean.Circuit.Loops

/-!
# Compositional cost (`CostIs`) and R1CS (`IsR1CSCirc`) facts for the RSA gadgets

Bottom-up `operationCount` / `operationsIsR1CS` certificates for the building-block
gadgets used by `main` (`rangeCheck`, `Normalize`, `Equal`, `LessThan`,
`EqViaCarries`, `MulMod`, `ModExp`, and the byte-glue `ByteBlock`/`BytesToBigInt`/
`PadDigest`), proved with the compositional lemmas in `Challenge.CostR1CS` (no
`native_decide`).

These leaves are all generic over the parameter bundle `P`; the top-level
`main`-specific R1CS assembly lives in `Main.lean`, which consumes these.

This file also folds in the `CostInfra` row-affineness helper for a
`ProvableVector (fields 32) n` symbolic witness vector (the byte/digest glue),
which the trusted module does not provide.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

open Challenge.CostR1CS

variable {Fld : Type} [Field Fld]

/-- Each `fields 32` row of a `varFromOffset` over a `ProvableVector (fields 32) n`
is itself a `varFromOffset`, hence affine. -/
theorem affineW_varFromOffset_pvec {n : ℕ} (off j : ℕ) (hj : j < n) :
    AffineW ((varFromOffset (ProvableVector (fields 32) n) off :
      Var (ProvableVector (fields 32) n) Fld)[j]'hj) := by
  rw [varFromOffset_vector, Vector.getElem_mapRange]
  exact affineW_varFromOffset _ _

end Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

/-- A `ProvableType.witness` over `α` allocates exactly `size α` cells and no
constraints. Its operation list is `[.witness (size α) ..]`, same shape as
`witnessVector`. -/
theorem CostIs.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    CostIs (ProvableType.witness (α := α) compute) ⟨size α, 0⟩ := by
  intro n; rfl

theorem IsR1CSCirc.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := α) compute) := by
  intro n; trivial

/-- Invoking a `GeneralFormalCircuit` as a subcircuit costs exactly its `main`'s
count (same operation shape as `CostIs.subcircuit`). -/
theorem CostIs.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)} {K : Count}
    (h : ∀ n, operationCount ((circuit.main b).operations n) = K) :
    CostIs (subcircuitWithAssertion circuit b) K := by
  intro n
  show operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K
  have hz : operationCount [Operation.subcircuit (circuit.toSubcircuit n b)]
      = nestedCount (circuit.toSubcircuit n b).ops := by
    show nestedCount _ + operationCount ([] : Operations (F circomPrime)) = nestedCount _
    rw [show operationCount ([] : Operations (F circomPrime)) = Count.zero from rfl, Count.add_zero]
  rw [hz]
  show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩) = K
  rw [show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩)
        = nestedListCount ((circuit.main b).operations n).toNested from rfl,
      Lemmas.operationCount_toNested]
  exact h n

theorem IsR1CSCirc.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)}
    (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n)) :
    IsR1CSCirc (subcircuitWithAssertion circuit b) := by
  intro n
  show operationsIsR1CS [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsR1CS (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (Lemmas.operationsIsR1CS_iff_toFlat _).mp (h n)

/-! ## `toBits` / `rangeCheck` (per-limb `B`-bit range check) -/

/-- `toBits.main n x` witnesses `n` bits, boolean-constrains each, and asserts the
recomposition equals `x`: `⟨n, n+1⟩`. -/
theorem costIs_toBits (n : ℕ) (x : Expression (F circomPrime)) :
    CostIs (Gadgets.ToBits.main n x) ⟨n, n + 1⟩ := by
  unfold Gadgets.ToBits.main
  have hcount : (⟨n, 0⟩ + (⟨n * 0, n * 1⟩ + (⟨0, 1⟩ + Count.zero)) : Count) = ⟨n, n + 1⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1; simp [Count.zero]
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) n _) fun bits => ?_
  refine CostIs.bind
    (show CostIs (Circuit.forEach bits (fun input => assertion assertBool input) _) ⟨n * 0, n * 1⟩ from
      CostIs.forEach fun a m =>
        (CostIs.assertion (circuit := assertBool) (b := a) (K := ⟨0, 1⟩) (fun k => rfl)) m) fun _ => ?_
  refine CostIs.bind
    (show CostIs (x === Utils.Bits.fieldFromBitsExpr bits) ⟨0, 1⟩ from ?_) fun _ => CostIs.pure _
  show CostIs (Expression.assertEquals x (Utils.Bits.fieldFromBitsExpr bits)) ⟨0, 1⟩
  unfold Expression.assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun m => ?_
  show operationCount ((Gadgets.Equality.main (M := id) (x, Utils.Bits.fieldFromBitsExpr bits)).operations m) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) m)

/-- A `forEach` is single-row R1CS when each *indexed* body is, so the certificate
can use that `xs[i]` is affine (the generic `IsR1CSCirc.forEach` quantifies over
all element values, too weak for booleanity rows). -/
theorem IsR1CSCirc.forEach_mem {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F circomPrime) Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- `fieldFromBitsExpr` over an affine bit-vector is affine. -/
theorem affine_fieldFromBitsExpr {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (h : AffineW bits) : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

/-- `toBits.main n x` is single-row R1CS when `x` is affine: each booleanity row
`bit·(bit-1)` and the recomposition row `x - fieldFromBitsExpr bits` are R1CS. -/
theorem isR1CS_toBits (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.ToBits.main n x) := by
  unfold Gadgets.ToBits.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector n _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine (IsR1CSCirc.assertion (circuit := assertBool) fun j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    show isR1CSRow (_ * (_ - 1))
    exact isR1CSRow_mul (affineW_witnessVector_output n _ w i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output n _ w i.val i.isLt) (Affine.const 1))
  · show IsR1CSCirc (x === Utils.Bits.fieldFromBitsExpr _)
    show IsR1CSCirc (Expression.assertEquals x (Utils.Bits.fieldFromBitsExpr _))
    unfold Expression.assertEquals
    refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit id) fun k => ?_
    show operationsIsR1CS ((Gadgets.Equality.main (M := id)
      (x, Utils.Bits.fieldFromBitsExpr ((Circuit.witnessVector n _).output w))).operations k)
    unfold Gadgets.Equality.main
    refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
    exact isR1CSRow_of_affine (Affine.sub hx
      (affine_fieldFromBitsExpr (Vector.mapRange n fun i => Expression.var { index := w + i })
        (affineW_mapRange_var _)))

/-! ### `rangeCheck` (a `FormalAssertion` wrapping `toBits`) -/

theorem costIs_toBits_sub (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime) (x : Expression (F circomPrime)) :
    CostIs (Gadgets.ToBits.toBits n hn x) ⟨n, n + 1⟩ :=
  CostIs.subcircuitWithAssertion (fun m => costIs_toBits n x m)

theorem isR1CS_toBits_sub (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.ToBits.toBits n hn x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun m => isR1CS_toBits n x hx m)

/-- `rangeCheck.main x = do let _ ← toBits n hn x`, hence cost `⟨n, n+1⟩`. -/
theorem costIs_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime) (x : Expression (F circomPrime)) :
    CostIs ((Gadgets.ToBits.rangeCheck n hn).main x) ⟨n, n + 1⟩ := by
  show CostIs (Gadgets.ToBits.toBits n hn x >>= fun _ => pure ()) ⟨n, n + 1⟩
  have := CostIs.bind (costIs_toBits_sub n hn x) (fun _ => CostIs.pure ())
  simpa [Count.add_zero] using this

theorem isR1CS_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc ((Gadgets.ToBits.rangeCheck n hn).main x) := by
  show IsR1CSCirc (Gadgets.ToBits.toBits n hn x >>= fun _ => pure ())
  exact IsR1CSCirc.bind (isR1CS_toBits_sub n hn x hx) (fun _ => IsR1CSCirc.pure ())

/-- The `rangeCheck` assertion invoked on `x` costs `⟨n, n+1⟩`. -/
theorem costIs_assertion_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) :
    CostIs (assertion (Gadgets.ToBits.rangeCheck n hn) x) ⟨n, n + 1⟩ :=
  CostIs.assertion (fun m => costIs_rangeCheck n hn x m)

theorem isR1CS_assertion_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (Gadgets.ToBits.rangeCheck n hn) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_rangeCheck n hn x hx m)

/-! ## G1 — `Normalize` -/

variable {m : ℕ}

/-- `Normalize.main P x` range-checks each of the `m` limbs of `x`. -/
theorem costIs_normalize (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (Normalize.main P x) ⟨m * P.B, m * (P.B + 1)⟩ := by
  unfold Normalize.main
  exact CostIs.forEach (fun a n => costIs_assertion_rangeCheck P.B P.hB a n)

theorem isR1CS_normalize (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (Normalize.main P x) := by
  unfold Normalize.main
  exact IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
    fun i n => isR1CS_assertion_rangeCheck P.B P.hB x[i.val] (hx i.val i.isLt) n

theorem costIs_assertion_normalize (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (assertion (Normalize.circuit P) x) ⟨m * P.B, m * (P.B + 1)⟩ :=
  CostIs.assertion (fun n => costIs_normalize P x n)

theorem isR1CS_assertion_normalize (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (assertion (Normalize.circuit P) x) :=
  IsR1CSCirc.assertion (fun n => isR1CS_normalize P x hx n)

/-! ## `Equal` -/

/-- `Equal.main input = input.lhs === input.rhs`, an `Equality` assertion over the
`m` limbs: `⟨0, m⟩`. -/
theorem costIs_equal (input : Var (Equal.Inputs m) (F circomPrime)) :
    CostIs (Equal.main input) ⟨0, m⟩ := by
  show CostIs (Gadgets.Equality.circuit (fields m) (input.lhs, input.rhs)) ⟨0, m⟩
  refine CostIs.assertion (K := ⟨0, m⟩) fun n => ?_
  show operationCount ((Gadgets.Equality.main (M := fields m)
    (input.lhs, input.rhs)).operations n) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := m) (fun a k => CostIs.assertZero _ k) n)

theorem isR1CS_equal (input : Var (Equal.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (Equal.main input) := by
  show IsR1CSCirc (Gadgets.Equality.circuit (fields m) (input.lhs, input.rhs))
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit (fields m)) fun n => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := fields m)
    (input.lhs, input.rhs)).operations n)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_) n
  refine IsR1CSCirc.assertZero ?_ k
  have hi : i.val < m := i.isLt
  rw [Vector.getElem_map, Vector.getElem_zip]
  exact isR1CSRow_of_affine (Affine.sub (hl i.val hi) (hr i.val hi))

theorem costIs_assertion_equal (P : BigIntParams circomPrime m)
    (input : Var (Equal.Inputs m) (F circomPrime)) :
    CostIs (assertion (Equal.circuit P) input) ⟨0, m⟩ :=
  CostIs.assertion (fun n => costIs_equal input n)

theorem isR1CS_assertion_equal (P : BigIntParams circomPrime m)
    (input : Var (Equal.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (Equal.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_equal input hl hr n)

/-- The output of a `ProvableType.witness (α := BigInt k)` is a fresh
`varFromOffset`, hence affine at every offset. -/
theorem affineW_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) (nd : ℕ) :
    AffineW ((ProvableType.witness (α := BigInt k) compute).output nd :
      Var (BigInt k) (F circomPrime)) := by
  rw [show ((ProvableType.witness (α := BigInt k) compute).output nd : Var (BigInt k) (F circomPrime))
        = varFromOffset (BigInt k) nd from rfl]
  exact affineW_varFromOffset _ _

theorem isR1CS_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := BigInt k) compute) :=
  IsR1CSCirc.provableWitness _

/-- `IsR1CSCirc.witnessVector` packaged so it unifies as the first argument of
`bind_out` (avoids the `compute` metavariable elaboration-order issue). -/
theorem isR1CS_witnessVec (k : ℕ) (c : ProverEnvironment (F circomPrime) → Vector (F circomPrime) k) :
    IsR1CSCirc (Circuit.witnessVector k c) := IsR1CSCirc.witnessVector k c

/-! ## G2 — `LessThan` -/

/-- Cost of `LessThan.main P input` (m ≥ 1): witness `d` (m), normalize `d`
(`m·B` / `m·(B+1)`), witness carries (m), boolean forEach (m constraints),
linear forEach (m constraints), and the forced top carry (1 constraint). -/
theorem costIs_lessThan (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime)) :
    CostIs (LessThan.main P input)
      ⟨m + m * P.B + m, m * (P.B + 1) + m + m + 1⟩ := by
  have hne : ¬ (m = 0) := NeZero.ne m
  rw [show (⟨m + m * P.B + m, m * (P.B + 1) + m + m + 1⟩ : Count)
        = ⟨m, 0⟩ + (⟨m * P.B, m * (P.B + 1)⟩ + (⟨m, 0⟩ +
            (⟨m * 0, m * 1⟩ + (⟨m * 0, m * 1⟩ + (⟨0, 1⟩ + Count.zero))))) from by
      simp only [Count.zero]; congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold LessThan.main
  refine CostIs.bind (CostIs.provableWitness _) fun d => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector m _) fun carry => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  rw [dif_neg hne]
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_lessThan (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (LessThan.main P input) := by
  have hne : ¬ (m = 0) := NeZero.ne m
  unfold LessThan.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nd => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nd))
    fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec m _) fun nc => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- boolean forEach: each `c * (c - 1)` is a single row
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- linear forEach: each constraint is affine
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    refine isR1CSRow_of_affine ?_
    refine Affine.sub (Affine.sub (Affine.add (Affine.add (Affine.add
      (hl i.val i.isLt) (affineW_provableWitness_bigInt _ nd i.val i.isLt)) ?_) ?_)
      (hr i.val i.isLt))
      (Affine.mul_fconst _ (affineW_witnessVector_output _ _ _ i.val i.isLt))
    · split
      · exact Affine.zero
      · exact affineW_witnessVector_output _ _ _ _ (by omega)
    · split
      · exact Affine.const 1
      · exact Affine.zero
  rw [dif_neg hne]
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_of_affine (affineW_witnessVector_output _ _ _ (m - 1) (by omega))))
    fun _ => IsR1CSCirc.pure _

theorem costIs_assertion_lessThan (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime)) :
    CostIs (assertion (LessThan.circuit P) input)
      ⟨m + m * P.B + m, m * (P.B + 1) + m + m + 1⟩ :=
  CostIs.assertion (fun n => costIs_lessThan P input n)

theorem isR1CS_assertion_lessThan (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (LessThan.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_lessThan P input hl hr n)

/-! ## G4 — `EqViaCarries` -/

/-- Cost of `EqViaCarries.main P input` (m ≥ 1, so `2m-1 ≥ 1`): witness the
`2m-1` carries, range-check each to `W` bits, one linear constraint per index,
and the forced top carry. -/
theorem costIs_eqViaCarries (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (EqViaCarries.main P input)
      ⟨(2 * m - 1) + (2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1) + (2 * m - 1) + 1⟩ := by
  have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
  have hne : ¬ (2 * m - 1 = 0) := by omega
  rw [show (⟨(2 * m - 1) + (2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1) + (2 * m - 1) + 1⟩ : Count)
        = ⟨2 * m - 1, 0⟩ + (⟨(2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1)⟩ +
            (⟨(2 * m - 1) * 0, (2 * m - 1) * 1⟩ + (⟨0, 1⟩ + Count.zero))) from by
      simp only [Count.zero]
      congr 1; simp only [Count.add_constraints]; ring]
  unfold EqViaCarries.main
  refine CostIs.bind (CostIs.witnessVector (2 * m - 1) _) fun carry => ?_
  refine CostIs.bind (CostIs.forEach fun a n => costIs_assertion_rangeCheck P.W P.hW a n) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  rw [dif_neg hne]
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_eqViaCarries (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (EqViaCarries.main P input) := by
  have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
  have hne : ¬ (2 * m - 1 = 0) := by omega
  unfold EqViaCarries.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec (2 * m - 1) _) fun nc => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- range-check each carry: `W`-bit, R1CS since carry entries are affine
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    exact isR1CS_assertion_rangeCheck P.W P.hW _
      (affineW_witnessVector_output _ _ _ i.val i.isLt) k
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- per-index linear constraint is affine
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    refine isR1CSRow_of_affine ?_
    refine Affine.sub (Affine.sub (Affine.add (hl i.val i.isLt) ?_) (hr i.val i.isLt))
      (Affine.mul_fconst _ (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt)
        (Affine.const _)))
    · split
      · exact Affine.zero
      · exact Affine.sub (affineW_witnessVector_output _ _ _ _ (by omega)) (Affine.const _)
  rw [dif_neg hne]
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_of_affine (Affine.sub
      (affineW_witnessVector_output _ _ _ (2 * m - 1 - 1) (by omega)) (Affine.const _))))
    fun _ => IsR1CSCirc.pure _

theorem costIs_assertion_eqViaCarries (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (assertion (EqViaCarries.circuit P) input)
      ⟨(2 * m - 1) + (2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1) + (2 * m - 1) + 1⟩ :=
  CostIs.assertion (fun n => costIs_eqViaCarries P input n)

theorem isR1CS_assertion_eqViaCarries (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (EqViaCarries.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_eqViaCarries P input hl hr n)

/-! ## G5 — `MulMod` -/

/-- `A*B - C` with all of `A, B, C` affine is a single R1CS row (`⟨A,z⟩·⟨B,z⟩ =
⟨C,z⟩`). Mirror of the trusted `isR1CSRow_sub_mul`, with the product on the left
(the form `MulMod.witnessedMul` produces: `a[i]·b[j] − pp[t]`). -/
theorem isR1CSRow_mul_sub {A B C : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) : isR1CSRow (A * B - C) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (A * B + -C) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (A * B + -C) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)

/-- Each coefficient of `bigIntMulVars pp` is an affine fold of the (affine)
witnessed products `pp`, hence affine. This is what makes the witnessed-product
multiply R1CS-clean: the convolution coefficients fed to `EqViaCarries` are linear
forms over fresh cells rather than rank-≥2 sums of products. -/
theorem affineW_bigIntMulVars [NeZero m] (pp : Vector (Expression (F circomPrime)) (m * m))
    (hpp : ∀ t (ht : t < m * m), Affine pp[t]) :
    AffineW (bigIntMulVars pp) := by
  intro k hk
  simp only [bigIntMulVars]
  rw [Vector.getElem_mapFinRange, vector_foldl_finRange]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  split
  · exact Affine.add hacc (hpp _ _)
  · exact hacc

/-- The output of `witnessedMul a b` is `bigIntMulVars` over the freshly witnessed
product matrix, hence affine at every offset. -/
theorem affineW_witnessedMul_output [NeZero m] (a b : Var (BigInt m) (F circomPrime)) (off : ℕ) :
    AffineW ((MulMod.witnessedMul a b).output off) := by
  rw [show (MulMod.witnessedMul a b).output off
        = bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F circomPrime) { index := off + i })
      from MulMod.witnessedMul_output off a b]
  refine affineW_bigIntMulVars _ fun t ht => ?_
  rw [Vector.getElem_mapRange]; exact Affine.var _

/-- `witnessedMul a b` witnesses the `m·m` product matrix (`⟨m·m, 0⟩`) and asserts
each product (`m·m` rows): `⟨m·m, m·m⟩`. -/
theorem costIs_witnessedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime)) :
    CostIs (MulMod.witnessedMul a b) ⟨m * m, m * m⟩ := by
  rw [show (⟨m * m, m * m⟩ : Count)
        = ⟨m * m, 0⟩ + (⟨m * m * 0, m * m * 1⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1
      simp only [Count.add_constraints]; ring]
  unfold MulMod.witnessedMul
  refine CostIs.bind (CostIs.provableWitness _) fun pp => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

/-- Each product assert `a[t/m]·b[t%m] − pp[t]` of `witnessedMul` is a single R1CS
row (a single rank-1 product minus an affine cell), given affine inputs `a, b`. -/
theorem isR1CS_witnessedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.witnessedMul a b) := by
  unfold MulMod.witnessedMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun npp => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (ha _ (Nat.div_lt_of_lt_mul t.isLt))
      (hb _ (Nat.mod_lt _ (Nat.pos_of_neZero m)))
      (affineW_provableWitness_bigInt (k := m * m) _ npp t.val t.isLt)
  exact IsR1CSCirc.pure _

/-- The per-gadget `Count` of one `MulMod` subcircuit, as a sum of the leaf
gadget counts: witness `q,r` (`m + m`), normalize `q,r` (two `⟨m·B, m·(B+1)⟩`),
the two `witnessedMul` product matrices (`⟨m·m, m·m⟩` each), and the
`EqViaCarries` and `LessThan` assertions. -/
def mulModCount (B W : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + (⟨m * B, m * (B + 1)⟩ + (⟨m * B, m * (B + 1)⟩ +
    (⟨m * m, m * m⟩ + (⟨m * m, m * m⟩ +
    (⟨(2 * m - 1) + (2 * m - 1) * W, (2 * m - 1) * (W + 1) + (2 * m - 1) + 1⟩ +
      (⟨m + m * B + m, m * (B + 1) + m + m + 1⟩ + Count.zero)))))))

theorem costIs_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulMod.main P input) (mulModCount (m := m) P.B P.W) := by
  unfold MulMod.main mulModCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_witnessedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_witnessedMul _ _) fun Sqn => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarries P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan P _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (MulMod.circuit P) b) (mulModCount (m := m) P.B P.W) :=
  CostIs.subcircuit (fun n => costIs_mulMod P b n)

/-! ## G6 — `ModExp` -/

/-- `mulModCount` equals `ModExp.mulModLen` (the per-iteration allocation count) in
its `allocations` field; the loop's `localLength` formula uses `mulModLen`. -/
theorem mulModCount_allocations (B W : ℕ) :
    (mulModCount (m := m) B W).allocations = ModExp.mulModLen (m := m) B W := by
  unfold mulModCount ModExp.mulModLen
  simp only [Count.add_allocations, Count.zero]
  ring

/-- The `modExpLoop` over a bit list costs `(bs.length + bs.count true)` copies of
`mulModCount` (one squaring per bit, one extra multiply per set bit). -/
theorem costIs_modExpLoop (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)),
      CostIs (ModExp.modExpLoop P base n bs acc)
        ⟨(bs.length + bs.count true) * (mulModCount (m := m) P.B P.W).allocations,
         (bs.length + bs.count true) * (mulModCount (m := m) P.B P.W).constraints⟩ := by
  intro bs
  induction bs with
  | nil =>
    intro acc
    simp only [ModExp.modExpLoop, List.length_nil, List.count_nil, Nat.zero_add, Nat.zero_mul]
    exact CostIs.pure _
  | cons bit rest ih =>
    intro acc
    set K := mulModCount (m := m) P.B P.W with hK
    rw [show ModExp.modExpLoop P base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulMod.circuit P) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExp.modExpLoop P base n rest acc') from rfl]
    cases bit
    · -- clear bit: one squaring MulMod, then recurse
      have hcount : (Count.mk ((rest.length + 1 + rest.count true) * K.allocations)
            ((rest.length + 1 + rest.count true) * K.constraints))
          = (K + (Count.zero +
              Count.mk ((rest.length + rest.count true) * K.allocations)
               ((rest.length + rest.count true) * K.constraints)) : Count) := by
        congr 1 <;> simp only [Count.add_allocations, Count.add_constraints, Count.zero] <;> ring
      simp only [List.length_cons, List.count_cons, Bool.false_eq_true, if_false, Nat.add_zero,
        beq_iff_eq, hcount]
      refine CostIs.bind (costIs_sub_mulMod P _) fun sq => ?_
      exact CostIs.bind (CostIs.pure sq) fun acc' => ih acc'
    · -- set bit: squaring + multiply, then recurse
      have hcount : (Count.mk ((rest.length + 1 + (rest.count true + 1)) * K.allocations)
            ((rest.length + 1 + (rest.count true + 1)) * K.constraints))
          = (K + (K +
              Count.mk ((rest.length + rest.count true) * K.allocations)
               ((rest.length + rest.count true) * K.constraints)) : Count) := by
        congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring
      simp only [List.length_cons, List.count_cons, beq_self_eq_true, if_true, hcount]
      refine CostIs.bind (costIs_sub_mulMod P _) fun sq => ?_
      exact CostIs.bind (costIs_sub_mulMod P _) fun acc' => ih acc'

theorem costIs_modExp (P : RSAParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (ModExp.Inputs m) (F circomPrime)) :
    CostIs (ModExp.main P input)
      ⟨ModExp.modExpCount P.e * (mulModCount (m := m) P.bigIntParams.B P.bigIntParams.W).allocations,
       ModExp.modExpCount P.e * (mulModCount (m := m) P.bigIntParams.B P.bigIntParams.W).constraints⟩ := by
  unfold ModExp.main ModExp.modExpCount
  cases h : ModExp.eBits P.e with
  | nil =>
    simp only [Nat.zero_mul]
    exact CostIs.pure _
  | cons headBit tail =>
    simp only []
    exact costIs_modExpLoop P.bigIntParams _ _ tail _

theorem costIs_sub_modExp (P : RSAParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExp.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (ModExp.circuit P) b)
      ⟨ModExp.modExpCount P.e * (mulModCount (m := m) P.bigIntParams.B P.bigIntParams.W).allocations,
       ModExp.modExpCount P.e * (mulModCount (m := m) P.bigIntParams.B P.bigIntParams.W).constraints⟩ :=
  CostIs.subcircuit (fun n => costIs_modExp P b n)

/-! ## Byte glue — `ByteBlock`, `BytesToBigInt`, `PadDigest` -/

/-- `ByteBlock.main` inlines a 256-row booleanity loop (`bit·(bit−1) = 0`) and a
32-row digest-consistency loop (one constraint per byte), no witnesses:
`⟨0, 288⟩` (`256·1 + 32·1`). -/
theorem costIs_byteBlock (input : Var ByteBlock.Inputs (F circomPrime)) :
    CostIs (ByteBlock.main input)
      (⟨256 * 0, 256 * 1⟩ + ⟨32 * 0, 32 * 1⟩) := by
  unfold ByteBlock.main
  refine CostIs.bind
    (show CostIs (Circuit.forEach input.bits (fun b => assertZero (b * (b - 1)))) ⟨256 * 0, 256 * 1⟩
      from CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.forEach fun a k => CostIs.assertZero _ k

/-- Each inlined row — the booleanity row `b·(b−1)` and each digest-consistency
row `byte − byteFromBits …` — is R1CS, given affine bits and bytes. -/
theorem isR1CS_byteBlock (input : Var ByteBlock.Inputs (F circomPrime))
    (hbits : ∀ i (hi : i < 256), Affine input.bits[i])
    (hbytes : ∀ j (hj : j < 32), Affine input.bytes[j]) :
    IsR1CSCirc (ByteBlock.main input) := by
  unfold ByteBlock.main
  refine IsR1CSCirc.bind
    (show IsR1CSCirc (Circuit.forEach input.bits (fun b => assertZero (b * (b - 1)))) from ?_)
    fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (hbits i.val i.isLt) (Affine.sub (hbits i.val i.isLt) (Affine.const 1))
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_ofFn]
    refine isR1CSRow_of_affine (Affine.sub (hbytes i.val i.isLt) ?_)
    unfold Bytes.byteFromBits
    apply affine_finFoldl'
    · exact Affine.zero
    · intro acc t hacc
      refine Affine.add hacc ?_
      split
      · exact Affine.mul_deg0 (hbits _ (by assumption)) (degree_const _)
      · exact Affine.mul_deg0 Affine.zero (degree_const _)

theorem costIs_assertion_byteBlock (input : Var ByteBlock.Inputs (F circomPrime)) :
    CostIs (assertion ByteBlock.circuit input) ⟨0, 288⟩ :=
  CostIs.assertion (fun n => costIs_byteBlock input n)

theorem isR1CS_assertion_byteBlock (input : Var ByteBlock.Inputs (F circomPrime))
    (hbits : ∀ i (hi : i < 256), Affine input.bits[i])
    (hbytes : ∀ j (hj : j < 32), Affine input.bytes[j]) :
    IsR1CSCirc (assertion ByteBlock.circuit input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_byteBlock input hbits hbytes n)

/-- Each limb of `packLimbs bits` is an affine fold `Σ bit·2^t` of the (affine)
bits, hence affine. -/
theorem affineW_packLimbs (bits : Vector (Expression (F circomPrime)) Bytes.totalBits)
    (hbits : ∀ p (hp : p < Bytes.totalBits), Affine bits[p]) :
    AffineW (Bytes.packLimbs bits) := by
  intro k hk
  rw [Bytes.packLimbs, Vector.getElem_ofFn]
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc t hacc
    refine Affine.add hacc ?_
    split
    · exact Affine.mul_deg0 (hbits _ (by assumption)) (degree_const _)
    · exact Affine.mul_deg0 Affine.zero (degree_const _)

/-- Each bit of `emBits digBits` is either a (affine) digest bit or a constant. -/
theorem affineW_emBits (digBits : Vector (Expression (F circomPrime)) 256)
    (hbits : ∀ p (hp : p < 256), Affine digBits[p]) :
    ∀ p (hp : p < Bytes.totalBits), Affine (Bytes.emBits digBits)[p] := by
  intro p hp
  rw [Bytes.emBits, Vector.getElem_ofFn]
  split
  · exact hbits _ (by assumption)
  · exact Affine.const _

/-- The output limbs of a `BytesToBigInt` subcircuit (= `packLimbs (varFromOffset
…)`) are affine. -/
theorem affineW_sub_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit BytesToBigInt.circuit bytes).output n) := by
  have h : (subcircuit BytesToBigInt.circuit bytes).output n
      = Bytes.packLimbs (varFromOffset (fields Bytes.totalBits) n) := by
    simp only [circuit_norm, subcircuit, BytesToBigInt.circuit, BytesToBigInt.elaborated]
  rw [h]
  exact affineW_packLimbs _ (fun p hp => affineW_varFromOffset _ _ p hp)

/-- The output limbs of a `PadDigest` subcircuit (= `packLimbs (emBits
(varFromOffset …))`) are affine. -/
theorem affineW_sub_padDigest (digest : Var (fields digestBytesLen) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit PadDigest.circuit digest).output n) := by
  have h : (subcircuit PadDigest.circuit digest).output n
      = Bytes.packLimbs (Bytes.emBits (varFromOffset (fields 256) n)) := by
    simp only [circuit_norm, subcircuit, PadDigest.circuit, PadDigest.elaborated]
  rw [h]
  exact affineW_packLimbs _ (affineW_emBits _ (fun p hp => affineW_varFromOffset _ _ p hp))

/-- The output limbs of a `MulMod` subcircuit are a fresh `varFromOffset`
(the remainder `r`), hence affine. -/
theorem affineW_sub_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (MulMod.circuit P) b).output n) := by
  have h : (subcircuit (MulMod.circuit P) b).output n = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, MulMod.circuit, MulMod.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

-- Keep the heavy affine folds opaque so `unfold *.main` below stays cheap.
attribute [local irreducible] Bytes.packLimbs Bytes.emBits Bytes.byteFromBits

/-- `BytesToBigInt.main` = witness 4096 bits + 16 `ByteBlock` assertions
(`16·288 = 4608` constraints) + pure `packLimbs`: `⟨4096, 4608⟩`. -/
theorem costIs_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime)) :
    CostIs (BytesToBigInt.main bytes) ⟨4096, 4608⟩ := by
  unfold BytesToBigInt.main
  rw [show (⟨4096, 4608⟩ : Count) = ⟨Bytes.totalBits, 0⟩ + (⟨16 * 0, 16 * 288⟩ + Count.zero) from by
      simp only [Count.zero, Bytes.totalBits]; congr 1]
  refine CostIs.bind (CostIs.witnessVector Bytes.totalBits _) fun allBits => ?_
  refine CostIs.bind
    (show CostIs (Circuit.forEach (Vector.finRange 16) _ _) ⟨16 * 0, 16 * 288⟩
      from CostIs.forEach fun b k => costIs_assertion_byteBlock _ k) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime)) :
    CostIs (subcircuit BytesToBigInt.circuit bytes) ⟨4096, 4608⟩ :=
  CostIs.subcircuit (fun n => costIs_bytesToBigInt bytes n)

/-- `PadDigest.main` = witness 256 bits + one `ByteBlock` assertion (288
constraints) + pure `packLimbs (emBits …)`: `⟨256, 288⟩`. -/
theorem costIs_padDigest (digest : Var (fields digestBytesLen) (F circomPrime)) :
    CostIs (PadDigest.main digest) ⟨256, 288⟩ := by
  unfold PadDigest.main
  rw [show (⟨256, 288⟩ : Count) = ⟨256, 0⟩ + (⟨0, 288⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1]
  refine CostIs.bind (CostIs.witnessVector 256 _) fun digBits => ?_
  refine CostIs.bind (costIs_assertion_byteBlock _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_padDigest (digest : Var (fields digestBytesLen) (F circomPrime)) :
    CostIs (subcircuit PadDigest.circuit digest) ⟨256, 288⟩ :=
  CostIs.subcircuit (fun n => costIs_padDigest digest n)

/-! ## R1CS certificates for `MulMod` / `ModExp` and the byte subcircuits

`MulMod` is fully single-row R1CS. The key is `witnessedMul`: instead of feeding
`EqViaCarries` the schoolbook convolution `bigIntMulNoReduce a b` (whose `k`-th
coefficient is a rank-≥2 *sum of products* `a[i]·b[k−i]`), each product `a[i]·b[j]`
is first witnessed as a fresh cell (one rank-1 row `a[i]·b[j] − pp[t] = 0`), so the
convolution coefficients `bigIntMulVars pp` fed to `EqViaCarries` are linear forms
over those cells — affine, hence single-R1CS-row clean (`affineW_bigIntMulVars`). -/

/-- **R1CS certificate for `MulMod`.**

`q`, `r` are witnessed (affine); `Normalize q/r`, the two `witnessedMul` blocks,
`EqViaCarries`, and `LessThan {r, n}` are each single-row R1CS once their inputs
are affine. The `EqViaCarries` inputs are affine because `witnessedMul` returns
the convolution as a linear form over the freshly witnessed products
(`affineW_witnessedMul_output`). -/
theorem isR1CS_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus) :
    IsR1CSCirc (MulMod.main P input) := by
  unfold MulMod.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  -- witness the two product matrices: `a·b` and `q·n` (each `m·m` rank-1 rows)
  refine IsR1CSCirc.bind_out (isR1CS_witnessedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_witnessedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  -- EqViaCarries on the affine coefficient vectors `Pc = bigIntMulVars (a·b)` and
  -- `S = bigIntMulVars (q·n) + r` (both linear forms over witnessed cells).
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarries P _ ?_ ?_) fun _ => ?_
  · -- `Pc` is the affine output of `witnessedMul a b`
    exact affineW_witnessedMul_output _ _ _
  · -- `S[i] = Sqn[i] (+ r[i])` is affine: a sum of affine witnessed forms
    intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_witnessedMul_output _ _ _ i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_witnessedMul_output _ _ _ i hi
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- LessThan {r, n}: r is the witnessed remainder (affine), n is affine
    refine isR1CS_assertion_lessThan P _ ?_ hn
    intro i hi
    change Affine (varFromOffset (BigInt m) nr : Var (BigInt m) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (MulMod.circuit P) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulMod P b ha hb hn n)

/-- **R1CS certificate for the `modExpLoop`.** Threads the invariant "the running
accumulator's limbs are affine" through the loop: each `MulMod` is R1CS (modulo
the `MulMod` gap), and its output (the remainder) is a fresh witness, hence affine. -/
theorem isR1CS_modExpLoop (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) (hbase : AffineW base) (hn : AffineW n) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)), AffineW acc →
      IsR1CSCirc (ModExp.modExpLoop P base n bs acc) := by
  intro bs
  induction bs with
  | nil => intro acc hacc; simp only [ModExp.modExpLoop]; exact IsR1CSCirc.pure _
  | cons bit rest ih =>
    intro acc hacc
    rw [show ModExp.modExpLoop P base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulMod.circuit P) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExp.modExpLoop P base n rest acc') from rfl]
    refine IsR1CSCirc.bind_out (isR1CS_sub_mulMod P _ hacc hacc hn) fun nsq => ?_
    have hsq : AffineW ((subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }).output nsq) :=
      affineW_sub_mulMod P _ nsq
    cases bit
    · simp only [Bool.false_eq_true, if_false]
      refine IsR1CSCirc.bind_out (IsR1CSCirc.pure _) fun nacc' => ?_
      exact ih _ hsq
    · simp only [if_true]
      refine IsR1CSCirc.bind_out (isR1CS_sub_mulMod P _ hsq hbase hn) fun nmul => ?_
      exact ih _ (affineW_sub_mulMod P _ nmul)

theorem isR1CS_modExp (P : RSAParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (ModExp.Inputs m) (F circomPrime))
    (hbase : AffineW input.base) (hn : AffineW input.modulus) :
    IsR1CSCirc (ModExp.main P input) := by
  unfold ModExp.main
  cases h : ModExp.eBits P.e with
  | nil =>
    simp only []
    intro k
    -- the `e = 0` branch returns the constant `1`, no operations
    rw [show (Vector.ofFn fun k : Fin m => if k.val = 0 then (1 : Expression (F circomPrime)) else 0)
          = (Vector.ofFn fun k : Fin m => if k.val = 0 then (1 : Expression (F circomPrime)) else 0) from rfl]
    exact (IsR1CSCirc.pure _ : IsR1CSCirc (pure _)) k
  | cons headBit tail =>
    simp only []
    exact isR1CS_modExpLoop P.bigIntParams _ _ hbase hn tail _ hbase

theorem isR1CS_sub_modExp (P : RSAParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExp.Inputs m) (F circomPrime))
    (hbase : AffineW b.base) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (ModExp.circuit P) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_modExp P b hbase hn n)

/-- The accumulator output of `modExpLoop` is affine: it is either the seed `acc`
(empty bit list) or a fresh `MulMod` remainder witness (`varFromOffset`). -/
theorem affineW_modExpLoop_output (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) (_hbase : AffineW base) (_hn : AffineW n) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)) (offset : ℕ), AffineW acc →
      AffineW ((ModExp.modExpLoop P base n bs acc).output offset) := by
  intro bs
  induction bs with
  | nil => intro acc offset hacc; simpa only [ModExp.modExpLoop, Circuit.pure_output_eq] using hacc
  | cons bit rest ih =>
    intro acc offset hacc
    rw [show ModExp.modExpLoop P base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulMod.circuit P) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExp.modExpLoop P base n rest acc') from rfl]
    rw [Circuit.bind_output_eq]
    cases bit
    · simp only [Bool.false_eq_true, if_false, Circuit.bind_output_eq, Circuit.pure_output_eq]
      exact ih _ _ (affineW_sub_mulMod P _ _)
    · simp only [if_true, Circuit.bind_output_eq]
      exact ih _ _ (affineW_sub_mulMod P _ _)

theorem affineW_sub_modExp (P : RSAParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExp.Inputs m) (F circomPrime)) (off : ℕ)
    (hbase : AffineW b.base) (hn : AffineW b.modulus) :
    AffineW ((subcircuit (ModExp.circuit P) b).output off) := by
  have h : (subcircuit (ModExp.circuit P) b).output off = (ModExp.main P b).output off := by
    simp only [circuit_norm, subcircuit, ModExp.circuit]
  rw [h]
  unfold ModExp.main
  cases hb : ModExp.eBits P.e with
  | nil =>
    simp only [Circuit.pure_output_eq]
    intro i hi
    rw [Vector.getElem_ofFn]
    split
    · exact Affine.const 1
    · exact Affine.zero
  | cons headBit tail =>
    exact affineW_modExpLoop_output P.bigIntParams _ _ hbase hn tail _ _ hbase

/-! ### Byte-subcircuit R1CS (fully R1CS — no gaps) -/

/-- Each `byteSlice` entry is an input byte, affine when the input bytes are. -/
theorem affine_byteSlice (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (hbytes : AffineW bytes) (b : Fin 16) (i : ℕ) (hi : i < 32) :
    Affine (BytesToBigInt.byteSlice bytes b)[i] := by
  rw [BytesToBigInt.byteSlice, Vector.getElem_ofFn]
  exact hbytes _ (by have := b.isLt; show 32 * b.val + i < 512; omega)

/-- Each `bitSlice` entry is a witnessed bit, affine. -/
theorem affine_bitSlice (allBits : Vector (Expression (F circomPrime)) Bytes.totalBits)
    (hbits : ∀ p (hp : p < Bytes.totalBits), Affine allBits[p]) (b : Fin 16) (i : ℕ) (hi : i < 256) :
    Affine (BytesToBigInt.bitSlice allBits b)[i] := by
  rw [BytesToBigInt.bitSlice, Vector.getElem_ofFn]
  exact hbits _ (by have := b.isLt; simp only [Bytes.totalBits]; omega)

theorem isR1CS_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (hbytes : AffineW bytes) : IsR1CSCirc (BytesToBigInt.main bytes) := by
  unfold BytesToBigInt.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec Bytes.totalBits _) fun nbits => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Fin 16) fun b k => ?_
    refine isR1CS_assertion_byteBlock _ ?_ ?_ k
    · intro i hi; exact affine_bitSlice _ (fun p hp => affineW_witnessVector_output _ _ _ p hp) _ i hi
    · intro j hj; exact affine_byteSlice _ hbytes _ j hj
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (hbytes : AffineW bytes) : IsR1CSCirc (subcircuit BytesToBigInt.circuit bytes) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_bytesToBigInt bytes hbytes n)

theorem isR1CS_padDigest (digest : Var (fields digestBytesLen) (F circomPrime))
    (hdigest : AffineW digest) : IsR1CSCirc (PadDigest.main digest) := by
  unfold PadDigest.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec 256 _) fun nbits => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_byteBlock _ ?_ ?_) fun _ => ?_
  · intro i hi
    exact affineW_witnessVector_output 256 (PadDigest.digestBitsWitness digest) nbits i hi
  · intro j hj; exact hdigest _ hj
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_padDigest (digest : Var (fields digestBytesLen) (F circomPrime))
    (hdigest : AffineW digest) : IsR1CSCirc (subcircuit PadDigest.circuit digest) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_padDigest digest hdigest n)

/-- The `modulus` slice of the offset-0 input allocation is a `varFromOffset`. -/
theorem affineW_input_modulus :
    AffineW (varFromOffset Input 0 : Var Input (F circomPrime)).modulus := by
  have h : (varFromOffset Input 0 : Var Input (F circomPrime)).modulus
      = varFromOffset (fields modulusBytesLen) 0 := by simp only [circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem affineW_input_signature :
    AffineW (varFromOffset Input 0 : Var Input (F circomPrime)).signature := by
  have h : (varFromOffset Input 0 : Var Input (F circomPrime)).signature
      = varFromOffset (fields modulusBytesLen) (modulusBytesLen + digestBytesLen) := by
    simp only [circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem affineW_input_digest :
    AffineW (varFromOffset Input 0 : Var Input (F circomPrime)).digest := by
  have h : (varFromOffset Input 0 : Var Input (F circomPrime)).digest
      = varFromOffset (fields digestBytesLen) modulusBytesLen := by simp only [circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

end GadgetCost
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
