import Solution.Secp256k1ScalarMulFixedBase.ScalarMul
import Challenge.Utils.CostR1CS
import Clean.Circuit.Loops

/-!
# Compositional cost (`CostIs`) and R1CS (`IsR1CSCirc`) facts for the secp256k1 gadgets

Bottom-up `operationCount` / `operationsIsR1CS` certificates for the gadget tree
of the scalar-multiplication circuit — the RSA-ported big-integer layer
(`rangeCheck`, `Normalize`, `Equal`, `LessThan`, `EqViaCarries`, `MulMod`), the
point-arithmetic layer (`Mux`, `IsZeroFe`, `AddMod`, `SubMod`, `DivOrZero`,
`ToBytes`, `CompleteAdd`, `Step`), and the 256-step double-and-add fold
(`ScalarMul`) — proved with the compositional lemmas in `Challenge.CostR1CS`
(no `native_decide`, no `decide` on circuit terms).

Per-gadget counts (verified against `#eval! operationCount` of the actual
circuits):

| gadget        | allocations | constraints |
|---------------|-------------|-------------|
| `IsZeroField` | 2           | 2           |
| `IsZeroFe`    | 11          | 11          |
| `Mux M`       | `size M`    | `size M`    |
| `Normalize`   | 256         | 260         |
| `Equal`       | 0           | 4           |
| `LessThan`    | 264         | 269         |
| `EqViaCarries`| 490         | 498         |
| `MulMod`      | 1306        | 1319        |
| `AddMod`      | 1015        | 1028        |
| `SubMod`      | 1015        | 1028        |
| `DivOrZero`   | 1849        | 1871        |
| `ToBytes`     | 288         | 292         |
| `CompleteAdd` | 15975       | 16166       |
| `Step`        | 31959       | 32341       |
| `ScalarMul`   | 8182144     | 8279944     |

The top-level `main`-specific assembly lives in `Main.lean`, which consumes
these.
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace Cost

open Challenge.CostR1CS

/-! ## Generic subcircuit / witness leaves -/

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

/-- The output of a `ProvableType.witness` is a fresh `varFromOffset`, hence
affine at every offset. -/
theorem affineProvable_provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) (n : ℕ) :
    AffineProvable ((ProvableType.witness (α := α) compute).output n) := by
  rw [show ((ProvableType.witness (α := α) compute).output n)
        = varFromOffset α n from rfl]
  exact affineProvable_varFromOffset n

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

/-! ## `Normalize` -/

variable {m : ℕ}

/-- `Normalize.main P x` range-checks each of the `m` limbs of `x`. -/
theorem costIs_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (Normalize.main P x) ⟨m * P.B, m * (P.B + 1)⟩ := by
  unfold Normalize.main
  exact CostIs.forEach (fun a n => costIs_assertion_rangeCheck P.B P.hB a n)

theorem isR1CS_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (Normalize.main P x) := by
  unfold Normalize.main
  exact IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
    fun i n => isR1CS_assertion_rangeCheck P.B P.hB x[i.val] (hx i.val i.isLt) n

theorem costIs_assertion_normalize (P : BigIntParams circomPrime m)
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (assertion (Normalize.circuit P) x) ⟨m * P.B, m * (P.B + 1)⟩ :=
  CostIs.assertion (fun n => costIs_normalize P x n)

theorem isR1CS_assertion_normalize (P : BigIntParams circomPrime m)
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

/-! ## `LessThan` -/

/-- Cost of `LessThan.main P input` (m ≥ 1): witness `d` (m), normalize `d`
(`m·B` / `m·(B+1)`), witness carries (m), boolean forEach (m constraints),
linear forEach (m constraints), and the forced top carry (1 constraint). -/
theorem costIs_lessThan (P : BigIntParams circomPrime m) [NeZero m]
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

theorem isR1CS_lessThan (P : BigIntParams circomPrime m) [NeZero m]
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

theorem costIs_assertion_lessThan (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime)) :
    CostIs (assertion (LessThan.circuit P) input)
      ⟨m + m * P.B + m, m * (P.B + 1) + m + m + 1⟩ :=
  CostIs.assertion (fun n => costIs_lessThan P input n)

theorem isR1CS_assertion_lessThan (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (LessThan.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_lessThan P input hl hr n)

/-! ## `EqViaCarries` -/

/-- Cost of `EqViaCarries.main P input` (m ≥ 1, so `2m-1 ≥ 1`): witness the
`2m-1` carries, range-check each to `W` bits, one linear constraint per index,
and the forced top carry. -/
theorem costIs_eqViaCarries (P : BigIntParams circomPrime m) [NeZero m]
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

theorem isR1CS_eqViaCarries (P : BigIntParams circomPrime m) [NeZero m]
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

theorem costIs_assertion_eqViaCarries (P : BigIntParams circomPrime m)
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (assertion (EqViaCarries.circuit P) input)
      ⟨(2 * m - 1) + (2 * m - 1) * P.W, (2 * m - 1) * (P.W + 1) + (2 * m - 1) + 1⟩ :=
  CostIs.assertion (fun n => costIs_eqViaCarries P input n)

theorem isR1CS_assertion_eqViaCarries (P : BigIntParams circomPrime m)
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (EqViaCarries.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_eqViaCarries P input hl hr n)

/-! ## `MulMod` -/

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
def mulModCount (m B W : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + (⟨m * B, m * (B + 1)⟩ + (⟨m * B, m * (B + 1)⟩ +
    (⟨m * m, m * m⟩ + (⟨m * m, m * m⟩ +
    (⟨(2 * m - 1) + (2 * m - 1) * W, (2 * m - 1) * (W + 1) + (2 * m - 1) + 1⟩ +
      (⟨m + m * B + m, m * (B + 1) + m + m + 1⟩ + Count.zero)))))))

theorem costIs_mulMod (P : BigIntParams circomPrime m) [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulMod.main P input) (mulModCount m P.B P.W) := by
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

theorem costIs_sub_mulMod (P : BigIntParams circomPrime m) [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (MulMod.circuit P) b) (mulModCount m P.B P.W) :=
  CostIs.subcircuit (fun n => costIs_mulMod P b n)

/-- **R1CS certificate for `MulMod`.**

`q`, `r` are witnessed (affine); `Normalize q/r`, the two `witnessedMul` blocks,
`EqViaCarries`, and `LessThan {r, n}` are each single-row R1CS once their inputs
are affine. The `EqViaCarries` inputs are affine because `witnessedMul` returns
the convolution as a linear form over the freshly witnessed products
(`affineW_witnessedMul_output`). -/
theorem isR1CS_mulMod (P : BigIntParams circomPrime m) [NeZero m]
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

theorem isR1CS_sub_mulMod (P : BigIntParams circomPrime m) [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (MulMod.circuit P) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulMod P b ha hb hn n)

/-- The output limbs of a `MulMod` subcircuit are a fresh `varFromOffset`
(the remainder `r`), hence affine. -/
theorem affineW_sub_mulMod (P : BigIntParams circomPrime m) [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (MulMod.circuit P) b).output n) := by
  have h : (subcircuit (MulMod.circuit P) b).output n = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, MulMod.circuit, MulMod.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-! ## Expression-row helpers for the point-arithmetic gadgets -/

/-- Prove a `Count` equality from its two projections (used to decompose a
target count into the syntactic sum a `CostIs.bind` chain produces). -/
theorem count_eq (a c : ℕ) {x : Count} (ha : x.allocations = a) (hc : x.constraints = c) :
    (⟨a, c⟩ : Count) = x := by
  cases x; cases ha; cases hc; rfl

theorem affine_one : Affine (1 : Expression (F circomPrime)) := Affine.const 1

/-- `A·B + C − D` with all of `A, B, C, D` affine is a single R1CS row — the
`Mux` row `sel·(t−f) + f − out`. -/
theorem isR1CSRow_mul_add_sub {A B C D : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) (hD : Affine D) :
    isR1CSRow (A * B + C - D) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (A * B + C + -D) = some 0
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (A * B + C + -D) = some 1
    rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hC, r1csProducts_of_affine hD]

/-- `w − (1 − A·B)` with `w, A, B` affine is a single R1CS row — the
`IsZeroField` assignment row `isZero − (1 − x·xInv)`. -/
theorem isR1CSRow_sub_one_sub_mul {w A B : Expression (F circomPrime)}
    (hw : Affine w) (hA : Affine A) (hB : Affine B) :
    isR1CSRow (w - (1 - A * B)) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
    show r1csProducts (w + -((1 : Expression (F circomPrime)) + -(A * B))) = some 0
    rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hw, r1csProducts_of_affine affine_one]
  · refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)
    show r1csProducts (w + -((1 : Expression (F circomPrime)) + -(A * B))) = some 1
    rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add, r1csProducts_neg, h,
        r1csProducts_of_affine hw, r1csProducts_of_affine affine_one]

/-! ## `===` and `<==` on single field expressions -/

/-- `x === y` on expressions is one `Equality` assertion: `⟨0, 1⟩`. -/
theorem costIs_assertEqField (x y : Expression (F circomPrime)) :
    CostIs (x === y) ⟨0, 1⟩ := by
  show CostIs (Expression.assertEquals x y) ⟨0, 1⟩
  unfold Expression.assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun m => ?_
  show operationCount ((Gadgets.Equality.main (M := id) (x, y)).operations m) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) m)

/-- `x === y` is single-row R1CS whenever the difference row `x − y` is. -/
theorem isR1CS_assertEqField {x y : Expression (F circomPrime)}
    (h : isR1CSRow (x - y)) : IsR1CSCirc (x === y) := by
  show IsR1CSCirc (Expression.assertEquals x y)
  unfold Expression.assertEquals
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit id) fun k => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := id) (x, y)).operations k)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
  refine IsR1CSCirc.assertZero ?_ j
  simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
  exact h

/-- `let w <== rhs` witnesses one cell and asserts one row: `⟨1, 1⟩`. -/
theorem costIs_assignEqField (rhs : Expression (F circomPrime)) :
    CostIs (HasAssignEq.assignEq (F := F circomPrime) rhs) ⟨1, 1⟩ := by
  rw [show (⟨1, 1⟩ : Count) = ⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero) from by decide]
  exact CostIs.bind (CostIs.witnessField _) fun w =>
    CostIs.bind (costIs_assertEqField _ rhs) fun _ => CostIs.pure _

/-- `let w <== rhs` is single-row R1CS whenever the row `w − rhs` is, for the
fresh cell `w`. -/
theorem isR1CS_assignEqField (rhs : Expression (F circomPrime))
    (h : ∀ w : Variable (F circomPrime), isR1CSRow (Expression.var w - rhs)) :
    IsR1CSCirc (HasAssignEq.assignEq (F := F circomPrime) rhs) := by
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun k => ?_
  exact IsR1CSCirc.bind (isR1CS_assertEqField (h ⟨k⟩)) fun _ => IsR1CSCirc.pure _

/-- The output of `let w <== rhs` is the fresh cell `w`, affine. -/
theorem affine_assignEq_output (rhs : Expression (F circomPrime)) (n : ℕ) :
    Affine ((HasAssignEq.assignEq (F := F circomPrime) rhs).output n) := Affine.var _

/-! ### The `Var field` (provable-type) instances of `===` / `<==`

When the operands' type is displayed as `Var field _` (e.g. subcircuit outputs
of `field`-valued gadgets), `===`/`<==` resolve to the `M (Expression F)`
instances with `M := field` — same operations, different terms. -/

theorem costIs_assertEqFieldM (x y : Var field (F circomPrime)) :
    CostIs (x === y) ⟨0, 1⟩ := by
  show CostIs (assertEquals (M := field) x y) ⟨0, 1⟩
  unfold assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun n => ?_
  show operationCount ((Gadgets.Equality.main (M := field) (x, y)).operations n) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) n)

theorem isR1CS_assertEqFieldM {x y : Var field (F circomPrime)}
    (h : isR1CSRow (x - y)) : IsR1CSCirc (x === y) := by
  show IsR1CSCirc (assertEquals (M := field) x y)
  unfold assertEquals
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit field) fun k => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := field) (x, y)).operations k)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
  refine IsR1CSCirc.assertZero ?_ j
  simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
  exact h

theorem costIs_assignEqFieldM (rhs : Var field (F circomPrime)) :
    CostIs (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) rhs) ⟨1, 1⟩ := by
  rw [show (⟨1, 1⟩ : Count) = ⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero) from by decide]
  exact CostIs.bind (CostIs.provableWitness (α := field) _) fun w =>
    CostIs.bind (costIs_assertEqFieldM _ rhs) fun _ => CostIs.pure _

theorem isR1CS_assignEqFieldM (rhs : Var field (F circomPrime))
    (h : ∀ w : Variable (F circomPrime), isR1CSRow (Expression.var w - rhs)) :
    IsR1CSCirc (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) rhs) := by
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun k => ?_
  exact IsR1CSCirc.bind (isR1CS_assertEqFieldM (h ⟨k⟩)) fun _ => IsR1CSCirc.pure _

/-- The output of a `Var field` `<==` is the fresh cell, affine. -/
theorem affine_assignEqFieldM_output (rhs : Var field (F circomPrime)) (n : ℕ) :
    Affine ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) rhs).output n) :=
  Affine.var _

/-! ## `IsZeroField` (Clean's stock zero-test gadget) -/

/-- `IsZeroField.main x` witnesses `xInv` and `isZero` and asserts two rows:
`⟨2, 2⟩`. -/
theorem costIs_isZeroField (x : Expression (F circomPrime)) :
    CostIs (Gadgets.IsZeroField.main x) ⟨2, 2⟩ := by
  rw [show (⟨2, 2⟩ : Count) = ⟨1, 0⟩ + (⟨1, 1⟩ + (⟨0, 1⟩ + Count.zero)) from by decide]
  unfold Gadgets.IsZeroField.main
  refine CostIs.bind (CostIs.witnessField _) fun xInv => ?_
  refine CostIs.bind (costIs_assignEqField _) fun isZero => ?_
  exact CostIs.bind (costIs_assertEqField _ _) fun _ => CostIs.pure _

/-- Both `IsZeroField` rows are single R1CS rows when `x` is affine:
`isZero − (1 − x·xInv)` and `isZero·x − 0`. -/
theorem isR1CS_isZeroField (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.IsZeroField.main x) := by
  unfold Gadgets.IsZeroField.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nInv => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqField _ fun w =>
    isR1CSRow_sub_one_sub_mul (Affine.var w) hx (Affine.var _)) fun nz => ?_
  refine IsR1CSCirc.bind (isR1CS_assertEqField ?_) fun _ => IsR1CSCirc.pure _
  exact isR1CSRow_mul_sub (affine_assignEq_output _ nz) hx (Affine.const 0)

theorem costIs_sub_isZeroField (x : Expression (F circomPrime)) :
    CostIs (subcircuit Gadgets.IsZeroField.circuit x) ⟨2, 2⟩ :=
  CostIs.subcircuit (fun n => costIs_isZeroField x n)

theorem isR1CS_sub_isZeroField (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (subcircuit Gadgets.IsZeroField.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_isZeroField x hx n)

/-- The output of an `IsZeroField` subcircuit is the fresh `isZero` cell,
affine. -/
theorem affine_sub_isZeroField (x : Expression (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit Gadgets.IsZeroField.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, Gadgets.IsZeroField.circuit,
    Gadgets.IsZeroField.elaborated]
  exact Affine.var _

/-! ## `Mux` (materialized boolean selection) -/

/-- `Mux.main` witnesses the `size M` output cells and asserts one selection
row per cell: `⟨size M, size M⟩`. -/
theorem costIs_mux {M : TypeMap} [ProvableType M]
    (input : Var (Mux.Inputs M) (F circomPrime)) :
    CostIs (Mux.main input) ⟨size M, size M⟩ := by
  obtain ⟨sel, t, f⟩ := input
  rw [show (⟨size M, size M⟩ : Count)
        = ⟨size M, 0⟩ + (⟨size M * 0, size M * 1⟩ + Count.zero) from
      count_eq _ _ (by simp only [Count.add_allocations, Count.zero]; omega)
        (by simp only [Count.add_constraints, Count.zero]; omega)]
  unfold Mux.main
  refine CostIs.bind (CostIs.provableWitness _) fun out => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _

/-- Each `Mux` row `sel·(t_i − f_i) + f_i − out_i` is a single R1CS row for an
affine selector and affine candidate values (the outputs are fresh cells). -/
theorem isR1CS_mux {M : TypeMap} [ProvableType M]
    (input : Var (Mux.Inputs M) (F circomPrime))
    (hsel : Affine input.selector)
    (ht : AffineProvable input.ifTrue) (hf : AffineProvable input.ifFalse) :
    IsR1CSCirc (Mux.main input) := by
  obtain ⟨sel, t, f⟩ := input
  unfold Mux.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nout => ?_
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_ofFn]
  exact isR1CSRow_mul_add_sub hsel
    (Affine.sub (ht i.val i.isLt) (hf i.val i.isLt)) (hf i.val i.isLt)
    (affineProvable_provableWitness _ nout i.val i.isLt)

theorem costIs_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime)) :
    CostIs (subcircuit (Mux.circuit (M := M)) b) ⟨size M, size M⟩ :=
  CostIs.subcircuit (fun n => costIs_mux b n)

theorem isR1CS_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime))
    (hsel : Affine b.selector)
    (ht : AffineProvable b.ifTrue) (hf : AffineProvable b.ifFalse) :
    IsR1CSCirc (subcircuit (Mux.circuit (M := M)) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mux b hsel ht hf n)

/-- The output of a `Mux` subcircuit is the fresh witness block, a
`varFromOffset`, hence affine. -/
theorem affineProvable_sub_mux {M : TypeMap} [ProvableType M]
    (b : Var (Mux.Inputs M) (F circomPrime)) (n : ℕ) :
    AffineProvable ((subcircuit (Mux.circuit (M := M)) b).output n) := by
  have h : (subcircuit (Mux.circuit (M := M)) b).output n = varFromOffset M n := by
    simp only [circuit_norm, subcircuit, Mux.circuit, Mux.elaborated]
  rw [h]
  exact affineProvable_varFromOffset n

/-! ## `IsZeroFe` (emulated-field zero test) -/

theorem costIs_isZeroFe (x : Var Emu (F circomPrime)) :
    CostIs (IsZeroFe.main x) ⟨11, 11⟩ := by
  rw [show (⟨11, 11⟩ : Count)
        = ⟨2, 2⟩ + (⟨2, 2⟩ + (⟨2, 2⟩ + (⟨2, 2⟩ +
            (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + Count.zero)))))) from by decide]
  unfold IsZeroFe.main
  refine CostIs.bind (costIs_sub_isZeroField _) fun z0 => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun z1 => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun z2 => ?_
  refine CostIs.bind (costIs_sub_isZeroField _) fun z3 => ?_
  refine CostIs.bind (costIs_assignEqFieldM _) fun t01 => ?_
  refine CostIs.bind (costIs_assignEqFieldM _) fun t23 => ?_
  exact CostIs.bind (costIs_assignEqFieldM _) fun z => CostIs.pure _

theorem isR1CS_isZeroFe (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (IsZeroFe.main x) := by
  unfold IsZeroFe.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 0 (by decide))) fun n0 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 1 (by decide))) fun n1 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 2 (by decide))) fun n2 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroField _ (hx 3 (by decide))) fun n3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_sub_isZeroField _ n0)
      (affine_sub_isZeroField _ n1)) fun n4 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_sub_isZeroField _ n2)
      (affine_sub_isZeroField _ n3)) fun n5 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_assignEqFieldM_output _ n4)
      (affine_assignEqFieldM_output _ n5)) fun n6 => ?_
  exact IsR1CSCirc.pure _

theorem costIs_sub_isZeroFe (x : Var Emu (F circomPrime)) :
    CostIs (subcircuit IsZeroFe.circuit x) ⟨11, 11⟩ :=
  CostIs.subcircuit (fun n => costIs_isZeroFe x n)

theorem isR1CS_sub_isZeroFe (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (subcircuit IsZeroFe.circuit x) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_isZeroFe x hx n)

/-- The output of an `IsZeroFe` subcircuit is the fresh `z` cell, affine. -/
theorem affine_sub_isZeroFe (x : Var Emu (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit IsZeroFe.circuit x).output n) := by
  simp only [circuit_norm, subcircuit, IsZeroFe.circuit, IsZeroFe.elaborated]
  exact Affine.var _

/-! ## Constant limbs and single-field witnesses -/

/-- Every limb of an `emuConst` is a constant expression (degree 0). -/
theorem degree_emuConst (v : ℕ) (i : ℕ) (hi : i < numLimbs) :
    degree (emuConst v : Var Emu (F circomPrime))[i] = 0 := by
  unfold emuConst
  rw [Vector.getElem_ofFn]
  exact degree_const _

theorem affineW_emuConst (v : ℕ) : AffineW (emuConst v : Var Emu (F circomPrime)) := by
  intro i hi
  unfold emuConst
  rw [Vector.getElem_ofFn]
  exact Affine.const _

theorem affineW_pConst : AffineW (pConst : Var Emu (F circomPrime)) :=
  affineW_emuConst P256

theorem degree_pConst (i : ℕ) (hi : i < numLimbs) :
    degree (pConst : Var Emu (F circomPrime))[i] = 0 :=
  degree_emuConst P256 i hi

/-- The output of a single-field `ProvableType.witness` is a fresh cell, affine. -/
theorem affine_provableWitness_field
    (c : ProverEnvironment (F circomPrime) → field (F circomPrime)) (n : ℕ) :
    Affine ((ProvableType.witness (α := field) c).output n) := Affine.var _

/-! ## `AddMod` / `SubMod` (emulated field addition / subtraction) -/

def addModCost : Count := ⟨1015, 1028⟩

theorem costIs_addMod (input : Var AddMod.Inputs (F circomPrime)) :
    CostIs (AddMod.main input) addModCost := by
  obtain ⟨a, b⟩ := input
  rw [show addModCost
        = ⟨4, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨256, 260⟩ + (⟨264, 269⟩ +
            (⟨490, 498⟩ + Count.zero))))) from by decide]
  unfold AddMod.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarries secpParams _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_addMod (input : Var AddMod.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) :
    IsR1CSCirc (AddMod.main input) := by
  obtain ⟨a, b⟩ := input
  unfold AddMod.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nq => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nq)
      (Affine.sub (affine_provableWitness_field _ nq) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize secpParams _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_lessThan secpParams _ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nr : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact affineW_pConst
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarries secpParams _ ?_ ?_) fun _ =>
    IsR1CSCirc.pure _
  · -- lhs[k] = a[k] + b[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (ha _ (by assumption)) (hb _ (by assumption))
    · exact Affine.zero
  · -- rhs[k] = q·p[k] + r[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add
        (Affine.mul_deg0 (affine_provableWitness_field _ nq) (degree_pConst _ (by assumption)))
        (affineW_provableWitness_bigInt _ nr _ (by assumption))
    · exact Affine.zero

theorem costIs_sub_addMod (b : Var AddMod.Inputs (F circomPrime)) :
    CostIs (subcircuit AddMod.circuit b) addModCost :=
  CostIs.subcircuit (fun n => costIs_addMod b n)

theorem isR1CS_sub_addMod (b : Var AddMod.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) :
    IsR1CSCirc (subcircuit AddMod.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_addMod b ha hb n)

/-- The output of an `AddMod` subcircuit is the freshly witnessed `r`, affine. -/
theorem affineW_sub_addMod (b : Var AddMod.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit AddMod.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, AddMod.circuit, AddMod.elaborated]
  exact affineW_varFromOffset _ _

def subModCost : Count := ⟨1015, 1028⟩

theorem costIs_subMod (input : Var SubMod.Inputs (F circomPrime)) :
    CostIs (SubMod.main input) subModCost := by
  obtain ⟨a, b⟩ := input
  rw [show subModCost
        = ⟨4, 0⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨256, 260⟩ + (⟨264, 269⟩ +
            (⟨490, 498⟩ + Count.zero))))) from by decide]
  unfold SubMod.main
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarries secpParams _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_subMod (input : Var SubMod.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) :
    IsR1CSCirc (SubMod.main input) := by
  obtain ⟨a, b⟩ := input
  unfold SubMod.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness (α := field) _) fun nq => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affine_provableWitness_field _ nq)
      (Affine.sub (affine_provableWitness_field _ nq) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize secpParams _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_lessThan secpParams _ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nr : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact affineW_pConst
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarries secpParams _ ?_ ?_) fun _ =>
    IsR1CSCirc.pure _
  · -- lhs[k] = r[k] + b[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_provableWitness_bigInt _ nr _ (by assumption))
        (hb _ (by assumption))
    · exact Affine.zero
  · -- rhs[k] = a[k] + q·p[k] (k < 4) or 0
    intro k hk
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (ha _ (by assumption))
        (Affine.mul_deg0 (affine_provableWitness_field _ nq) (degree_pConst _ (by assumption)))
    · exact Affine.zero

theorem costIs_sub_subMod (b : Var SubMod.Inputs (F circomPrime)) :
    CostIs (subcircuit SubMod.circuit b) subModCost :=
  CostIs.subcircuit (fun n => costIs_subMod b n)

theorem isR1CS_sub_subMod (b : Var SubMod.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) :
    IsR1CSCirc (subcircuit SubMod.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_subMod b ha hb n)

/-- The output of a `SubMod` subcircuit is the freshly witnessed `r`, affine. -/
theorem affineW_sub_subMod (b : Var SubMod.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit SubMod.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, SubMod.circuit, SubMod.elaborated]
  exact affineW_varFromOffset _ _

/-! ## `DivOrZero` (witnessed division with zero guard) -/

def divOrZeroCost : Count := ⟨1849, 1871⟩

theorem costIs_divOrZero (input : Var DivOrZero.Inputs (F circomPrime)) :
    CostIs (DivOrZero.main input) divOrZeroCost := by
  obtain ⟨num, den⟩ := input
  rw [show divOrZeroCost
        = ⟨11, 11⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 0⟩ + (⟨256, 260⟩ + (⟨264, 269⟩ +
            (⟨1306, 1319⟩ + (⟨0, 4⟩ + Count.zero))))))) from by decide]
  unfold DivOrZero.main
  refine CostIs.bind (costIs_sub_isZeroFe _) fun z => ?_
  refine CostIs.bind (costIs_sub_mux _) fun denSafe => ?_
  refine CostIs.bind (costIs_sub_mux _) fun numSafe => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun lam => ?_
  refine CostIs.bind (costIs_assertion_normalize secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan secpParams _) fun _ => ?_
  refine CostIs.bind (costIs_sub_mulMod secpParams _) fun prod => ?_
  refine CostIs.bind (costIs_assertion_equal secpParams _) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_divOrZero (input : Var DivOrZero.Inputs (F circomPrime))
    (hnum : AffineW input.num) (hden : AffineW input.den) :
    IsR1CSCirc (DivOrZero.main input) := by
  obtain ⟨num, den⟩ := input
  unfold DivOrZero.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroFe _ hden) fun nz => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nd => ?_
  · exact affine_sub_isZeroFe _ nz
  · exact (affineW_emuConst 1).affineProvable
  · exact hden.affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nn => ?_
  · exact affine_sub_isZeroFe _ nz
  · exact (affineW_emuConst 0).affineProvable
  · exact hnum.affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nl => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_normalize secpParams _ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  refine IsR1CSCirc.bind (isR1CS_assertion_lessThan secpParams _ ?_ ?_) fun _ => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact affineW_pConst
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulMod secpParams _ ?_ ?_ ?_) fun np => ?_
  · intro i hi
    change Affine (varFromOffset (BigInt numLimbs) nl : Var (BigInt numLimbs) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  · exact (affineProvable_sub_mux _ nd).affineW
  · exact affineW_pConst
  refine IsR1CSCirc.bind (isR1CS_assertion_equal secpParams _ ?_ ?_) fun _ => ?_
  · exact affineW_sub_mulMod secpParams _ np
  · exact (affineProvable_sub_mux _ nn).affineW
  exact IsR1CSCirc.pure _

theorem costIs_sub_divOrZero (b : Var DivOrZero.Inputs (F circomPrime)) :
    CostIs (subcircuit DivOrZero.circuit b) divOrZeroCost :=
  CostIs.subcircuit (fun n => costIs_divOrZero b n)

theorem isR1CS_sub_divOrZero (b : Var DivOrZero.Inputs (F circomPrime))
    (hnum : AffineW b.num) (hden : AffineW b.den) :
    IsR1CSCirc (subcircuit DivOrZero.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_divOrZero b hnum hden n)

/-- The output of a `DivOrZero` subcircuit is the freshly witnessed `λ`, affine. -/
theorem affineW_sub_divOrZero (b : Var DivOrZero.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit DivOrZero.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, DivOrZero.circuit, DivOrZero.elaborated]
  exact affineW_varFromOffset _ _

/-! ## `ToBytes` (byte decomposition of an emulated field element) -/

def toBytesCost : Count := ⟨288, 292⟩

theorem costIs_toBytes (x : Var Emu (F circomPrime)) :
    CostIs (ToBytes.main x) toBytesCost := by
  rw [show toBytesCost
        = ⟨32, 0⟩ + (⟨32 * 8, 32 * (8 + 1)⟩ + (⟨4 * 0, 4 * 1⟩ + Count.zero)) from by decide]
  unfold ToBytes.main
  refine CostIs.bind (CostIs.provableWitness _) fun bytes => ?_
  refine CostIs.bind
    (CostIs.forEach fun a n => costIs_assertion_rangeCheck 8 (by decide) a n) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _

theorem isR1CS_toBytes (x : Var Emu (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (ToBytes.main x) := by
  unfold ToBytes.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nb => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine isR1CS_assertion_rangeCheck 8 (by decide) _ ?_ k
    exact (affineProvable_provableWitness _ nb).affineW i.val i.isLt
  refine IsR1CSCirc.bind ?_ fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun k j => ?_
  refine IsR1CSCirc.assertZero ?_ j
  rw [Vector.getElem_ofFn]
  refine isR1CSRow_of_affine (Affine.sub ?_ (hx _ (by exact k.isLt)))
  refine affine_finFoldl' _ _ Affine.zero fun acc t hacc => ?_
  exact Affine.add hacc
    (Affine.mul_deg0 ((affineProvable_provableWitness _ nb).affineW _ (by
      have hk := k.isLt; have ht := t.isLt
      simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
      omega)) (degree_const _))

theorem costIs_sub_toBytes (b : Var Emu (F circomPrime)) :
    CostIs (subcircuit ToBytes.circuit b) toBytesCost :=
  CostIs.subcircuit (fun n => costIs_toBytes b n)

theorem isR1CS_sub_toBytes (b : Var Emu (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit ToBytes.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_toBytes b hb n)

/-- The output of a `ToBytes` subcircuit is the freshly witnessed byte block,
affine. -/
theorem affineW_sub_toBytes (b : Var Emu (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit ToBytes.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, ToBytes.circuit, ToBytes.elaborated]
  exact affineW_varFromOffset _ _

/-! ## Flagged-point affineness -/

/-- Componentwise affineness of a flagged-point variable: the accumulator
invariant threaded through the double-and-add fold. -/
def AffineFP (v : Var FlaggedPoint (F circomPrime)) : Prop :=
  AffineW v.x ∧ AffineW v.y ∧ Affine v.isInf

/-- Decompose `AffineProvable` on a flagged point into its components
(`toElements` is the flat append `v.x ++ (v.y ++ #v[v.isInf])`). -/
theorem AffineFP.of_affineProvable {v : Var FlaggedPoint (F circomPrime)}
    (h : AffineProvable v) : AffineFP v := by
  have hflat : AffineW
      (v.x ++ (v.y ++ #v[v.isInf]) :
        fields (numLimbs + (numLimbs + 1)) (Expression (F circomPrime))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using h i (by exact hi)
  refine ⟨AffineW.left_of_append hflat,
    AffineW.left_of_append (AffineW.right_of_append hflat), ?_⟩
  have h1 := AffineW.right_of_append (AffineW.right_of_append hflat) 0 (by decide)
  simpa using h1

/-- Appending affine vectors stays affine (inverse of
`AffineW.left_of_append` / `AffineW.right_of_append`). -/
theorem AffineW.append {m n : ℕ}
    {a : fields m (Expression (F circomPrime))} {b : fields n (Expression (F circomPrime))}
    (ha : AffineW a) (hb : AffineW b) :
    AffineW (a ++ b : fields (m + n) (Expression (F circomPrime))) := by
  intro i hi
  rw [Vector.getElem_append]
  split
  · exact ha _ _
  · exact hb _ _

theorem affineW_singleton {e : Expression (F circomPrime)} (he : Affine e) :
    AffineW (#v[e] : fields 1 (Expression (F circomPrime))) := by
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  simpa using he

/-- Assemble `AffineProvable` on a flagged point from its components. -/
theorem AffineFP.affineProvable {v : Var FlaggedPoint (F circomPrime)}
    (h : AffineFP v) : AffineProvable v := by
  obtain ⟨hx, hy, hi⟩ := h
  intro j hj
  simp only [circuit_norm, explicit_provable_type]
  exact AffineW.append hx (AffineW.append hy (affineW_singleton hi)) j hj

theorem affineFP_infConst : AffineFP (infConst : Var FlaggedPoint (F circomPrime)) :=
  ⟨affineW_emuConst 0, affineW_emuConst 0, Affine.const 1⟩

theorem affineProvable_infConst :
    AffineProvable (infConst : Var FlaggedPoint (F circomPrime)) :=
  affineFP_infConst.affineProvable

/-! ## `CompleteAdd` (complete secp256k1 group law) -/

def completeAddCost : Count := ⟨15975, 16166⟩

theorem costIs_completeAdd (input : Var CompleteAdd.Inputs (F circomPrime)) :
    CostIs (CompleteAdd.main input) completeAddCost := by
  obtain ⟨P, Q⟩ := input
  rw [show completeAddCost
        = ⟨1015, 1028⟩ + (⟨1015, 1028⟩ + (⟨11, 11⟩ + (⟨1015, 1028⟩ + (⟨11, 11⟩ +
            (⟨1306, 1319⟩ + (⟨1015, 1028⟩ + (⟨1015, 1028⟩ + (⟨1015, 1028⟩ + (⟨4, 4⟩ +
            (⟨4, 4⟩ + (⟨1849, 1871⟩ + (⟨1306, 1319⟩ + (⟨1015, 1028⟩ + (⟨1015, 1028⟩ +
            (⟨1015, 1028⟩ + (⟨1306, 1319⟩ + (⟨1015, 1028⟩ + (⟨1, 1⟩ + (⟨9, 9⟩ +
            (⟨9, 9⟩ + (⟨9, 9⟩ + Count.zero))))))))))))))))))))) from by decide]
  unfold CompleteAdd.main
  refine CostIs.bind (costIs_sub_subMod _) fun dx => ?_
  refine CostIs.bind (costIs_sub_subMod _) fun dy => ?_
  refine CostIs.bind (costIs_sub_isZeroFe _) fun sameX => ?_
  refine CostIs.bind (costIs_sub_addMod _) fun sy => ?_
  refine CostIs.bind (costIs_sub_isZeroFe _) fun oppY => ?_
  refine CostIs.bind (costIs_sub_mulMod secpParams _) fun x1sq => ?_
  refine CostIs.bind (costIs_sub_addMod _) fun x1sq2 => ?_
  refine CostIs.bind (costIs_sub_addMod _) fun tNum => ?_
  refine CostIs.bind (costIs_sub_addMod _) fun tDen => ?_
  refine CostIs.bind (costIs_sub_mux _) fun num => ?_
  refine CostIs.bind (costIs_sub_mux _) fun den => ?_
  refine CostIs.bind (costIs_sub_divOrZero _) fun lam => ?_
  refine CostIs.bind (costIs_sub_mulMod secpParams _) fun lamSq => ?_
  refine CostIs.bind (costIs_sub_subMod _) fun xs => ?_
  refine CostIs.bind (costIs_sub_subMod _) fun x3 => ?_
  refine CostIs.bind (costIs_sub_subMod _) fun xd => ?_
  refine CostIs.bind (costIs_sub_mulMod secpParams _) fun yprod => ?_
  refine CostIs.bind (costIs_sub_subMod _) fun y3 => ?_
  refine CostIs.bind (costIs_assignEqFieldM _) fun cancel => ?_
  refine CostIs.bind (costIs_sub_mux _) fun s1 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun s2 => ?_
  refine CostIs.bind (costIs_sub_mux _) fun out => ?_
  exact CostIs.pure _

theorem isR1CS_completeAdd (input : Var CompleteAdd.Inputs (F circomPrime))
    (hP : AffineFP input.P) (hQ : AffineFP input.Q) :
    IsR1CSCirc (CompleteAdd.main input) := by
  obtain ⟨P, Q⟩ := input
  obtain ⟨hPx, hPy, hPi⟩ := hP
  obtain ⟨hQx, hQy, hQi⟩ := hQ
  unfold CompleteAdd.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_subMod _ hQx hPx) fun ndx => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_subMod _ hQy hPy) fun ndy => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroFe _ (affineW_sub_subMod _ ndx)) fun nsx => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_addMod _ hPy hQy) fun nsy => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_isZeroFe _ (affineW_sub_addMod _ nsy)) fun noy => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulMod secpParams _ hPx hPx affineW_pConst)
    fun nx1 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_addMod _ (affineW_sub_mulMod secpParams _ nx1)
    (affineW_sub_mulMod secpParams _ nx1)) fun nx2 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_addMod _ (affineW_sub_addMod _ nx2)
    (affineW_sub_mulMod secpParams _ nx1)) fun ntn => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_addMod _ hPy hPy) fun ntd => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ (affine_sub_isZeroFe _ nsx)
    (affineW_sub_addMod _ ntn).affineProvable
    (affineW_sub_subMod _ ndy).affineProvable) fun nnum => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ (affine_sub_isZeroFe _ nsx)
    (affineW_sub_addMod _ ntd).affineProvable
    (affineW_sub_subMod _ ndx).affineProvable) fun nden => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_divOrZero _
    (affineProvable_sub_mux _ nnum).affineW
    (affineProvable_sub_mux _ nden).affineW) fun nlam => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulMod secpParams _
    (affineW_sub_divOrZero _ nlam) (affineW_sub_divOrZero _ nlam) affineW_pConst)
    fun nls => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_subMod _
    (affineW_sub_mulMod secpParams _ nls) hPx) fun nxs => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_subMod _
    (affineW_sub_subMod _ nxs) hQx) fun nx3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_subMod _
    hPx (affineW_sub_subMod _ nx3)) fun nxd => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulMod secpParams _
    (affineW_sub_divOrZero _ nlam) (affineW_sub_subMod _ nxd) affineW_pConst)
    fun nyp => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_subMod _
    (affineW_sub_mulMod secpParams _ nyp) hPy) fun ny3 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_assignEqFieldM _ fun w =>
    isR1CSRow_sub_mul (Affine.var w) (affine_sub_isZeroFe _ nsx)
      (affine_sub_isZeroFe _ noy)) fun ncl => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun ns1 => ?_
  · exact Affine.var _
  · exact affineProvable_infConst
  · exact AffineFP.affineProvable ⟨affineW_sub_subMod _ nx3, affineW_sub_subMod _ ny3,
      Affine.const 0⟩
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hQi
    (AffineFP.affineProvable ⟨hPx, hPy, hPi⟩)
    (affineProvable_sub_mux _ ns1)) fun ns2 => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ hPi
    (AffineFP.affineProvable ⟨hQx, hQy, hQi⟩)
    (affineProvable_sub_mux _ ns2)) fun nout => ?_
  exact IsR1CSCirc.pure _

theorem costIs_sub_completeAdd (b : Var CompleteAdd.Inputs (F circomPrime)) :
    CostIs (subcircuit CompleteAdd.circuit b) completeAddCost :=
  CostIs.subcircuit (fun n => costIs_completeAdd b n)

theorem isR1CS_sub_completeAdd (b : Var CompleteAdd.Inputs (F circomPrime))
    (hP : AffineFP b.P) (hQ : AffineFP b.Q) :
    IsR1CSCirc (subcircuit CompleteAdd.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_completeAdd b hP hQ n)

set_option maxRecDepth 4000 in
/-- The output of a `CompleteAdd` subcircuit is the final `Mux` witness block:
fresh variable rows, componentwise affine. -/
theorem affineFP_sub_completeAdd (b : Var CompleteAdd.Inputs (F circomPrime)) (n : ℕ) :
    AffineFP ((subcircuit CompleteAdd.circuit b).output n) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [circuit_norm, subcircuit, CompleteAdd.circuit, CompleteAdd.elaborated]
  · exact affineW_mapRange_var _
  · exact affineW_mapRange_var _
  · exact Affine.var _

/-! ## `Step` (one double-and-add iteration) -/

def stepCost : Count := ⟨31959, 32341⟩

theorem costIs_step (input : Var Step.Inputs (F circomPrime)) :
    CostIs (Step.main input) stepCost := by
  obtain ⟨acc, px, py, bit⟩ := input
  rw [show stepCost = ⟨15975, 16166⟩ + (⟨15975, 16166⟩ + ⟨9, 9⟩) from by decide]
  unfold Step.main
  refine CostIs.bind (costIs_sub_completeAdd _) fun doubled => ?_
  refine CostIs.bind (costIs_sub_completeAdd _) fun added => ?_
  exact costIs_sub_mux _

theorem isR1CS_step (input : Var Step.Inputs (F circomPrime))
    (hacc : AffineFP input.acc) (hpx : AffineW input.px) (hpy : AffineW input.py)
    (hbit : Affine input.bit) :
    IsR1CSCirc (Step.main input) := by
  obtain ⟨acc, px, py, bit⟩ := input
  unfold Step.main
  refine IsR1CSCirc.bind_out (isR1CS_sub_completeAdd _ hacc hacc) fun nd => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_completeAdd _
    (affineFP_sub_completeAdd _ nd) ⟨hpx, hpy, Affine.const 0⟩) fun na => ?_
  exact isR1CS_sub_mux _ hbit
    (AffineFP.affineProvable (affineFP_sub_completeAdd _ na))
    (AffineFP.affineProvable (affineFP_sub_completeAdd _ nd))

theorem costIs_sub_step (b : Var Step.Inputs (F circomPrime)) :
    CostIs (subcircuit Step.circuit b) stepCost :=
  CostIs.subcircuit (fun n => costIs_step b n)

theorem isR1CS_sub_step (b : Var Step.Inputs (F circomPrime))
    (hacc : AffineFP b.acc) (hpx : AffineW b.px) (hpy : AffineW b.py)
    (hbit : Affine b.bit) :
    IsR1CSCirc (subcircuit Step.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_step b hacc hpx hpy hbit n)

set_option maxRecDepth 4000 in
/-- The output of a `Step` subcircuit is the final `Mux` witness block:
fresh variable rows, componentwise affine. -/
theorem affineFP_sub_step (b : Var Step.Inputs (F circomPrime)) (n : ℕ) :
    AffineFP ((subcircuit Step.circuit b).output n) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [circuit_norm, subcircuit, Step.circuit, Step.elaborated]
  · exact affineW_mapRange_var _
  · exact affineW_mapRange_var _
  · exact Affine.var _

/-! ## `ScalarMul` (the 256-step double-and-add fold) -/

def scalarMulCost : Count := ⟨8182144, 8279944⟩

theorem costIs_scalarMul (input : Var ScalarMul.Inputs (F circomPrime)) :
    CostIs (ScalarMul.main input) scalarMulCost := by
  rw [show scalarMulCost
        = ⟨256 * 31959, 256 * 32341⟩ + (⟨288, 292⟩ + (⟨288, 292⟩ +
            (⟨32, 32⟩ + (⟨32, 32⟩ + Count.zero)))) from by decide]
  unfold ScalarMul.main
  refine CostIs.bind (CostIs.foldlRange fun s i n => costIs_sub_step _ n) fun acc => ?_
  refine CostIs.bind (costIs_sub_toBytes _) fun xb => ?_
  refine CostIs.bind (costIs_sub_toBytes _) fun yb => ?_
  refine CostIs.bind (costIs_sub_mux _) fun xm => ?_
  refine CostIs.bind (costIs_sub_mux _) fun ym => ?_
  exact CostIs.pure _

/-- The output of the double-and-add `foldlRange` is componentwise affine:
the invariant `AffineFP` holds at the start (`infConst` is constant) and is
preserved by every `Step` (whose output is a fresh witness block). -/
theorem affineFP_foldlRange_output {m : ℕ} {init : Var FlaggedPoint (F circomPrime)}
    {body : Var FlaggedPoint (F circomPrime) → Fin m →
      Circuit (F circomPrime) (Var FlaggedPoint (F circomPrime))}
    {constant : Circuit.ConstantLength
      fun (t : Var FlaggedPoint (F circomPrime) × Fin m) => body t.1 t.2}
    (hinit : AffineFP init)
    (hstep : ∀ s (i : Fin m) (n : ℕ), AffineFP s → AffineFP ((body s i).output n))
    (n : ℕ) :
    AffineFP ((Circuit.foldlRange m init body constant).output n) := by
  rw [Circuit.foldlRange.output_eq]
  exact finFoldl_invariant AffineFP _ _ hinit fun acc i h => hstep _ _ _ h

/-- `IsR1CSCirc.bind_out` with an abstracted output: the continuation only
sees an opaque value satisfying the invariant `P`, never the (possibly huge)
output term itself — this keeps the 256-step fold output from ever being
whnf-ed during unification. -/
theorem IsR1CSCirc.bind_out_inv {α β : Type} {f : Circuit (F circomPrime) α}
    {g : α → Circuit (F circomPrime) β} (P : α → Prop)
    (hf : IsR1CSCirc f)
    (hout : ∀ n, P (f.output n))
    (hg : ∀ a, P a → IsR1CSCirc (g a)) :
    IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, Lemmas.operationsIsR1CS_append]
  exact ⟨hf n, hg _ (hout _) _⟩

theorem isR1CS_scalarMul (input : Var ScalarMul.Inputs (F circomPrime))
    (hbits : ∀ i (hi : i < Specs.Secp256k1.scalarBits), Affine input.bits[i])
    (hpx : AffineW input.px) (hpy : AffineW input.py) :
    IsR1CSCirc (ScalarMul.main input) := by
  unfold ScalarMul.main
  refine IsR1CSCirc.bind_out_inv AffineFP ?_ ?_ fun acc hacc => ?_
  · exact IsR1CSCirc.foldlRange_inv AffineFP affineFP_infConst
      (fun s i hs => isR1CS_sub_step _ hs hpx hpy (hbits i.val i.isLt))
      (fun s i k hs => affineFP_sub_step _ k)
  · exact fun n => affineFP_foldlRange_output affineFP_infConst
      (fun s i k hs => affineFP_sub_step _ k) n
  refine IsR1CSCirc.bind_out (isR1CS_sub_toBytes _ hacc.1) fun nxb => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_toBytes _ hacc.2.1) fun nyb => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nxm => ?_
  · exact hacc.2.2
  · refine AffineW.affineProvable ?_
    show AffineW (Vector.ofFn fun _ : Fin coordBytes =>
      ((0 : F circomPrime) : Expression (F circomPrime)))
    intro j hj
    rw [Vector.getElem_ofFn]
    exact Affine.const _
  · exact (affineW_sub_toBytes _ nxb).affineProvable
  refine IsR1CSCirc.bind_out (isR1CS_sub_mux _ ?_ ?_ ?_) fun nym => ?_
  · exact hacc.2.2
  · refine AffineW.affineProvable ?_
    show AffineW (Vector.ofFn fun _ : Fin coordBytes =>
      ((0 : F circomPrime) : Expression (F circomPrime)))
    intro j hj
    rw [Vector.getElem_ofFn]
    exact Affine.const _
  · exact (affineW_sub_toBytes _ nyb).affineProvable
  exact IsR1CSCirc.pure _

theorem costIs_sub_scalarMul (b : Var ScalarMul.Inputs (F circomPrime)) :
    CostIs (subcircuit ScalarMul.circuit b) scalarMulCost :=
  CostIs.subcircuit (fun n => costIs_scalarMul b n)

theorem isR1CS_sub_scalarMul (b : Var ScalarMul.Inputs (F circomPrime))
    (hbits : ∀ i (hi : i < Specs.Secp256k1.scalarBits), Affine b.bits[i])
    (hpx : AffineW b.px) (hpy : AffineW b.py) :
    IsR1CSCirc (subcircuit ScalarMul.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_scalarMul b hbits hpx hpy n)

/-- An `ofFn` of bare variables is affine. -/
theorem affineW_ofFn_var {m : ℕ} (f : Fin m → ℕ) :
    AffineW (Vector.ofFn (fun i => Expression.var ⟨f i⟩) : Var (fields m) (F circomPrime)) := by
  intro j hj
  rw [Vector.getElem_ofFn]
  exact Affine.var _

set_option maxRecDepth 8000 in
/-- The outputs of a `ScalarMul` subcircuit are componentwise affine: the
coordinate bytes are (reindexed) fresh `Mux` witness cells and the flag is the
fold accumulator's fresh witness cell. -/
theorem affineOut_sub_scalarMul (b : Var ScalarMul.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit ScalarMul.circuit b).output n).x ∧
    AffineW ((subcircuit ScalarMul.circuit b).output n).y ∧
    Affine ((subcircuit ScalarMul.circuit b).output n).isInf := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [circuit_norm, subcircuit, ScalarMul.circuit, ScalarMul.elaborated]
  · exact affineW_ofFn_var _
  · exact affineW_ofFn_var _
  · -- the flag is the fold accumulator's `isInf`: thread affineness through
    -- the (output-level) `Fin.foldl`
    refine finFoldl_invariant
      (fun (s : Var FlaggedPoint (F circomPrime)) => Affine s.isInf) _ _ ?_ ?_
    · exact affineFP_infConst.2.2
    · intro acc i h
      exact Affine.var _

/-! ## Symbolic top-level input/output atoms -/

open Challenge.Instances.Secp256k1ScalarMulFixedBase in
/-- Componentwise affineness of an `AffineProvable` symbolic top-level input.
The fixed-base input is bit-sequence-only (`toElements` is `bits ++ #v[]`). -/
theorem affineInput_components (input : Var Interface.Input (F circomPrime))
    (hinput : AffineProvable input) :
    AffineW input.bits := by
  have hflat : AffineW
      (input.bits ++ (#v[] : Vector (Expression (F circomPrime)) 0) :
        fields (Interface.scalarBits + 0) (Expression (F circomPrime))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hinput i (by exact hi)
  exact AffineW.left_of_append hflat

open Challenge.Instances.Secp256k1ScalarMulFixedBase in
/-- Assemble `AffineProvable` on a symbolic top-level output from its
components (`toElements` is the flat append `x ++ (y ++ #v[isInf])`). -/
theorem affineProvable_interfaceOutput {v : Var Interface.Output (F circomPrime)}
    (hx : AffineW v.x) (hy : AffineW v.y) (hi : Affine v.isInf) :
    AffineProvable v := by
  intro j hj
  simp only [circuit_norm, explicit_provable_type]
  exact AffineW.append hx (AffineW.append hy (affineW_singleton hi)) j hj

end Cost
end Solution.Secp256k1ScalarMulFixedBase
