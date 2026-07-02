import Clean.Utils.Bits
import Clean.Circuit.Loops
import Challenge.Utils.CostR1CS
import Solution.AssertBytes.Num2Bits
import Challenge.Instances.AssertBytes.Interface

/-!
# Compositional cost (`CostIs`) and R1CS (`IsR1CSCirc`) facts for `AssertBytes`

Bottom-up `operationCount` / `operationsIsR1CS` certificates for the single
building block of `AssertBytes.main`: the per-element `Num2Bits 8` byte range
check, proved with the compositional lemmas in `Challenge.CostR1CS` (no
`native_decide`, no large `decide`).

`Num2Bits.main` inlines its constraints directly (`witnessVector`, a booleanity
`forEach`, and a recomposition `assertZero`), so its cost / R1CS certificate is a
straight structural recursion over that `do`-block — no subcircuit nesting. The
only extra ingredient is an index-aware `forEach` R1CS combinator: the generic
`IsR1CSCirc.forEach` quantifies over *all* element values, too weak for the
booleanity rows that need each bit (a `witnessVector` cell) to be affine.
-/

namespace Solution.AssertBytes
namespace Cost

open Challenge.Instances.AssertBytes.Interface
open Challenge.CostR1CS
open Utils.Bits

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

/-- `Num2Bits.main n x` witnesses `n` bits (`⟨n, 0⟩`), boolean-constrains each
(`⟨0, n⟩`), and asserts the recomposition (`⟨0, 1⟩`): total `⟨n, n+1⟩`. -/
theorem costIs_num2Bits (n : ℕ) (x : Expression (F circomPrime)) :
    CostIs (Num2Bits.main n x) ⟨n, n + 1⟩ := by
  unfold Num2Bits.main
  have hcount : (⟨n, 0⟩ + (⟨n * 0, n * 1⟩ + ⟨0, 1⟩) : Count) = ⟨n, n + 1⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1; simp
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) n _) fun bits => ?_
  refine CostIs.bind (CostIs.forEach fun b m => CostIs.assertZero (b * (b - 1)) m) fun _ => ?_
  exact CostIs.assertZero _

/-- `fieldFromBitsExpr` over an affine bit-vector is affine. -/
theorem affine_fieldFromBitsExpr {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (h : AffineW bits) : Affine (fieldFromBitsExpr bits) := by
  unfold fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- `Num2Bits.main n x` is single-row R1CS when `x` is affine: each booleanity row
`bit·(bit−1)` and the recomposition row `x − fieldFromBitsExpr bits` are R1CS. -/
theorem isR1CS_num2Bits (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Num2Bits.main n x) := by
  unfold Num2Bits.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector n _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- booleanity loop: each `bit · (bit - 1)` is a single rank-1 row
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    show isR1CSRow (_ * (_ - 1))
    exact isR1CSRow_mul (affineW_witnessVector_output n _ w i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output n _ w i.val i.isLt) (Affine.const 1))
  · -- recomposition row: `x - fieldFromBitsExpr bits` is affine
    refine IsR1CSCirc.assertZero ?_
    exact isR1CSRow_of_affine (Affine.sub hx
      (affine_fieldFromBitsExpr ((Circuit.witnessVector n _).output w)
        (affineW_witnessVector_output n _ w)))

/-- The `Num2Bits n` assertion invoked on `x` costs `⟨n, n+1⟩`. -/
theorem costIs_assertion_num2Bits (n : ℕ) (x : Expression (F circomPrime)) :
    CostIs (assertion (Num2Bits.circuit n) x) ⟨n, n + 1⟩ :=
  CostIs.assertion (fun m => costIs_num2Bits n x m)

theorem isR1CS_assertion_num2Bits (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (Num2Bits.circuit n) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_num2Bits n x hx m)

end Cost
end Solution.AssertBytes
