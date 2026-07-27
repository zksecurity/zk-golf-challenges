import Solution.SHA256CompressGF2.Theorems
import Challenge.Utils.CostR1CSCanonical

/-!
# Shared canonical helpers + `IsCidCirc` fold combinators

The solution-side `IsCidCirc` analogues of the base `IsR1CSCirc` fold lemmas
(the trusted `IsCidCirc` has no fold combinator), plus the shared `zxorOut`
output word used by `Ch32Canon`/`Maj32Canon`.
-/

namespace Challenge.CostR1CS

variable {F : Type} [Field F]

/-- Canonical (`IsCidCirc`) analogue of `IsR1CSCirc.foldlRange_inv`: a `foldlRange`
is ordered canonical-R1CS when every iteration is, for accumulators satisfying an
invariant `P` that each step preserves, provided each iteration is *balanced*:
it contributes exactly `L` constraints where `L` is also its `localLength`, so
iteration `i`'s pins start at `n + i·L`, exactly its running offset. Proved
solution-side (the trusted `IsCidCirc` has no fold combinator). -/
theorem IsCidCirc.foldlRange_inv {β : Type} {m : ℕ} [Inhabited β] {init : β}
    {body : β → Fin m → Circuit F β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2}
    {L : ℕ}
    (P : β → Prop) (hinit : P init)
    (hlen : ∀ i : Fin m, (body default i).localLength = L)
    (hbal : ∀ s (i : Fin m) n, P s →
      (operationCount ((body s i).operations n)).constraints = L)
    (hbody : ∀ s i, P s → IsCidCirc (body s i))
    (hstep : ∀ s (i : Fin m) n, P s → P ((body s i).output n)) :
    IsCidCirc (Circuit.foldlRange m init body constant) := by
  refine IsCidCirc.of_ops fun n => ?_
  rw [Circuit.foldlRange.operations_eq]
  have hacc : ∀ i : Fin m, P (Circuit.FoldlM.foldlAcc n (Vector.finRange m) body init i) := by
    intro i
    rw [Circuit.FoldlM.foldlAcc]
    apply finFoldl_invariant P _ _ hinit
    intro acc j hacc
    exact hstep acc _ _ hacc
  refine operationsIsCid_flatten_ofFn (L := L) (fun i => hbal _ i _ (hacc i)) fun i => ?_
  rw [hlen i]
  exact (hbody _ i (hacc i)).ops _

/-- Canonical (`IsCidCirc`) analogue of `IsR1CSCirc.mapFinRange`, balanced. -/
theorem IsCidCirc.mapFinRange {β : Type} {m : ℕ} [NeZero m] {body : Fin m → Circuit F β}
    {constant : Circuit.ConstantLength body} {L : ℕ}
    (hlen : (body 0).localLength = L)
    (hbal : ∀ (i : Fin m) n, (operationCount ((body i).operations n)).constraints = L)
    (h : ∀ i, IsCidCirc (body i)) :
    IsCidCirc (Circuit.mapFinRange m body constant) := by
  refine IsCidCirc.of_ops fun n => ?_
  rw [Circuit.mapFinRange.operations_eq]
  refine operationsIsCid_flatten_ofFn (L := L) (fun i => hbal i _) fun i => ?_
  rw [hlen]
  exact (h i).ops _

end Challenge.CostR1CS

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

/-- Inlined `Ch`/`Maj` output word: bit `i` is `zᵢ ⊕ pᵢ` (`z` an input word, `p`
the AND witnesses). A named def keeps the circuit output opaque so subcircuit
affineness does not reduce the whole `ofFn`. -/
def zxorOut (v : Var (fields 96) (F p2)) (p : Var (fields 32) (F p2)) :
    Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => a96 v (64 + i.val) + p[i.val]'i.isLt

/-- `zxorOut` mixes an input word with the AND witnesses, so agreement needs both. -/
theorem eval_zxorOut_congr {v : Var (fields 96) (F p2)} {p : Var (fields 32) (F p2)}
    {env env' : ProverEnvironment (F p2)}
    (hv : eval env v = eval env' v) (hp : eval env p = eval env' p) :
    eval env (zxorOut v p) = eval env' (zxorOut v p) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold zxorOut a96
  rw [Vector.getElem_ofFn]
  simp only [circuit_norm]
  rw [eval_getElem_congr hv, eval_getElem_congr hp]

end Solution.SHA256CompressGF2
