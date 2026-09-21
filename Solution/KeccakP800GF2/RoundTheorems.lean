import Challenge.Instances.KeccakP800GF2.Interface

namespace Solution.KeccakP800GF2

open Challenge.Instances.KeccakP800GF2.Interface
open Challenge.F2Bits

namespace Round

abbrev StateVar := Var (fields permutationBits) (F p2)

def preChi {α : Type} [Add α] (s : Specs.KeccakP800.State α) :
    Specs.KeccakP800.State α :=
  Specs.KeccakP800.rhoPi (Specs.KeccakP800.theta s)

def chiProduct {α : Type} [Add α] [Mul α] [One α]
    (pre : Specs.KeccakP800.State α) (i : Fin Specs.KeccakP800.stateBits) : α :=
  let x := Specs.KeccakP800.xOf i
  let y := Specs.KeccakP800.yOf i
  let z := Specs.KeccakP800.zOf i
  (1 + Specs.KeccakP800.bit pre (x + 1) y z) *
    Specs.KeccakP800.bit pre (x + 2) y z

def chiProducts {α : Type} [Add α] [Mul α] [One α]
    (pre : Specs.KeccakP800.State α) : Specs.KeccakP800.State α :=
  Vector.ofFn fun i : Fin Specs.KeccakP800.stateBits => chiProduct pre i

def chiFromProducts {α : Type} [Add α]
    (pre products : Specs.KeccakP800.State α) : Specs.KeccakP800.State α :=
  Vector.ofFn fun i : Fin Specs.KeccakP800.stateBits =>
    let x := Specs.KeccakP800.xOf i
    let y := Specs.KeccakP800.yOf i
    let z := Specs.KeccakP800.zOf i
    Specs.KeccakP800.bit pre x y z + products[i]

def roundOut {α : Type} [Add α] [Zero α] [One α]
    (r : Specs.KeccakP800.RoundIndex)
    (pre products : Specs.KeccakP800.State α) : Specs.KeccakP800.State α :=
  Specs.KeccakP800.iota r (chiFromProducts pre products)

theorem chiFromProducts_products {α : Type} [Add α] [Mul α] [One α]
    (pre : Specs.KeccakP800.State α) :
    chiFromProducts pre (chiProducts pre) = Specs.KeccakP800.chi pre := by
  refine Vector.ext fun i hi => ?_
  simp [chiFromProducts, chiProducts, chiProduct, Specs.KeccakP800.chi]

theorem roundOut_products {α : Type} [Add α] [Mul α] [Zero α] [One α]
    (r : Specs.KeccakP800.RoundIndex) (s : Specs.KeccakP800.State α) :
    roundOut r (preChi s) (chiProducts (preChi s)) = Specs.KeccakP800.round r s := by
  unfold roundOut Specs.KeccakP800.round preChi
  rw [chiFromProducts_products]

theorem eval_bit (env : Environment (F p2)) (s : StateVar) (x y z : ℕ) :
    Expression.eval env (Specs.KeccakP800.bit s x y z)
      = Specs.KeccakP800.bit (Vector.map (Expression.eval env) s) x y z := by
  unfold Specs.KeccakP800.bit
  symm
  exact Vector.getElem_map (Expression.eval env)
    (xs := s) (hi := (Specs.KeccakP800.bitIndex x y z).isLt)

theorem eval_roundConstantBit (env : Environment (F p2))
    (r : Specs.KeccakP800.RoundIndex) (z : ℕ) :
    Expression.eval env (Specs.KeccakP800.roundConstantBit r z)
      = Specs.KeccakP800.roundConstantBit r z := by
  unfold Specs.KeccakP800.roundConstantBit
  split <;> rfl

theorem eval_columnParity (env : Environment (F p2)) (s : StateVar) (x z : ℕ) :
    Expression.eval env (Specs.KeccakP800.columnParity s x z)
      = Specs.KeccakP800.columnParity (Vector.map (Expression.eval env) s) x z := by
  unfold Specs.KeccakP800.columnParity
  simp only [circuit_norm]

theorem eval_theta (env : Environment (F p2)) (s : StateVar) :
    Vector.map (Expression.eval env) (Specs.KeccakP800.theta s)
      = Specs.KeccakP800.theta (Vector.map (Expression.eval env) s) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_map]
  change Expression.eval env ((Specs.KeccakP800.theta s)[i]'hi)
      = (Specs.KeccakP800.theta (Vector.map (Expression.eval env) s))[i]'hi
  unfold Specs.KeccakP800.theta
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  simp only [circuit_norm, eval_columnParity]

theorem eval_rhoPi (env : Environment (F p2)) (s : StateVar) :
    Vector.map (Expression.eval env) (Specs.KeccakP800.rhoPi s)
      = Specs.KeccakP800.rhoPi (Vector.map (Expression.eval env) s) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_map]
  change Expression.eval env ((Specs.KeccakP800.rhoPi s)[i]'hi)
      = (Specs.KeccakP800.rhoPi (Vector.map (Expression.eval env) s))[i]'hi
  unfold Specs.KeccakP800.rhoPi
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact eval_bit env s _ _ _

theorem eval_preChi (env : Environment (F p2)) (s : StateVar) :
    Vector.map (Expression.eval env) (preChi s)
      = preChi (Vector.map (Expression.eval env) s) := by
  unfold preChi
  rw [eval_rhoPi, eval_theta]

theorem eval_chiProduct (env : Environment (F p2)) (pre : StateVar)
    (i : Fin Specs.KeccakP800.stateBits) :
    Expression.eval env (chiProduct pre i)
      = chiProduct (Vector.map (Expression.eval env) pre) i := by
  unfold chiProduct
  simp only [circuit_norm]

theorem eval_chiFromProducts (env : Environment (F p2)) (pre products : StateVar) :
    Vector.map (Expression.eval env) (chiFromProducts pre products)
      = chiFromProducts (Vector.map (Expression.eval env) pre)
          (Vector.map (Expression.eval env) products) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_map]
  change Expression.eval env ((chiFromProducts pre products)[i]'hi)
      = (chiFromProducts (Vector.map (Expression.eval env) pre)
          (Vector.map (Expression.eval env) products))[i]'hi
  unfold chiFromProducts
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  simp only [circuit_norm]

theorem eval_iota (env : Environment (F p2)) (r : Specs.KeccakP800.RoundIndex)
    (s : StateVar) :
    Vector.map (Expression.eval env) (Specs.KeccakP800.iota r s)
      = Specs.KeccakP800.iota r (Vector.map (Expression.eval env) s) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_map]
  change Expression.eval env ((Specs.KeccakP800.iota r s)[i]'hi)
      = (Specs.KeccakP800.iota r (Vector.map (Expression.eval env) s))[i]'hi
  unfold Specs.KeccakP800.iota
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  dsimp only
  split
  · simp only [circuit_norm]
    rw [eval_roundConstantBit]
  · exact eval_bit env s _ _ _

theorem eval_roundOut (env : Environment (F p2)) (r : Specs.KeccakP800.RoundIndex)
    (pre products : StateVar) :
    Vector.map (Expression.eval env) (roundOut r pre products)
      = roundOut r (Vector.map (Expression.eval env) pre)
          (Vector.map (Expression.eval env) products) := by
  unfold roundOut
  rw [eval_iota, eval_chiFromProducts]

end Round

end Solution.KeccakP800GF2
