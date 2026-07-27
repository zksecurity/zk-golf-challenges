import Challenge.Instances.KangarooTwelveGF2.Interface

namespace Solution.KangarooTwelveGF2

open Challenge.Instances.KangarooTwelveGF2.Interface
open Challenge.F2Bits

namespace Round

abbrev StateVar := Var (fields permutationBits) (F p2)

def preChi {α : Type} [Add α] (s : Specs.KangarooTwelve.State α) :
    Specs.KangarooTwelve.State α :=
  Specs.KangarooTwelve.rhoPi (Specs.KangarooTwelve.theta s)

def chiProduct {α : Type} [Add α] [Mul α] [One α]
    (pre : Specs.KangarooTwelve.State α) (i : Fin Specs.KangarooTwelve.stateBits) : α :=
  let x := Specs.KangarooTwelve.xOf i
  let y := Specs.KangarooTwelve.yOf i
  let z := Specs.KangarooTwelve.zOf i
  (1 + Specs.KangarooTwelve.bit pre (x + 1) y z) *
    Specs.KangarooTwelve.bit pre (x + 2) y z

def chiProducts {α : Type} [Add α] [Mul α] [One α]
    (pre : Specs.KangarooTwelve.State α) : Specs.KangarooTwelve.State α :=
  Vector.ofFn fun i : Fin Specs.KangarooTwelve.stateBits => chiProduct pre i

def chiFromProducts {α : Type} [Add α]
    (pre products : Specs.KangarooTwelve.State α) : Specs.KangarooTwelve.State α :=
  Vector.ofFn fun i : Fin Specs.KangarooTwelve.stateBits =>
    let x := Specs.KangarooTwelve.xOf i
    let y := Specs.KangarooTwelve.yOf i
    let z := Specs.KangarooTwelve.zOf i
    Specs.KangarooTwelve.bit pre x y z + products[i]

def roundOut {α : Type} [Add α] [Zero α] [One α]
    (r : Fin Specs.KangarooTwelve.rounds)
    (pre products : Specs.KangarooTwelve.State α) : Specs.KangarooTwelve.State α :=
  Specs.KangarooTwelve.iota r (chiFromProducts pre products)

theorem chiFromProducts_products {α : Type} [Add α] [Mul α] [One α]
    (pre : Specs.KangarooTwelve.State α) :
    chiFromProducts pre (chiProducts pre) = Specs.KangarooTwelve.chi pre := by
  refine Vector.ext fun i hi => ?_
  simp [chiFromProducts, chiProducts, chiProduct, Specs.KangarooTwelve.chi]

theorem roundOut_products {α : Type} [Add α] [Mul α] [Zero α] [One α]
    (r : Fin Specs.KangarooTwelve.rounds) (s : Specs.KangarooTwelve.State α) :
    roundOut r (preChi s) (chiProducts (preChi s)) = Specs.KangarooTwelve.round r s := by
  unfold roundOut Specs.KangarooTwelve.round preChi
  rw [chiFromProducts_products]

theorem eval_bit (env : Environment (F p2)) (s : StateVar) (x y z : ℕ) :
    Expression.eval env (Specs.KangarooTwelve.bit s x y z)
      = Specs.KangarooTwelve.bit (Vector.map (Expression.eval env) s) x y z := by
  unfold Specs.KangarooTwelve.bit
  symm
  exact Vector.getElem_map (Expression.eval env)
    (xs := s) (hi := (Specs.KangarooTwelve.bitIndex x y z).isLt)

theorem eval_roundConstantBit (env : Environment (F p2))
    (r : Fin Specs.KangarooTwelve.rounds) (z : ℕ) :
    Expression.eval env (Specs.KangarooTwelve.roundConstantBit r z)
      = Specs.KangarooTwelve.roundConstantBit r z := by
  unfold Specs.KangarooTwelve.roundConstantBit
  split <;> rfl

theorem eval_columnParity (env : Environment (F p2)) (s : StateVar) (x z : ℕ) :
    Expression.eval env (Specs.KangarooTwelve.columnParity s x z)
      = Specs.KangarooTwelve.columnParity (Vector.map (Expression.eval env) s) x z := by
  unfold Specs.KangarooTwelve.columnParity
  simp only [circuit_norm]

theorem eval_theta (env : Environment (F p2)) (s : StateVar) :
    Vector.map (Expression.eval env) (Specs.KangarooTwelve.theta s)
      = Specs.KangarooTwelve.theta (Vector.map (Expression.eval env) s) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_map]
  change Expression.eval env ((Specs.KangarooTwelve.theta s)[i]'hi)
      = (Specs.KangarooTwelve.theta (Vector.map (Expression.eval env) s))[i]'hi
  unfold Specs.KangarooTwelve.theta
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  simp only [circuit_norm, eval_columnParity]

theorem eval_rhoPi (env : Environment (F p2)) (s : StateVar) :
    Vector.map (Expression.eval env) (Specs.KangarooTwelve.rhoPi s)
      = Specs.KangarooTwelve.rhoPi (Vector.map (Expression.eval env) s) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_map]
  change Expression.eval env ((Specs.KangarooTwelve.rhoPi s)[i]'hi)
      = (Specs.KangarooTwelve.rhoPi (Vector.map (Expression.eval env) s))[i]'hi
  unfold Specs.KangarooTwelve.rhoPi
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact eval_bit env s _ _ _

theorem eval_preChi (env : Environment (F p2)) (s : StateVar) :
    Vector.map (Expression.eval env) (preChi s)
      = preChi (Vector.map (Expression.eval env) s) := by
  unfold preChi
  rw [eval_rhoPi, eval_theta]

theorem eval_chiProduct (env : Environment (F p2)) (pre : StateVar)
    (i : Fin Specs.KangarooTwelve.stateBits) :
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

theorem eval_iota (env : Environment (F p2)) (r : Fin Specs.KangarooTwelve.rounds)
    (s : StateVar) :
    Vector.map (Expression.eval env) (Specs.KangarooTwelve.iota r s)
      = Specs.KangarooTwelve.iota r (Vector.map (Expression.eval env) s) := by
  refine Vector.ext fun i hi => ?_
  rw [Vector.getElem_map]
  change Expression.eval env ((Specs.KangarooTwelve.iota r s)[i]'hi)
      = (Specs.KangarooTwelve.iota r (Vector.map (Expression.eval env) s))[i]'hi
  unfold Specs.KangarooTwelve.iota
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  dsimp only
  split
  · simp only [circuit_norm]
    rw [eval_roundConstantBit]
  · exact eval_bit env s _ _ _

theorem eval_roundOut (env : Environment (F p2)) (r : Fin Specs.KangarooTwelve.rounds)
    (pre products : StateVar) :
    Vector.map (Expression.eval env) (roundOut r pre products)
      = roundOut r (Vector.map (Expression.eval env) pre)
          (Vector.map (Expression.eval env) products) := by
  unfold roundOut
  rw [eval_iota, eval_chiFromProducts]

end Round

end Solution.KangarooTwelveGF2
