import Solution.KangarooTwelveGF2.RoundTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Solution.KangarooTwelveGF2

open Challenge.Instances.KangarooTwelveGF2.Interface
open Challenge.F2Bits

namespace Round

def main (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar) :
    Circuit (F p2) StateVar := do
  let pre := preChi s
  let products ← witnessVector permutationBits (fun env =>
    Vector.ofFn fun i : Fin permutationBits => (chiProduct pre i).eval env)
  Circuit.forEach (Vector.finRange permutationBits) (fun i =>
    assertZero (products[i.val]'i.isLt - chiProduct pre i))
  return roundOut r pre products

instance elaborated (r : Fin Specs.KangarooTwelve.rounds) :
    ElaboratedCircuit (F p2) (fields permutationBits) (fields permutationBits) (main r) := by
  elaborate_circuit

def Assumptions (_ : fields permutationBits (F p2)) : Prop := True

def Spec (r : Fin Specs.KangarooTwelve.rounds)
    (input output : fields permutationBits (F p2)) : Prop :=
  output = Specs.KangarooTwelve.round r input

theorem soundness (r : Fin Specs.KangarooTwelve.rounds) :
    Soundness (F p2) (main r) Assumptions (Spec r) := by
  circuit_proof_start [main, Spec]
  have hinput : Vector.map (Expression.eval env) input_var = input := h_input
  let products : StateVar := Vector.mapRange permutationBits fun i => Expression.var ⟨i₀ + i⟩
  have hproducts : Vector.map (Expression.eval env) products = chiProducts (preChi input) := by
    refine Vector.ext fun i hi => ?_
    rw [Vector.getElem_map]
    change Expression.eval env (products[i]'hi) = (chiProducts (preChi input))[i]'hi
    change Expression.eval env
        ((Vector.mapRange permutationBits fun j => Expression.var ⟨i₀ + j⟩ :
          StateVar)[i]'hi) = (chiProducts (preChi input))[i]'hi
    rw [show ((Vector.mapRange permutationBits fun j => Expression.var ⟨i₀ + j⟩ :
        StateVar)[i]'hi) = Expression.var ⟨i₀ + i⟩ by
      simp only [Vector.getElem_mapRange]]
    unfold chiProducts
    rw [Vector.getElem_ofFn]
    have hrow := h_holds ⟨i, hi⟩
    simp only [circuit_norm] at hrow
    rw [← hinput, ← eval_preChi env input_var,
      ← eval_chiProduct env (preChi input_var) ⟨i, hi⟩]
    change env.get (i₀ + i) = Expression.eval env (chiProduct (preChi input_var) ⟨i, hi⟩)
    linear_combination hrow
  change Vector.map (Expression.eval env) (roundOut r (preChi input_var) products)
      = Specs.KangarooTwelve.round r input
  calc
    Vector.map (Expression.eval env) (roundOut r (preChi input_var) products)
        = roundOut r (Vector.map (Expression.eval env) (preChi input_var))
            (Vector.map (Expression.eval env) products) := eval_roundOut env r _ _
    _ = roundOut r (preChi input) (chiProducts (preChi input)) := by
      rw [eval_preChi, hinput, hproducts]
    _ = Specs.KangarooTwelve.round r input := roundOut_products r input

theorem completeness (r : Fin Specs.KangarooTwelve.rounds) :
    Completeness (F p2) (main r) Assumptions := by
  circuit_proof_start
  intro i
  have henv := h_env i
  simp only [circuit_norm, Vector.getElem_ofFn] at henv ⊢
  rw [henv]
  ring

def circuit (r : Fin Specs.KangarooTwelve.rounds) :
    FormalCircuit (F p2) (fields permutationBits) (fields permutationBits) where
  main := main r
  elaborated := elaborated r
  Assumptions := Assumptions
  Spec := Spec r
  soundness := soundness r
  completeness := completeness r

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

theorem computableWitnesses (r : Fin Specs.KangarooTwelve.rounds) :
    (circuit r).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main r input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessVector_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    have hmap : Vector.map (Expression.eval env.toEnvironment) input
        = Vector.map (Expression.eval env'.toEnvironment) input := by
      simpa [circuit_norm] using h_input
    have hpre : Vector.map (Expression.eval env.toEnvironment) (preChi input)
        = Vector.map (Expression.eval env'.toEnvironment) (preChi input) := by
      rw [eval_preChi, eval_preChi, hmap]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn]
    rw [eval_chiProduct env.toEnvironment (preChi input) ⟨i, hi⟩,
      eval_chiProduct env'.toEnvironment (preChi input) ⟨i, hi⟩, hpre]
  · intro _
    trivial

theorem computableWitness (r : Fin Specs.KangarooTwelve.rounds) : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p2) => eval env input) →
    Circuit.ComputableWitnesses (main r input) n :=
  FormalCircuitBase.computableWitnesses_implies
    (circuit := (circuit r).base) (computableWitnesses r)

theorem subcircuit_localLength (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar)
    (m : ℕ) : (subcircuit (circuit r) s).localLength m = 1600 := rfl

/-- The round subcircuit output evaluates equally under two prover environments
that agree below `n + permutationBits` and evaluate the input state equally
(the output mixes affine functions of the input with the fresh witnesses). -/
theorem eval_subOut_of_agreesBelow (r : Fin Specs.KangarooTwelve.rounds)
    (s : StateVar) (n : ℕ) {k : ℕ} (hk : n + 1600 ≤ k)
    {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow k env')
    (h_input : eval env s = eval env' s) :
    eval env ((subcircuit (circuit r) s).output n)
      = eval env' ((subcircuit (circuit r) s).output n) := by
  rw [CircuitType.eval_var_fields_prover, CircuitType.eval_var_fields_prover] at h_input ⊢
  have hout : (subcircuit (circuit r) s).output n
      = roundOut r (preChi s)
          (Vector.mapRange permutationBits fun i => Expression.var ⟨n + i⟩) := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  rw [hout, eval_roundOut, eval_roundOut]
  have hprods : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange permutationBits fun i => (Expression.var ⟨n + i⟩ : Expression (F p2)))
      = Vector.map (Expression.eval env'.toEnvironment)
        (Vector.mapRange permutationBits fun i => (Expression.var ⟨n + i⟩ : Expression (F p2))) := by
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact h_agree (n + i) (by
      have hi' : i < 1600 := hi
      omega)
  rw [eval_preChi, eval_preChi, h_input, hprods]

end ComputableWitness

end Round

end Solution.KangarooTwelveGF2
