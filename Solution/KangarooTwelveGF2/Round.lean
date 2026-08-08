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

/-- Index into the witness block without materialising it (cf. `Cost.wv_getElem`). -/
theorem wv_getElem {m : ℕ} (c : ProverEnvironment (F p2) → Vector (F p2) m)
    (w i : ℕ) (h : i < m) :
    ((Circuit.witnessVector m c).output w)[i]'h = Expression.var ⟨w + i⟩ := by
  rw [show (Circuit.witnessVector m c).output w = varFromOffset (fields m) w from rfl]
  simp only [varFromOffset, instProvableTypeFields, size, Vector.getElem_mapRange]

/-- A condition on the round's operations reduces to the witness obligation plus one per row. -/
theorem forAllNoOffset_main (cond : ConditionNoOffset (F p2))
    (r : Fin Specs.KangarooTwelve.rounds) (s : StateVar) (n : ℕ) :
    Operations.forAllNoOffset cond ((main r s).operations n) ↔
      cond.witness permutationBits
          (fun env => Vector.ofFn fun i : Fin permutationBits => (chiProduct (preChi s) i).eval env)
        ∧ ∀ i : Fin permutationBits,
            cond.assert ((Expression.var ⟨n + i.val⟩ : Expression (F p2))
              - chiProduct (preChi s) i) := by
  unfold main
  rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append,
      Circuit.bind_operations_eq, Operations.forAllNoOffset_append,
      Circuit.forEach.forAllNoOffset]
  simp only [Circuit.operations, Circuit.witnessVector, Circuit.assertZero,
    Operations.forAllNoOffset, Vector.getElem_finRange, wv_getElem, and_true]

def Assumptions (_ : fields permutationBits (F p2)) : Prop := True

def Spec (r : Fin Specs.KangarooTwelve.rounds)
    (input output : fields permutationBits (F p2)) : Prop :=
  output = Specs.KangarooTwelve.round r input

theorem soundness (r : Fin Specs.KangarooTwelve.rounds) :
    Soundness (F p2) (main r) Assumptions (Spec r) := by
  circuit_proof_start_core
  simp only [ConstraintsHold.Soundness, forAllNoOffset_main] at h_holds
  obtain ⟨-, h_rows⟩ := h_holds
  simp only [circuit_norm] at h_input
  refine ⟨?_, ?_⟩
  · simp only [Spec, circuit_norm]
    have hinput : Vector.map (Expression.eval env) input_var = input := h_input
    have hproducts : Vector.map (Expression.eval env)
          (Vector.mapRange permutationBits fun i => (Expression.var ⟨i₀ + i⟩ : Expression (F p2)))
        = chiProducts (preChi input) := by
      refine Vector.ext fun i hi => ?_
      rw [Vector.getElem_map, Vector.getElem_mapRange]
      unfold chiProducts
      rw [Vector.getElem_ofFn]
      have hrow := h_rows ⟨i, hi⟩
      simp only [circuit_norm] at hrow
      rw [← hinput, ← eval_preChi env input_var,
        ← eval_chiProduct env (preChi input_var) ⟨i, hi⟩]
      change env.get (i₀ + i) = Expression.eval env (chiProduct (preChi input_var) ⟨i, hi⟩)
      linear_combination hrow
    calc
      Vector.map (Expression.eval env)
            (roundOut r (preChi input_var)
              (Vector.mapRange permutationBits fun i => (Expression.var ⟨i₀ + i⟩ : Expression (F p2))))
          = roundOut r (Vector.map (Expression.eval env) (preChi input_var))
              (Vector.map (Expression.eval env)
                (Vector.mapRange permutationBits
                  fun i => (Expression.var ⟨i₀ + i⟩ : Expression (F p2)))) := eval_roundOut env r _ _
      _ = roundOut r (preChi input) (chiProducts (preChi input)) := by
            rw [eval_preChi, hinput, hproducts]
      _ = Specs.KangarooTwelve.round r input := roundOut_products r input
  · simp only [Operations.Requirements, forAllNoOffset_main]
    exact ⟨trivial, fun _ => trivial⟩

theorem completeness (r : Fin Specs.KangarooTwelve.rounds) :
    Completeness (F p2) (main r) Assumptions := by
  circuit_proof_start_core
  unfold main at h_env
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
  obtain ⟨h_wit, -⟩ := h_env
  simp only [circuit_norm] at h_wit
  simp only [ConstraintsHold.Completeness, forAllNoOffset_main]
  refine ⟨trivial, fun i => ?_⟩
  have henv := h_wit i
  simp only [circuit_norm, Vector.getElem_ofFn] at henv ⊢
  rw [henv]
  ring

def circuit (r : Fin Specs.KangarooTwelve.rounds) :
    FormalCircuit (F p2) (fields permutationBits) (fields permutationBits) where
  main := main r
  elaborated := elaborated r
  exposedChannels_eq := by
    intro _ _ _ h
    exact (List.not_mem_nil h).elim
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
  rw [Circuit.bind_structuralComputableWitnesses_iff]
  refine ⟨?_, ?_⟩
  · rw [Circuit.witnessVector_structuralComputableWitnesses_iff]
    intro _ h_input
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
  · rw [Circuit.bind_structuralComputableWitnesses_iff]
    refine ⟨?_, ?_⟩
    · rw [Circuit.forEach_structuralComputableWitnesses_iff]
      intro i
      rw [Circuit.assertZero_structuralComputableWitnesses_iff]
      trivial
    · rw [Circuit.pure_structuralComputableWitnesses_iff]
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
          (Vector.mapRange permutationBits fun i => Expression.var ⟨n + i⟩) := rfl
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
