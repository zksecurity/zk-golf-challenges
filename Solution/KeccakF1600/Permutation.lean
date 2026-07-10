import Solution.KeccakF1600.PermutationDefs
import Solution.KeccakF1600.PermutationSound
import Solution.KeccakF1600.PermutationComplete

namespace Solution.KeccakF1600.Permutation

open Challenge.Instances.KeccakF1600.Interface

set_option maxHeartbeats 1000000

/-- The Keccak-f[1600] permutation on the lane state as a `FormalCircuit`. -/
def circuit : FormalCircuit (F circomPrime) KeccakBitState KeccakBitState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  -- `soundness := soundness` / `completeness := completeness` trigger a `whnf`
  -- timeout while checking the term against the structure's `base.main`
  -- projection (the same quirk noted in clean's own Keccak Permutation); routing
  -- through `simp only` matches the goal syntactically and sidesteps it.
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]

/-- `body s i` is definitionally the `KeccakRound` subcircuit; exposing the
`subcircuit` head lets the structural-computable-witnesses rewrites fire. -/
private lemma body_eq_subcircuit (s : Var KeccakBitState (F circomPrime)) (i : Fin 24) :
    body s i = subcircuit (KeccakRound.circuit (rc i) (rc_lt i)) s := rfl

/-- The symbolic state after round `i` (χ-output witnesses wired through ι)
evaluates identically under two environments that agree below `k`, provided the
whole `[offset + i*6400, offset + (i+1)*6400)` block lies below `k`. -/
lemma eval_stateVar_of_agreesBelow {k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)} (n i : ℕ)
    (hbound : n + i * 6400 + 6400 ≤ k)
    (h : env.AgreesBelow k env') :
    eval env (stateVar n i) = eval env' (stateVar n i) := by
  simp only [CircuitType.eval_var_prover_to_verifier]
  rw [eval_keccakState env.toEnvironment (stateVar n i),
    eval_keccakState env'.toEnvironment (stateVar n i)]
  simp only [stateVar, map_iotaWire]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map, Vector.getElem_mapFinRange]
  apply Vector.ext
  intro z hz
  simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  exact h (n + i * 6400 + 3200 + j * 128 + 64 + z) (by omega)

attribute [local irreducible] main

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.foldlRange_structuralComputableWitnesses_iff]
  intro i
  rw [show (body default i).localLength = 6400 from
      keccakRound_localLength (rc i) (rc_lt i) default 0,
    body_eq_subcircuit (acc offset input i) i,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    (KeccakRound.circuit (rc i) (rc_lt i)) input (acc offset input i)
    (offset + i.val * 6400)
    (by
      intro kk e e' hle h_agree h_input
      obtain ⟨_ | k', hiv⟩ := i
      · rw [acc_zero input offset hiv]
        exact h_input
      · rw [acc_succ input offset k' hiv]
        exact eval_stateVar_of_agreesBelow offset k'
          (by rw [show (⟨k' + 1, hiv⟩ : Fin 24).val = k' + 1 from rfl] at hle; omega) h_agree)
    (KeccakRound.computableWitnesses (rc i) (rc_lt i)) env env'

end Solution.KeccakF1600.Permutation
