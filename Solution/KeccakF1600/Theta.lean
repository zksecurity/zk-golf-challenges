import Solution.KeccakF1600.ThetaC
import Solution.KeccakF1600.ThetaD
import Solution.KeccakF1600.ThetaXor

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace Theta

def main (state : Var KeccakBitState (F p)) : Circuit (F p) (Var KeccakBitState (F p)) := do
  let c ← ThetaC.circuit state
  let d ← ThetaD.circuit c
  ThetaXor.circuit ⟨state, d⟩

def Assumptions (state : KeccakBitState (F p)) : Prop := StateNormalized state

def Spec (state : KeccakBitState (F p)) (out : KeccakBitState (F p)) : Prop :=
  StateNormalized out ∧
  stateValue out =
    thetaXorSpec (stateValue state) (thetaDSpec (thetaCSpec (stateValue state)))

instance elaborated : ElaboratedCircuit (F p) KeccakBitState KeccakBitState main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ThetaC.circuit, ThetaC.Assumptions, ThetaC.Spec,
    ThetaD.circuit, ThetaD.Assumptions, ThetaD.Spec,
    ThetaXor.circuit, ThetaXor.Assumptions, ThetaXor.Spec]
  obtain ⟨h_c, h_d, h_x⟩ := h_holds
  obtain ⟨c_norm, c_val⟩ := h_c h_assumptions
  obtain ⟨d_norm, d_val⟩ := h_d c_norm
  obtain ⟨out_norm, out_val⟩ := h_x ⟨h_assumptions, d_norm⟩
  refine ⟨out_norm, ?_⟩
  rw [out_val, d_val, c_val]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [ThetaC.circuit, ThetaC.Assumptions, ThetaC.Spec,
    ThetaD.circuit, ThetaD.Assumptions, ThetaD.Spec,
    ThetaXor.circuit, ThetaXor.Assumptions, ThetaXor.Spec]
  obtain ⟨h_c, h_d, _⟩ := h_env
  obtain ⟨c_norm, _⟩ := h_c h_assumptions
  obtain ⟨d_norm, _⟩ := h_d c_norm
  exact ⟨h_assumptions, c_norm, h_assumptions, d_norm⟩

def circuit : FormalCircuit (F p) KeccakBitState KeccakBitState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

open Challenge.Utils.ComputableWitnessLemmas in
/-- Generic version of `eval_mem_varFromOffset_fields_of_agreesBelow` for any
`ProvableType` output (here used for the nested `KeccakBitRow` outputs of the
`ThetaC`/`ThetaD` subcircuits). -/
lemma eval_varFromOffset_of_agreesBelow {α : TypeMap} [ProvableType α]
    {env env' : ProverEnvironment (F p)} {n : ℕ}
    (h : env.AgreesBelow (n + size α) env') :
    (eval env (varFromOffset α n : Var α (F p)) : α (F p)) =
      eval env' (varFromOffset α n : Var α (F p)) := by
  rw [ProvableType.eval_varFromOffset_prover, ProvableType.eval_varFromOffset_prover]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_mapRange]
  exact h (n + i) (by omega)

/-- A `KeccakBitRow` value assembled from per-lane `varFromOffset (fields 64)`
blocks evaluates identically under two environments that agree below `k`, as long as
each lane block lies below `k`. Used for the (possibly scattered) `ThetaC`/`ThetaD`
subcircuit outputs. -/
lemma eval_row_of_agreesBelow {k : ℕ}
    {env env' : ProverEnvironment (F p)} (base : Fin 5 → ℕ)
    (hbound : ∀ i : Fin 5, base i + 64 ≤ k)
    (h : env.AgreesBelow k env') (v : Var KeccakBitRow (F p))
    (hv : v = Vector.mapFinRange 5 fun i =>
      (varFromOffset (fields 64) (base i) : Var (fields 64) (F p))) :
    eval env v = eval env' v := by
  simp only [CircuitType.eval_var_prover_to_verifier]
  rw [hv]
  apply Vector.ext
  intro i hi
  rw [← getElem_eval_vector env.toEnvironment
        (Vector.mapFinRange 5 fun i => (varFromOffset (fields 64) (base i) : Var (fields 64) (F p))) i hi,
      ← getElem_eval_vector env'.toEnvironment
        (Vector.mapFinRange 5 fun i => (varFromOffset (fields 64) (base i) : Var (fields 64) (F p))) i hi,
      Vector.getElem_mapFinRange]
  apply Vector.ext
  intro j hj
  rw [← ProvableType.getElem_eval_fields env.toEnvironment
        (varFromOffset (fields 64) (base ⟨i, hi⟩)) j hj,
      ← ProvableType.getElem_eval_fields env'.toEnvironment
        (varFromOffset (fields 64) (base ⟨i, hi⟩)) j hj,
      ProvableType.varFromOffset_fields, Vector.getElem_mapRange]
  simp only [Expression.eval]
  exact h (base ⟨i, hi⟩ + j) (by have := hbound ⟨i, hi⟩; omega)

attribute [local irreducible] main

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let first : Circuit (F p) (Var KeccakBitRow (F p)) := ThetaC.circuit input
  let c := first.output offset
  let n1 := offset + first.localLength offset
  let second : Circuit (F p) (Var KeccakBitRow (F p)) := ThetaD.circuit c
  let d := second.output n1
  let n2 := n1 + second.localLength n1
  let thirdInput : Var ThetaXor.Inputs (F p) := ⟨input, d⟩
  have hlen1 : first.localLength offset = 1280 := by
    simp [first, ThetaC.circuit, circuit_norm]
  have hlen2 : second.localLength n1 = 320 := by
    simp [second, ThetaD.circuit, circuit_norm]
  have hn1 : n1 = offset + 1280 := by simp only [n1, hlen1]
  have hn2 : n2 = n1 + 320 := by simp only [n2, hlen2]
  have hc : c = (Vector.mapFinRange 5 fun i =>
      (varFromOffset (fields 64) (offset + i.val * 256 + 192) : Var (fields 64) (F p))) := by
    simp [c, first, ThetaC.circuit, circuit_norm]
  have hdvar : d = (Vector.mapFinRange 5 fun i =>
      (varFromOffset (fields 64) (n1 + i.val * 64) : Var (fields 64) (F p))) := by
    simp [d, second, ThetaD.circuit, circuit_norm]
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  and_intros
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      ThetaC.circuit input input offset
      (fun _ _ h => h)
      ThetaC.computableWitnesses env env'
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      ThetaD.circuit input c n1 ?_ ThetaD.computableWitnesses env env'
    intro k e e' hle h_agree h_input
    exact eval_row_of_agreesBelow
      (fun i => offset + i.val * 256 + 192)
      (fun i => by show offset + i.val * 256 + 192 + 64 ≤ k; have := i.isLt; omega)
      h_agree c hc
  · refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      ThetaXor.circuit input thirdInput n2 ?_ ThetaXor.computableWitnesses env env'
    intro k e e' hle h_agree h_input
    have hd : eval e d = eval e' d :=
      eval_row_of_agreesBelow
        (fun i => n1 + i.val * 64)
        (fun i => by show n1 + i.val * 64 + 64 ≤ k; have := i.isLt; omega)
        h_agree d hdvar
    have hstruct : ∀ env : ProverEnvironment (F p),
        eval env thirdInput
          = (⟨eval env input, eval env d⟩ : ThetaXor.Inputs (F p)) := by
      intro env
      simp only [thirdInput, circuit_norm]
    rw [hstruct e, hstruct e', h_input, hd]

end Theta
end Solution.KeccakF1600
end
