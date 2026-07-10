import Solution.KeccakF1600.XorLane

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace ThetaD

def main (c : Var KeccakBitRow (F p)) : Circuit (F p) (Var KeccakBitRow (F p)) :=
  .mapFinRange 5 fun x =>
    XorLane.circuit ⟨c[(x.val + 4) % 5], rotl 1 c[(x.val + 1) % 5]⟩

def Assumptions (c : KeccakBitRow (F p)) : Prop := RowNormalized c

def Spec (c : KeccakBitRow (F p)) (out : KeccakBitRow (F p)) : Prop :=
  RowNormalized out ∧ rowValue out = thetaDSpec (rowValue c)

instance elaborated : ElaboratedCircuit (F p) KeccakBitRow KeccakBitRow main := by
  elaborate_circuit

lemma thetaDSpec_loop (C : Vector ℕ 5) :
    thetaDSpec C = .ofFn fun x =>
      C[(x.val + 4) % 5] ^^^ Specs.Keccak.rotLeft 64 C[(x.val + 1) % 5] 1 := rfl

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [XorLane.circuit, XorLane.Assumptions, XorLane.Spec]
  have hs := h_input
  apply rowNormalized_value_ext
  simp only [thetaDSpec_loop, circuit_norm, eval_vector, rowValue]
  intro x
  have hb : ∀ j (hj : j < 5),
      Vector.map (Expression.eval env) input_var[j] = input[j] := by
    intro j hj
    have h := getElem_eval_vector (α := fields 64) env input_var j hj
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  -- the second XorLane input is `rotl 1` of a normalized lane
  have hrot_val : valueBits (Vector.map (Expression.eval env) (rotl 1 input_var[(x.val + 1) % 5]))
      = Specs.Keccak.rotLeft 64 (valueBits input[(x.val + 1) % 5]) 1 :=
    valueBits_eval_rotl env _ input[(x.val + 1) % 5] (hb _ (by omega))
      (h_assumptions ⟨(x.val + 1) % 5, by omega⟩) 1
  have hrot_norm : Normalized (Vector.map (Expression.eval env) (rotl 1 input_var[(x.val + 1) % 5])) :=
    Normalized_eval_rotl env _ input[(x.val + 1) % 5] (hb _ (by omega))
      (h_assumptions ⟨(x.val + 1) % 5, by omega⟩) 1
  have harg : Normalized (Vector.map (Expression.eval env) input_var[(x.val + 4) % 5])
      ∧ Normalized (Vector.map (Expression.eval env) (rotl 1 input_var[(x.val + 1) % 5])) := by
    rw [hb _ (by omega)]
    exact ⟨h_assumptions ⟨(x.val + 4) % 5, by omega⟩, hrot_norm⟩
  obtain ⟨h_val, h_norm⟩ := h_holds x harg
  refine ⟨h_norm, ?_⟩
  rw [Vector.getElem_ofFn, h_val, hb _ (by omega), hrot_val]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [XorLane.circuit, XorLane.Assumptions, XorLane.Spec]
  have hs := h_input
  intro x
  have hb : ∀ j (hj : j < 5),
      Vector.map (Expression.eval env.toEnvironment) input_var[j] = input[j] := by
    intro j hj
    have h := getElem_eval_vector (α := fields 64) env.toEnvironment input_var j hj
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  have hrot_norm :
      Normalized (Vector.map (Expression.eval env.toEnvironment) (rotl 1 input_var[(x.val + 1) % 5])) :=
    Normalized_eval_rotl env.toEnvironment _ input[(x.val + 1) % 5] (hb _ (by omega))
      (h_assumptions ⟨(x.val + 1) % 5, by omega⟩) 1
  rw [hb _ (by omega)]
  exact ⟨h_assumptions ⟨(x.val + 4) % 5, by omega⟩, hrot_norm⟩

def circuit : FormalCircuit (F p) KeccakBitRow KeccakBitRow where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.mapFinRange_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  intro x
  exact @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    (F p) _ KeccakBitRow XorLane.Inputs (fields 64) _ _ _
    XorLane.circuit input ⟨input[(x.val + 4) % 5], rotl 1 input[(x.val + 1) % 5]⟩ _
    (by
      intro env env' h_input
      simp [circuit_norm] at h_input ⊢
      have hword : ∀ (j : ℕ) (hj : j < 5),
          Vector.map (Expression.eval env.toEnvironment) (input[j]'hj)
            = Vector.map (Expression.eval env'.toEnvironment) (input[j]'hj) := by
        intro j hj
        rw [← CircuitType.eval_var_fields env.toEnvironment (input[j]'hj),
          ← CircuitType.eval_var_fields env'.toEnvironment (input[j]'hj),
          getElem_eval_vector env.toEnvironment input j hj,
          getElem_eval_vector env'.toEnvironment input j hj]
        exact congrArg (fun v : KeccakBitRow (F p) => v[j]'hj) h_input
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · simp only [Vector.mem_iff_getElem] at ha
        rcases ha with ⟨b, hb, hget⟩
        rw [← hget]
        simpa [Vector.getElem_map] using
          Vector.ext_iff.mp (hword ((↑x + 4) % 5) (by omega)) b hb
      · simp only [Vector.mem_iff_getElem] at ha
        rcases ha with ⟨b, hb, hget⟩
        rw [← hget, rotl, Vector.getElem_rotate hb]
        simpa [Vector.getElem_map] using
          Vector.ext_iff.mp (hword ((↑x + 1) % 5) (by omega))
            ((b + (64 - 1 % 64)) % 64) (Nat.mod_lt _ (by norm_num)))
    XorLane.computableWitnesses env env'

end ThetaD
end Solution.KeccakF1600
end
