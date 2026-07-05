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

end ThetaD
end Solution.KeccakF1600
end
