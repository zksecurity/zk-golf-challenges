import Solution.SHA256.Xor32
import Solution.SHA256.Theorems
import Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# σ₁ (lower sigma 1) for SHA-256

σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)

Two xor32 calls = 64 witnesses total.

Mirrors `LowerSigma0` with constants 17, 19, 10 instead of 7, 18, 3.
Reuses the shared helper lemmas in `Theorems`.
-/

namespace LowerSigma1

/-- σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x) -/
def lowerSigma1 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let r1 ← Xor32.circuit ⟨rotr32 17 x, rotr32 19 x⟩
  Xor32.circuit ⟨r1, shr32 10 x⟩

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  lowerSigma1 x

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.lowerSigma1 (valueBits x) ∧ Normalized z

/-! ## Soundness / Completeness

This gadget composes two `Xor32.circuit` subcircuits over `rotr32`/`shr32` of the
input. Both proofs reuse `Xor32`'s `Assumptions`/`Spec` and the shared
`Normalized_eval_*` / `valueBits_eval_*` bridges in `Theorems`; they never touch
witness indices. -/

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [lowerSigma1, Xor32.circuit]
  simp only [Xor32.Assumptions, Xor32.Spec, and_imp] at h_holds
  obtain ⟨c1, c2⟩ := h_holds
  have nr17 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 17
  have nr19 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 19
  have ns10 := Normalized_eval_shr32 env input_var input h_input h_assumptions 10
  obtain ⟨v1, n1⟩ := c1 nr17 nr19
  obtain ⟨v2, n2⟩ := c2 n1 ns10
  refine ⟨?_, n2⟩
  rw [v2, v1, valueBits_eval_rotr32 env input_var input h_input h_assumptions 17,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 19,
    valueBits_eval_shr32 env input_var input h_input h_assumptions 10]
  rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [lowerSigma1, Xor32.circuit]
  simp only [Xor32.Assumptions, Xor32.Spec, and_imp] at h_env ⊢
  have nr17 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 17
  have nr19 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 19
  have ns10 := Normalized_eval_shr32 env.toEnvironment input_var input h_input h_assumptions 10
  obtain ⟨_, n1⟩ := h_env.1 nr17 nr19
  exact ⟨⟨nr17, nr19⟩, n1, ns10⟩

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main lowerSigma1
  let firstInput : Var Xor32.Inputs (F p) := ⟨rotr32 17 input, rotr32 19 input⟩
  let first : Circuit (F p) (Var (fields 32) (F p)) := Xor32.circuit firstInput
  let r1 := first.output offset
  let n1 := offset + first.localLength offset
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  and_intros
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Xor32.circuit input firstInput offset
      (by
        intro env env' h_input
        simp [circuit_norm] at h_input ⊢
        constructor
        · intro a ha
          exact h_input a (by simpa [firstInput, rotr32, Vector.rotate] using ha)
        · intro a ha
          exact h_input a (by simpa [firstInput, rotr32, Vector.rotate] using ha))
      Xor32.computableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Xor32.circuit input ⟨r1, shr32 10 input⟩ n1
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm] at h_input
        simp [circuit_norm]
        constructor
        · exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
            h_agree (by
              have hlen : first.localLength offset = 32 := by
                dsimp [first, firstInput, Xor32.circuit]
                rfl
              omega)
        · intro a ha
          simp [shr32] at ha
          rcases ha with ⟨i, rfl⟩
          by_cases h : i.val + 10 < 32
          · simp [h]
            exact h_input _ (Vector.getElem_mem h)
          · simp [h, Expression.eval])
      Xor32.computableWitnesses env env'

end LowerSigma1
end Solution.SHA256
end
