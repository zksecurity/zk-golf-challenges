import Solution.SHA256.Xor32
import Solution.SHA256.Theorems

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

end LowerSigma1
end Solution.SHA256
end
