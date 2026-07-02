import Solution.SHA256.Xor32
import Solution.SHA256.Theorems

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# Σ₀ (upper sigma 0) for SHA-256

Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x)

Two xor32 calls = 64 witnesses total.

Mirrors `LowerSigma0` but with three rotations (no shift) and constants 2, 13, 22.
Reuses the shared helper lemmas in `Theorems`.
-/

namespace UpperSigma0

/-- Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x) -/
def upperSigma0 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let r1 ← Xor32.circuit ⟨rotr32 2 x, rotr32 13 x⟩
  Xor32.circuit ⟨r1, rotr32 22 x⟩

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  upperSigma0 x

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.upperSigma0 (valueBits x) ∧ Normalized z

/-! ## Soundness / Completeness

This gadget composes two `Xor32.circuit` subcircuits over three `rotr32`s of the
input. Both proofs reuse `Xor32`'s `Assumptions`/`Spec` and the shared
`Normalized_eval_rotr32` / `valueBits_eval_rotr32` bridges in `Theorems`; they
never touch witness indices. -/

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [upperSigma0, Xor32.circuit]
  simp only [Xor32.Assumptions, Xor32.Spec, and_imp] at h_holds
  obtain ⟨c1, c2⟩ := h_holds
  have nr2 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 2
  have nr13 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 13
  have nr22 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 22
  obtain ⟨v1, n1⟩ := c1 nr2 nr13
  obtain ⟨v2, n2⟩ := c2 n1 nr22
  refine ⟨?_, n2⟩
  rw [v2, v1, valueBits_eval_rotr32 env input_var input h_input h_assumptions 2,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 13,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 22]
  rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [upperSigma0, Xor32.circuit]
  simp only [Xor32.Assumptions, Xor32.Spec, and_imp] at h_env ⊢
  have nr2 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 2
  have nr13 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 13
  have nr22 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 22
  obtain ⟨_, n1⟩ := h_env.1 nr2 nr13
  exact ⟨⟨nr2, nr13⟩, n1, nr22⟩

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end UpperSigma0
end Solution.SHA256
end
