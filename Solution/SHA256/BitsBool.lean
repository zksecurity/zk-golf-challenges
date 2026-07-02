import Solution.SHA256.Common

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256
namespace BitsBool

/-!
# Boolean-bits assertion

A `FormalAssertion` over `fields n` that asserts every entry is boolean
(0 or 1), via the per-entry R1CS constraint `x * (x - 1) = 0`.

Kept generic in `n` so elaboration does not unfold any concrete length;
instantiated downstream at `n = paddedBitsLen`.
-/

def main (n : ℕ) [NeZero n] (input : Var (fields n) (F p)) : Circuit (F p) Unit :=
  Circuit.forEach (Vector.finRange n) fun i =>
    assertZero (input[i] * (input[i] - 1))

def Spec {n : ℕ} (input : fields n (F p)) : Prop := ∀ i : Fin n, IsBool input[i]

instance elaborated (n : ℕ) [NeZero n] : ElaboratedCircuit (F p) (fields n) unit (main n) := by
  elaborate_circuit

/-! ## Soundness and completeness -/

theorem soundness (n : ℕ) [NeZero n] :
    FormalAssertion.Soundness (F p) (main n) (fun _ => True) Spec := by
  circuit_proof_start [main]
  intro i
  have hi := h_holds i
  have hval : input[i.val] = Expression.eval env input_var[i.val] := by
    rw [← h_input, Vector.getElem_map]
  rw [hval, IsBool.iff_mul_sub_one, sub_eq_add_neg]
  exact hi

theorem completeness (n : ℕ) [NeZero n] :
    FormalAssertion.Completeness (F p) (main n) (fun _ => True) Spec := by
  circuit_proof_start [main]
  intro i
  have hb := h_spec i
  have hval : input[i.val] = Expression.eval env.toEnvironment input_var[i.val] := by
    rw [← h_input, Vector.getElem_map]
  rw [hval, IsBool.iff_mul_sub_one, sub_eq_add_neg] at hb
  exact hb

def circuit (n : ℕ) [NeZero n] : FormalAssertion (F p) (fields n) :=
  { main := main n
    elaborated := elaborated n
    Assumptions := fun _ => True
    Spec := Spec
    soundness := by simp only [soundness]
    completeness := by simp only [completeness]
    exposedChannels_eq := by intro _ _ exposed h; simp at h }

end BitsBool
end Solution.SHA256
end
