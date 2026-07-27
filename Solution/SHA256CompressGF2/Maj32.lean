import Solution.SHA256CompressGF2.Theorems

/-!
# `Maj32`: bitwise gadget over GF(2)
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Maj32

/-- Input `v = a ‖ b ‖ c`. Witness `maj_j = (a_j+c_j)·(b_j+c_j) + c_j`, pin with
`(w − c) − (a+c)·(b+c) = 0`. -/
def main (v : Var (fields 96) (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let w ← witnessVector 32 (fun env => Vector.ofFn fun i : Fin 32 =>
    ((a96 v i.val + a96 v (64 + i.val)) * (a96 v (32 + i.val) + a96 v (64 + i.val))
      + a96 v (64 + i.val)).eval env)
  Circuit.forEach (Vector.finRange 32) (fun i =>
    assertZero ((w[i.val]'i.isLt - a96 v (64 + i.val))
      - (a96 v i.val + a96 v (64 + i.val)) * (a96 v (32 + i.val) + a96 v (64 + i.val))))
  return w

instance elaborated : ElaboratedCircuit (F p2) (fields 96) (fields 32) main := by
  elaborate_circuit

def Assumptions (_ : fields 96 (F p2)) : Prop := True

/-- `Maj` on the packed words of `v = a ‖ b ‖ c`. -/
def Spec (v : fields 96 (F p2)) (out : fields 32 (F p2)) : Prop :=
  toNat out = Specs.SHA256.Maj (wordAt 32 v 0) (wordAt 32 v 1) (wordAt 32 v 2)

theorem soundness : Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec]
  have hv : ∀ (m : ℕ) (hm : m < 96),
      Expression.eval env (a96 input_var m) = input[m]'hm := by
    intro m hm
    unfold a96
    have h2 := Vector.ext_iff.mp h_input (m % 96) (Nat.mod_lt _ (by norm_num))
    rw [Vector.getElem_map] at h2
    simp only [Nat.mod_eq_of_lt hm] at h2 ⊢
    exact h2
  refine maj_words input _ fun j hj => ?_
  rw [Vector.getElem_map, Vector.getElem_mapRange]
  have hc := h_holds ⟨j, hj⟩
  rw [hv (64 + j) (by omega), hv j (by omega), hv (32 + j) (by omega)] at hc
  congr 1
  rw [show Expression.eval env (var { index := i₀ + j }) = env.get (i₀ + j) from rfl]
  linear_combination hc

theorem completeness : Completeness (F p2) main Assumptions := by
  circuit_proof_start
  intro i
  have henv := h_env i
  simp only [circuit_norm, Vector.getElem_ofFn] at henv ⊢
  rw [henv]; ring

def circuit : FormalCircuit (F p2) (fields 96) (fields 32) :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
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
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn, a96, circuit_norm, eval_getElem_congr h_input]
  · intro _
    trivial

theorem subcircuit_localLength (v : Var (fields 96) (F p2)) (m : ℕ) :
    (subcircuit circuit v).localLength m = 32 := rfl

theorem eval_subOut_of_agreesBelow (v : Var (fields 96) (F p2)) (n : ℕ) {k : ℕ} (hk : n + 32 ≤ k)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit v).output n)
      = eval env' ((subcircuit circuit v).output n) := by
  have hout : (subcircuit circuit v).output n = varFromOffset (fields 32) n := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree hk

end ComputableWitness

end Maj32

end Solution.SHA256CompressGF2
