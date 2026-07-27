import Solution.SHA256CompressGF2Canonical.Ch32Canon
import Solution.SHA256CompressGF2.Theorems
import Solution.SHA256CompressGF2.Cost
import Challenge.Utils.CostR1CSCanonical

/-!
# `Maj32Canon`: canonical (C = identity) Maj gadget
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Maj32Canon

open Solution.SHA256CompressGF2 (a96 a96_affine maj_words)

/-- Witness the AND `pᵢ = (aᵢ+cᵢ)·(bᵢ+cᵢ)`, pin with `pᵢ − (aᵢ+cᵢ)·(bᵢ+cᵢ) = 0`
(C = pᵢ), output inlined `cᵢ ⊕ pᵢ = Maj`. -/
def main (v : Var (fields 96) (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let p ← witnessVector 32 (fun env => Vector.ofFn fun i : Fin 32 =>
    ((a96 v i.val + a96 v (64 + i.val)) * (a96 v (32 + i.val) + a96 v (64 + i.val))).eval env)
  Circuit.forEach (Vector.finRange 32) (fun i =>
    assertZero (p[i.val]'i.isLt
      - (a96 v i.val + a96 v (64 + i.val)) * (a96 v (32 + i.val) + a96 v (64 + i.val))))
  return zxorOut v p

instance elaborated : ElaboratedCircuit (F p2) (fields 96) (fields 32) main := by
  elaborate_circuit

def Assumptions (_ : fields 96 (F p2)) : Prop := True

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
  rw [Vector.getElem_map]
  unfold zxorOut
  rw [Vector.getElem_ofFn]
  simp only [circuit_norm]
  have hc := h_holds ⟨j, hj⟩
  rw [hv (64 + j) (by omega), hv j (by omega), hv (32 + j) (by omega)] at hc
  rw [hv (64 + j) (by omega)]
  congr 1
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

/-- The canonical `Maj` output is the input word `c` xored with the AND witnesses. -/
theorem eval_subOut_of_agreesBelow (v : Var (fields 96) (F p2)) (n : ℕ) {k : ℕ} (hk : n + 32 ≤ k)
    {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow k env') (h_input : eval env v = eval env' v) :
    eval env ((subcircuit circuit v).output n)
      = eval env' ((subcircuit circuit v).output n) := by
  have hout : (subcircuit circuit v).output n = zxorOut v (varFromOffset (fields 32) n) := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  rw [hout]
  exact eval_zxorOut_congr h_input (eval_varFromOffset_of_agreesBelow h_agree (by omega))

end ComputableWitness

end Maj32Canon

end Solution.SHA256CompressGF2
