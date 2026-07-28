import Solution.Blake3CompressGF2Canonical.Add32Theorems
import Challenge.Utils.CostR1CSCanonical

/-!
# Canonical pins: explicit `·1` product rows

Same gadgets as `Pin32`/`Pin256` (materialize expression bits as fresh
witnesses), but each row is written as an explicit product `wᵢ − (vᵢ)·1`: the
ordered identity-C obligation has no linear-row case, so the constant-one `B`
must appear in the constraint expression itself. Same cost, same matrices
(`B` is the constant-one column either way); the shared `Pin32`/`Pin256` used
by the general-C solution are untouched.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

namespace Pin32Canon

@[reducible] def b32 {α : Type} (v : Vector α 32) (i : ℕ) : α :=
  v[i % 32]'(Nat.mod_lt _ (by norm_num))

def Assumptions (_ : fields 32 (F p2)) : Prop := True

def Spec (input output : fields 32 (F p2)) : Prop :=
  output = input

/-- Materialize 32 expression bits as fresh witnesses, `wᵢ − (vᵢ)·1 = 0`. -/
def main (v : Var (fields 32) (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let w ← witnessVector 32 (fun env => Vector.ofFn fun i : Fin 32 =>
    (b32 v i.val).eval env)
  Circuit.forEach (Vector.finRange 32) (fun i =>
    assertZero (w[i.val]'i.isLt - b32 v i.val * 1))
  return w

instance elaborated : ElaboratedCircuit (F p2) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec]
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_map, Vector.getElem_mapRange]
  have hc := h_holds ⟨j, hj⟩
  have hv : Expression.eval env (b32 input_var j) = input[j]'hj := by
    unfold b32
    have h2 := Vector.ext_iff.mp h_input (j % 32) (Nat.mod_lt _ (by norm_num))
    rw [Vector.getElem_map] at h2
    simp only [Nat.mod_eq_of_lt hj] at h2 ⊢
    exact h2
  rw [hv] at hc
  rw [show Expression.eval env (var { index := i₀ + j }) = env.get (i₀ + j) from rfl]
  linear_combination hc

theorem completeness : Completeness (F p2) main Assumptions := by
  circuit_proof_start
  intro i
  have henv := h_env i
  simp only [circuit_norm, Vector.getElem_ofFn] at henv ⊢
  rw [henv]; ring

def circuit : FormalCircuit (F p2) (fields 32) (fields 32) :=
  { main, elaborated, Assumptions := Assumptions, Spec := Spec,
    soundness, completeness }

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
    simp only [Vector.getElem_ofFn, b32, circuit_norm, eval_getElem_congr h_input]
  · intro _
    trivial

theorem subcircuit_localLength (v : Var (fields 32) (F p2)) (m : ℕ) :
    (subcircuit circuit v).localLength m = 32 := rfl

theorem eval_subOut_of_agreesBelow (v : Var (fields 32) (F p2)) (n : ℕ) {k : ℕ}
    (hk : n + 32 ≤ k)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit v).output n)
      = eval env' ((subcircuit circuit v).output n) := by
  have hout : (subcircuit circuit v).output n = varFromOffset (fields 32) n := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree hk

end ComputableWitness

end Pin32Canon

namespace PinStateCanon

@[reducible] def b512 {α : Type} (v : Vector α 512) (i : ℕ) : α :=
  v[i % 512]'(Nat.mod_lt _ (by norm_num))

def Assumptions (_ : fields 512 (F p2)) : Prop := True

def Spec (input output : fields 512 (F p2)) : Prop :=
  output = input

def main (v : Var (fields 512) (F p2)) :
    Circuit (F p2) (Var (fields 512) (F p2)) := do
  let w ← witnessVector 512 (fun env => Vector.ofFn fun i : Fin 512 =>
    (b512 v i.val).eval env)
  Circuit.forEach (Vector.finRange 512) (fun i =>
    assertZero (w[i.val]'i.isLt - b512 v i.val * 1))
  return w

instance elaborated :
    ElaboratedCircuit (F p2) (fields 512) (fields 512) main := by
  elaborate_circuit

theorem soundness : Soundness (F p2) main Assumptions Spec := by
  circuit_proof_start [main, Spec]
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_map, Vector.getElem_mapRange]
  have hc := h_holds ⟨j, hj⟩
  have hv : Expression.eval env (b512 input_var j) = input[j]'hj := by
    unfold b512
    have h2 := Vector.ext_iff.mp h_input (j % 512) (Nat.mod_lt _ (by norm_num))
    rw [Vector.getElem_map] at h2
    simp only [Nat.mod_eq_of_lt hj] at h2 ⊢
    exact h2
  rw [hv] at hc
  rw [show Expression.eval env (var { index := i₀ + j }) = env.get (i₀ + j) from rfl]
  linear_combination hc

theorem completeness : Completeness (F p2) main Assumptions := by
  circuit_proof_start
  intro i
  have henv := h_env i
  simp only [circuit_norm, Vector.getElem_ofFn] at henv ⊢
  rw [henv]
  ring

def circuit : FormalCircuit (F p2) (fields 512) (fields 512) :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

set_option maxRecDepth 2000 in
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
    simp only [Vector.getElem_ofFn, b512, circuit_norm, eval_getElem_congr h_input]
  · intro _
    trivial

theorem subcircuit_localLength (v : Var (fields 512) (F p2)) (m : ℕ) :
    (subcircuit circuit v).localLength m = 512 := rfl

theorem eval_subOut_of_agreesBelow (v : Var (fields 512) (F p2)) (n : ℕ) {k : ℕ}
    (hk : n + 512 ≤ k)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit v).output n)
      = eval env' ((subcircuit circuit v).output n) := by
  have hout : (subcircuit circuit v).output n = varFromOffset (fields 512) n := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree hk

end ComputableWitness

end PinStateCanon

end Solution.Blake3CompressGF2Canonical
