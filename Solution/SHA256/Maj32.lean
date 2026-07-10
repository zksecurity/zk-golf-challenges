import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Maj32Theorems
import Challenge.Specs.SHA256
import Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# Majority function Maj(a, b, c) for SHA-256

Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c).
Decomposition: let t = a·b; then maj = t + c·(a + b − 2·t).
Two R1CS constraints per bit:
  (1)  a·b = t
  (2)  c·(a + b − 2·t) = z − t
Witnesses 64 variables: 32 for t, 32 for z.
-/

namespace Maj32

/-- Majority function: Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c).
    Decomposition: let t = a·b; then maj = t + c·(a + b − 2·t).
    Two R1CS constraints per bit:
      (1)  a·b = t
      (2)  c·(a + b − 2·t) = z − t -/
def maj32 (a b c : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  -- Witness the intermediate product t[i] = a[i] * b[i]
  let t ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) => env a[i] * env b[i]
  -- Witness the majority output
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      env t[i] + env c[i] * (env a[i] + env b[i] - 2 * env t[i])
  -- Constraint (1): t[i] = a[i] * b[i]
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (t[i] - a[i] * b[i])
  -- Constraint (2): z[i] = t[i] + c[i] * (a[i] + b[i] - 2 * t[i])
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] - t[i] - c[i] * (a[i] + b[i] - 2 * t[i]))
  return z

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
  c : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  maj32 input.a input.b input.c

@[reducible] instance elaborated : ElaboratedCircuit (F p) _ _ main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.Maj (valueBits input.a) (valueBits input.b) (valueBits input.c) ∧
  Normalized z

/-!
## Helper lemmas for valueBits and bitwise Maj

Gadget-private lemmas live in `Maj32Theorems`. Shared lemmas
(`sum_bool_lt_two_pow`, `testBit_binary_sum`, ...) live in `Theorems`.
-/

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [maj32]
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_ci : ∀ i : Fin 32, Expression.eval env input_var_c[i.val] = input_c[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_c i i.isLt
    simp [Vector.getElem_map] at this; exact this
  -- Extract the two sets of constraints from h_holds
  obtain ⟨h_holds_t, h_holds_z⟩ := h_holds
  -- t[i] = a[i] * b[i]
  have h_t : ∀ i : Fin 32, env.get (i₀ + i.val) = input_a[i] * input_b[i] := by
    intro i
    have := h_holds_t i; rw [h_ai i, h_bi i] at this
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact this)
  -- z[i] = t[i] + c[i] * (a[i] + b[i] - 2 * t[i])
  have h_z : ∀ i : Fin 32, env.get (i₀ + 32 + i.val) =
      input_a[i] * input_b[i] + input_c[i] * (input_a[i] + input_b[i] - 2 * (input_a[i] * input_b[i])) := by
    intro i
    have := h_holds_z i; rw [h_t i, h_ai i, h_bi i, h_ci i] at this
    exact eq_of_sub_eq_zero (by ring_nf; ring_nf at this; exact this)
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + 32 + i} : Expression (F p))) with hz_def
  have h_z_get : ∀ i : Fin 32, z[i] = env.get (i₀ + 32 + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_eq' : ∀ i : Fin 32, z[i] =
      input_a[i] * input_b[i] + input_c[i] * (input_a[i] + input_b[i] - 2 * (input_a[i] * input_b[i])) := by
    intro i; rw [h_z_get i]; exact h_z i
  exact spec_of_constraint input_a input_b input_c z ha hb hc h_eq'

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [maj32]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (h_env.1) i
    simp only [Vector.getElem_ofFn] at this
    rw [this]; ring
  · have := (h_env.2.1) i
    simp only [Vector.getElem_ofFn] at this
    rw [this]; ring

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main maj32
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    simp [circuit_norm] at h_input
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have ha :
        Expression.eval env.toEnvironment input.a[i] =
          Expression.eval env'.toEnvironment input.a[i] :=
      h_input.1 _ (by simp)
    have hb :
        Expression.eval env.toEnvironment input.b[i] =
          Expression.eval env'.toEnvironment input.b[i] :=
      h_input.2.1 _ (by simp)
    simp [ha, hb]
  · intro h_agree h_input
    simp [circuit_norm] at h_input
    simp [Circuit.witnessVector, circuit_norm] at h_agree ⊢
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have ht : env.get (offset + i) = env'.get (offset + i) :=
      h_agree (offset + i) (by omega)
    have ha :
        Expression.eval env.toEnvironment input.a[i] =
          Expression.eval env'.toEnvironment input.a[i] :=
      h_input.1 _ (by simp)
    have hb :
        Expression.eval env.toEnvironment input.b[i] =
          Expression.eval env'.toEnvironment input.b[i] :=
      h_input.2.1 _ (by simp)
    have hc :
        Expression.eval env.toEnvironment input.c[i] =
          Expression.eval env'.toEnvironment input.c[i] :=
      h_input.2.2 _ (by simp)
    simp [ht, ha, hb, hc]
  · intro _
    trivial
  · intro _
    trivial

end Maj32
end Solution.SHA256
end
