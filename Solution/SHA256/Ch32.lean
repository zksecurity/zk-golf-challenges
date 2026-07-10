import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Ch32Theorems
import Challenge.Specs.SHA256
import Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# Choice function Ch(e, f, g) for SHA-256

Ch(e, f, g) = (e AND f) XOR (NOT e AND g) = g + e·(f − g).
Per bit: ch = g + e·(f − g), which equals f when e = 1 and g when e = 0.
One R1CS constraint per bit: e·(f − g) = ch − g.
Witnesses 32 output bits.
-/

namespace Ch32

/-- Choice function: Ch(e, f, g) = (e AND f) XOR (NOT e AND g) = g + e·(f − g).
    Per bit: ch = g + e·(f − g), which equals f when e = 1 and g when e = 0.
    One R1CS constraint per bit: e·(f − g) = ch − g. -/
def ch32 (e f g : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      env g[i] + env e[i] * (env f[i] - env g[i])
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] - g[i] - e[i] * (f[i] - g[i]))
  return z

structure Inputs (F : Type) where
  e : fields 32 F
  f : fields 32 F
  g : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  ch32 input.e input.f input.g

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.e ∧ Normalized input.f ∧ Normalized input.g

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.Ch (valueBits input.e) (valueBits input.f) (valueBits input.g) ∧
  Normalized z

/-!
## Helper lemmas

Gadget-private lemmas live in `Ch32Theorems`. Shared lemmas
(`sum_bool_lt_two_pow`, `testBit_binary_sum`, ...) live in `Theorems`.
-/

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ch32]
  obtain ⟨he, hf, hg⟩ := h_assumptions
  obtain ⟨h_input_e, h_input_f, h_input_g⟩ := h_input
  have h_ei : ∀ i : Fin 32, Expression.eval env input_var_e[i.val] = input_e[i] := by
    intro i; have := Vector.ext_iff.mp h_input_e i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_fi : ∀ i : Fin 32, Expression.eval env input_var_f[i.val] = input_f[i] := by
    intro i; have := Vector.ext_iff.mp h_input_f i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_gi : ∀ i : Fin 32, Expression.eval env input_var_g[i.val] = input_g[i] := by
    intro i; have := Vector.ext_iff.mp h_input_g i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_eq : ∀ i : Fin 32, env.get (i₀ + i.val) = input_g[i] + input_e[i] * (input_f[i] - input_g[i]) := by
    intro i
    have h := h_holds i; rw [h_ei i, h_fi i, h_gi i] at h
    have key : env.get (i₀ + i.val) - (input_g[i] + input_e[i] * (input_f[i] - input_g[i])) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + i} : Expression (F p))) with hz_def
  have h_z : ∀ i : Fin 32, z[i] = env.get (i₀ + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_eq' : ∀ i : Fin 32, z[i] = input_g[i] + input_e[i] * (input_f[i] - input_g[i]) := by
    intro i; rw [h_z i]; exact h_eq i
  exact spec_of_constraint input_e input_f input_g z he hf hg h_eq'

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [ch32]
  obtain ⟨he, hf, hg⟩ := h_assumptions
  obtain ⟨h_input_e, h_input_f, h_input_g⟩ := h_input
  have h_ei : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_e[i.val] = input_e[i] := by
    intro i; have := Vector.ext_iff.mp h_input_e i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_fi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_f[i.val] = input_f[i] := by
    intro i; have := Vector.ext_iff.mp h_input_f i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_gi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_g[i.val] = input_g[i] := by
    intro i; have := Vector.ext_iff.mp h_input_g i i.isLt; simp [Vector.getElem_map] at this; exact this
  intro i
  have henv := h_env i
  simp only [Vector.getElem_ofFn] at henv
  rw [h_ei i, h_fi i, h_gi i] at henv
  rw [henv, h_gi i, h_ei i, h_fi i]; ring

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main ch32
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
    have he :
        Expression.eval env.toEnvironment input.e[i] =
          Expression.eval env'.toEnvironment input.e[i] :=
      h_input.1 _ (by simp)
    have hf :
        Expression.eval env.toEnvironment input.f[i] =
          Expression.eval env'.toEnvironment input.f[i] :=
      h_input.2.1 _ (by simp)
    have hg :
        Expression.eval env.toEnvironment input.g[i] =
          Expression.eval env'.toEnvironment input.g[i] :=
      h_input.2.2 _ (by simp)
    simp [hg, he, hf]
  · intro _
    trivial

end Ch32
end Solution.SHA256
end
