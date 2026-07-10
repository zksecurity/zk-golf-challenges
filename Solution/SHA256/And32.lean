import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.And32Theorems
import Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# 32-bit Bitwise AND for SHA-256

Per bit: z = a · b  (correct when a, b ∈ {0, 1}).
Witnesses 32 output bits.
-/

namespace And32

/-- Bitwise AND of two 32-bit words.
    Per bit: z = a · b  (correct when a, b ∈ {0, 1}). -/
def and32 (a b : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      env a[i] * env b[i]
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] - a[i] * b[i])
  return z

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  and32 input.a input.b

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = valueBits input.a &&& valueBits input.b ∧ Normalized z

/-!
## Helper lemmas for valueBits and bitwise AND

Gadget-private lemmas live in `And32Theorems`. Shared lemmas
(`sum_bool_lt_two_pow`, `testBit_binary_sum`, ...) live in `Theorems`.
-/

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [and32]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_eq : ∀ i : Fin 32, env.get (i₀ + i.val) = input_a[i] * input_b[i] := by
    intro i
    have := h_holds i; rw [h_ai i, h_bi i] at this
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact this)
  have h_z : Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + i} : Expression (F p)))
      = Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := by
    ext i; simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  rw [h_z]
  have h_norm : ∀ i : Fin 32, env.get (i₀ + i.val) = 0 ∨ env.get (i₀ + i.val) = 1 := by
    intro i; rw [h_eq i]; exact IsBool.and_is_bool (ha i) (hb i)
  refine ⟨?_, fun i => ?_⟩
  · simp only [valueBits]
    simp_rw [show ∀ i : Fin 32, (Vector.ofFn fun j : Fin 32 => env.get (i₀ + j.val))[i] =
        env.get (i₀ + i.val) from fun i => by simp [Vector.getElem_ofFn]]
    simp_rw [h_eq, IsBool.and_eq_val_and (ha _) (hb _)]
    exact (bool_finsum_and 32 (fun i => (input_a[i] : F p).val) (fun i => (input_b[i] : F p).val)
      (fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])
      (fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])).symm
  · have : (Vector.ofFn fun j : Fin 32 => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) := by
      simp [Vector.getElem_ofFn]
    rw [this]; exact h_norm i

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [and32]
  intro i
  have := h_env i
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
  unfold main and32
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
      h_input.2 _ (by simp)
    simp [ha, hb]
  · intro _
    trivial

end And32
end Solution.SHA256
end
