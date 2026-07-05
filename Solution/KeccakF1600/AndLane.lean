import Solution.KeccakF1600.BitwiseOps
import Solution.KeccakF1600.Theorems

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace AndLane

/-- Bitwise AND of two 64-bit lanes.
    Per bit: z = a · b  (correct when a, b ∈ {0, 1}). -/
def andLane (a b : Var (fields 64) (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let z ← witnessVector 64 fun env =>
    Vector.ofFn fun (i : Fin 64) =>
      env a[i] * env b[i]
  Circuit.forEach (Vector.finRange 64) fun i =>
    assertZero (z[i] - a[i] * b[i])
  return z

structure Inputs (F : Type) where
  a : fields 64 F
  b : fields 64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 64) (F p)) :=
  andLane input.a input.b

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 64 (F p)) : Prop :=
  valueBits z = valueBits input.a &&& valueBits input.b ∧ Normalized z

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 64) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [andLane]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  have h_ai : ∀ i : Fin 64, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 64, Expression.eval env input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_eq : ∀ i : Fin 64, env.get (i₀ + i.val) = input_a[i] * input_b[i] := by
    intro i
    have := h_holds i; rw [h_ai i, h_bi i] at this
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact this)
  have h_z : Vector.map (Expression.eval env) (Vector.mapRange 64 fun i =>
      (var {index := i₀ + i} : Expression (F p)))
      = Vector.ofFn fun i : Fin 64 => env.get (i₀ + i.val) := by
    ext i; simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  rw [h_z]
  have h_norm : ∀ i : Fin 64, env.get (i₀ + i.val) = 0 ∨ env.get (i₀ + i.val) = 1 := by
    intro i; rw [h_eq i]; exact IsBool.and_is_bool (ha i) (hb i)
  refine ⟨?_, fun i => ?_⟩
  · simp only [valueBits]
    simp_rw [show ∀ i : Fin 64, (Vector.ofFn fun j : Fin 64 => env.get (i₀ + j.val))[i] =
        env.get (i₀ + i.val) from fun i => by simp [Vector.getElem_ofFn]]
    simp_rw [h_eq, IsBool.and_eq_val_and (ha _) (hb _)]
    exact (bool_finsum_and 64 (fun i => (input_a[i] : F p).val) (fun i => (input_b[i] : F p).val)
      (fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])
      (fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])).symm
  · have : (Vector.ofFn fun j : Fin 64 => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) := by
      simp [Vector.getElem_ofFn]
    rw [this]; exact h_norm i

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [andLane]
  intro i
  have := h_env i
  simp only [Vector.getElem_ofFn] at this
  rw [this]; ring

def circuit : FormalCircuit (F p) Inputs (fields 64) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end AndLane
end Solution.KeccakF1600
end
