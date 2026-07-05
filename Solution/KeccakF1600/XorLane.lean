import Solution.KeccakF1600.BitwiseOps
import Solution.KeccakF1600.Theorems

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace XorLane

/-- Bitwise XOR of two 64-bit lanes.
    Per bit: z = a + b − 2·a·b  (correct when a, b ∈ {0, 1}).
    Witnesses 64 output bits.

    Shared building block: the θ and χ gadgets call `xorLane` through
    `XorLane.circuit`. -/
def xorLane (a b : Var (fields 64) (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let z ← witnessVector 64 fun env =>
    Vector.ofFn fun (i : Fin 64) =>
      ((env a[i]).val ^^^ (env b[i]).val : F p)
  Circuit.forEach (Vector.finRange 64) fun i =>
    assertZero (z[i] - a[i] - b[i] + 2 * a[i] * b[i])
  return z

structure Inputs (F : Type) where
  a : fields 64 F
  b : fields 64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 64) (F p)) :=
  xorLane input.a input.b

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 64 (F p)) : Prop :=
  valueBits z = valueBits input.a ^^^ valueBits input.b ∧ Normalized z

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 64) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [xorLane]
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
  -- h_holds: env.get(i₀+i) = a[i] + b[i] - 2*a[i]*b[i]
  have h_eq : ∀ i : Fin 64, env.get (i₀ + i.val) = input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i] := by
    intro i
    have h := h_holds i; rw [h_ai i, h_bi i] at h
    -- h: env.get(i₀+i) + -a[i] + -b[i] + 2*a[i]*b[i] = 0
    have key : env.get (i₀ + i.val) - (input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i]) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  have h_z : Vector.map (Expression.eval env) (Vector.mapRange 64 fun i =>
      (var {index := i₀ + i} : Expression (F p)))
      = Vector.ofFn fun i : Fin 64 => env.get (i₀ + i.val) := by
    ext i; simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  rw [h_z]
  have h_norm : ∀ i : Fin 64, env.get (i₀ + i.val) = 0 ∨ env.get (i₀ + i.val) = 1 := by
    intro i; rw [h_eq i]; exact IsBool.xor_is_bool (ha i) (hb i)
  refine ⟨?_, fun i => ?_⟩
  · simp only [valueBits]
    simp_rw [show ∀ i : Fin 64, (Vector.ofFn fun j : Fin 64 => env.get (i₀ + j.val))[i] =
        env.get (i₀ + i.val) from fun i => by simp [Vector.getElem_ofFn]]
    simp_rw [h_eq, IsBool.xor_eq_val_xor (ha _) (hb _)]
    exact (bool_finsum_xor_eq 64 (fun i => (input_a[i] : F p).val) (fun i => (input_b[i] : F p).val)
      (fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])
      (fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]))
  · have : (Vector.ofFn fun j : Fin 64 => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) := by
      simp [Vector.getElem_ofFn]
    rw [this]; exact h_norm i

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [xorLane]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  have h_ai : ∀ i : Fin 64, Expression.eval env.toEnvironment input_var_a[i.val] = input_a[i] := by
    intro i; have := Vector.ext_iff.mp h_input_a i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 64, Expression.eval env.toEnvironment input_var_b[i.val] = input_b[i] := by
    intro i; have := Vector.ext_iff.mp h_input_b i i.isLt; simp [Vector.getElem_map] at this; exact this
  intro i
  have henv := h_env i
  simp only [Vector.getElem_ofFn] at henv
  rw [h_ai i, h_bi i] at henv
  have hcast : ((input_a[i].val ^^^ input_b[i].val : ℕ) : F p) =
      input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i] := by
    rw [← IsBool.xor_eq_val_xor (ha i) (hb i)]
    have := ZMod.natCast_val (R := ZMod p) (input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i])
    rw [this]; exact ZMod.cast_id p _
  rw [henv, hcast, h_ai i, h_bi i]; ring

def circuit : FormalCircuit (F p) Inputs (fields 64) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end XorLane
end Solution.KeccakF1600
end
