import Solution.KeccakF1600.BitwiseOps
import Solution.KeccakF1600.Theorems
import Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace XorLane

/-- Bitwise XOR of two 64-bit lanes.
    Per bit: z = a + b − 2·a·b  (correct when a, b ∈ {0, 1}).
    Witnesses 64 output bits.

    The witness program is the literal per-bit `ℕ`-xor of the two input bits' values,
    cast back into the field; `completeness` and `computableWitnesses` read the
    witnessed cells back in exactly that form.

    Shared building block: the θ and χ gadgets call `xorLane` through
    `XorLane.circuit`. -/
def xorLane (a b : Var (fields 64) (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let z ← Circuit.witnessVector 64 (.lit <| .ofFn fun i : Fin 64 =>
    (a[i].val ^^^ b[i].val).toField)
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
  -- the witness program is a literal vector, so `circuit_proof_start` already reads the
  -- witnessed cells back as the `ℕ`-xor of the two input bits
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  have h_ai : ∀ i : Fin 64, Expression.eval env.toEnvironment input_var_a[i.val] = input_a[i] := by
    intro i; have := Vector.ext_iff.mp h_input_a i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 64, Expression.eval env.toEnvironment input_var_b[i.val] = input_b[i] := by
    intro i; have := Vector.ext_iff.mp h_input_b i i.isLt; simp [Vector.getElem_map] at this; exact this
  intro i
  have henv := h_env i
  -- the u64 sort truncates at 2^64; both operands are bits, so the wrap is the identity
  have hbnd : ∀ x : F p, (x = 0 ∨ x = 1) → x.val % 2 ^ 64 = x.val := by
    rintro x (rfl | rfl)
    · simp
    · rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le 1 p) (by norm_num))
  rw [h_ai i, h_bi i, hbnd _ (ha i), hbnd _ (hb i)] at henv
  have hcast : ((input_a[i].val ^^^ input_b[i].val : ℕ) : F p) =
      input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i] := by
    rw [← IsBool.xor_eq_val_xor (ha i) (hb i)]
    have := ZMod.natCast_val (R := ZMod p) (input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i])
    rw [this]; exact ZMod.cast_id p _
  rw [henv, hcast, h_ai i, h_bi i]; ring

def circuit : FormalCircuit (F p) Inputs (fields 64) where
  main; elaborated; Assumptions; Spec; soundness; completeness

/-- Componentwise characterization of "the two environments evaluate the input
equally". `circuit_norm` no longer reduces `eval` on a struct *variable*, so this
is proved once here by destructuring and reused by the callers. -/
lemma eval_inputs_iff {input : Var Inputs (F p)} {env env' : ProverEnvironment (F p)} :
    eval env input = eval env' input ↔
      ((∀ x ∈ input.a, Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x) ∧
       (∀ x ∈ input.b, Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x)) := by
  obtain ⟨a, b⟩ := input
  simp [circuit_norm, explicit_provable_type]

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main xorLane
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    obtain ⟨ia, ib⟩ := input
    simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h_input
    apply Vector.ext
    intro i hi
    -- the witnessed cell is the literal xor, so it reads only the two input bits
    simp only [circuit_norm]
    have ha := Vector.ext_iff.mp h_input.1 i hi
    have hb := Vector.ext_iff.mp h_input.2 i hi
    simp only [Vector.getElem_map] at ha hb
    simp [ha, hb]
  · intro _
    trivial

end XorLane
end Solution.KeccakF1600
end
