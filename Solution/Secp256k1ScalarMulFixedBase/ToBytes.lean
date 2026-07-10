import Solution.Secp256k1ScalarMulFixedBase.Params
import Solution.Secp256k1ScalarMulFixedBase.ToBytesTheorems
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Byte decomposition of an emulated field element — `ToBytes`

`FormalCircuit` decomposing an emulated field element (4×64-bit limbs) into
its 32 bytes, little-endian (byte `i` holds bits `[8·i, 8·i + 8)`).

## Strategy

Witness the 32 bytes, range-check each to 8 bits
(`Gadgets.ToBits.rangeCheck`), and assert the affine per-limb recomposition

  `limb_k = Σ_{t < 8} byte_{8·k + t} · 2^(8·t)`

(no cross-limb carries, since the limbs are byte-aligned; each equation's
sides are `< 2^64 ≪ circomPrime`, so there is no field wraparound). The
byte range checks make the decomposition unique, and together with the
recomposition they subsume the limb range check.

The output bytes are fresh witness variables — affine, degree 1 — so they
can be exposed directly as circuit outputs.

Soundness and completeness are fully proved, with the arithmetic content
factored into `ToBytesTheorems` (`soundness_core`, `completeness_core`).
-/

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ToBytes

/-- Little-endian byte `i` of a natural number. -/
def byteOfNat (v i : ℕ) : ℕ := v / 2 ^ (8 * i) % 256

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields coordBytes) (F circomPrime)) := do
  -- witness the 32 little-endian bytes of the value
  let bytes ← ProvableType.witness (α := fields coordBytes) fun env =>
    Vector.ofFn fun i : Fin coordBytes =>
      ((byteOfNat (evalEmu env x) i.val : ℕ) : F circomPrime)

  -- each byte is 8 bits
  Circuit.forEach bytes (fun b => Gadgets.ToBits.rangeCheck 8 (by decide) b)

  -- per-limb affine recomposition: limb_k = Σ_{t<8} byte_{8k+t} · 2^(8t)
  let constraints := Vector.ofFn fun k : Fin numLimbs =>
    (Fin.foldl bytesPerLimb (fun acc t =>
      acc + bytes[bytesPerLimb * k.val + t.val]'(by
          have hk := k.isLt; have ht := t.isLt
          simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
          omega)
        * (((2 ^ (8 * t.val) : ℕ) : F circomPrime) : Expression (F circomPrime)))
      0)
    - x[k.val]'k.isLt
  Circuit.forEach constraints assertZero

  return bytes

instance elaborated : ElaboratedCircuit (F circomPrime) Emu (fields coordBytes) main := by
  elaborate_circuit

/-- Precondition: the input is a normalized emulated field element. -/
def Assumptions (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits

/-- Postcondition: the outputs are bytes and recompose (little-endian) to the
value of the input. -/
def Spec (x : Emu (F circomPrime)) (out : fields coordBytes (F circomPrime)) : Prop :=
  (∀ i : Fin coordBytes, (out[i]).val < 256) ∧
    Limbs.fromLimbs 8 (out.toList.map ZMod.val) = x.value limbBits

theorem soundness :
    Soundness (Input := Emu) (Output := fields coordBytes) (F circomPrime)
      main Assumptions Spec := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck]
  obtain ⟨h_bytes, h_rows⟩ := h_holds
  refine ⟨fun i => lt_of_lt_of_eq (h_bytes i) (by norm_num), ?_⟩
  apply soundness_core env i₀ input h_bytes
  intro k
  have h := h_rows k
  simp only [Vector.getElem_ofFn] at h
  rw [eval_row_iff] at h
  rw [← h_input, Vector.getElem_map]
  exact h

theorem completeness :
    Completeness (Input := Emu) (Output := fields coordBytes) (F circomPrime)
      main Assumptions := by
  circuit_proof_start [Gadgets.ToBits.rangeCheck]
  obtain ⟨h_wit, -⟩ := h_env
  -- the witnessed value is the input's value
  have hv : evalEmu env input_var = BigInt.value limbBits input := by
    rw [evalEmu, h_input]
    rfl
  -- each witnessed byte is the corresponding byte of the input's value
  have hbyte : ∀ i : Fin coordBytes,
      env.get (i₀ + i.val)
        = ((byteOfNat (BigInt.value limbBits input) i.val : ℕ) : F circomPrime) := by
    intro i
    rw [h_wit i]
    simp only [Vector.getElem_ofFn, hv]
  -- a byte value is < 2^8
  have hbyte_lt : ∀ v j : ℕ, byteOfNat v j < 2 ^ 8 :=
    fun v j => Nat.mod_lt _ (by norm_num)
  refine ⟨fun i => ?_, fun k => ?_⟩
  · -- range checks: the witnessed bytes are 8-bit
    rw [hbyte i, ZMod.val_natCast_of_lt (lt_trans (hbyte_lt _ _)
      (lt_trans (by norm_num) two_pow_64_lt_circomPrime))]
    exact hbyte_lt _ _
  · -- recomposition rows
    simp only [Vector.getElem_ofFn]
    rw [eval_row_iff]
    have hx : Expression.eval env.toEnvironment (input_var[k.val]'k.isLt)
        = input[k.val]'k.isLt := by
      rw [← h_input, Vector.getElem_map]
    rw [hx]
    show (∑ t : Fin bytesPerLimb,
        env.get (i₀ + (bytesPerLimb * k.val + t.val))
          * ((2 ^ (8 * t.val) : ℕ) : F circomPrime))
      = input[k.val]'k.isLt
    apply completeness_core input h_assumptions k
    intro t
    have hidx : bytesPerLimb * k.val + t.val < coordBytes := by
      have hk := k.isLt
      have ht := t.isLt
      simp only [numLimbs, bytesPerLimb, coordBytes] at hk ht ⊢
      omega
    rw [hbyte ⟨bytesPerLimb * k.val + t.val, hidx⟩]
    simp only [byteOfNat]

/-- The `ToBytes` formal circuit: little-endian byte decomposition of an
emulated field element. -/
def circuit : FormalCircuit (F circomPrime) Emu (fields coordBytes) where
  main; elaborated; Assumptions; Spec; soundness; completeness

open Challenge.Utils.ComputableWitnessLemmas in
/-- The Clean library `toBits n hn` circuit has computable witnesses: its sole
witness `witnessVector n (fun env => fieldToBits n (x.eval env))` reads only the
gadget input `x`; the boolean and recomposition constraints are assertions. -/
private theorem toBits_computableWitnesses (n : ℕ) (hn : 2 ^ n < circomPrime) :
    (Gadgets.ToBits.toBits (p := circomPrime) n hn).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((Gadgets.ToBits.main n input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold Gadgets.ToBits.main
  simp only [
    HasAssertEq.assert_eq, Expression.assertEquals,
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessVector_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    and_true]
  refine ⟨?_, ?_, ?_⟩
  · intro _ h_input
    simp only [circuit_norm] at h_input
    rw [h_input]
  · intro i
    rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll]
    simp only [circuit_norm, FlatOperation.forAll,
      FormalCircuitBase.computableWitnessCondition, and_true]
  · rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll,
      Operations.forAll_toFlat_iff]
    simp only [Gadgets.Equality.main, Operations.forAllFlat, circuit_norm,
      FormalCircuitBase.computableWitnessCondition]

open Challenge.Utils.ComputableWitnessLemmas in
/-- The Clean library range-check assertion `rangeCheck n hn` has computable
witnesses. Its `main` is `do let _ ← toBits n hn x`, so the only witnesses are
those of the `toBits` subcircuit, discharged by `toBits_computableWitnesses`. -/
private theorem rangeCheck_computableWitnesses (n : ℕ) (hn : 2 ^ n < circomPrime) :
    (Gadgets.ToBits.rangeCheck (p := circomPrime) n hn).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    (((Gadgets.ToBits.rangeCheck n hn).main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  show FormalCircuitBase.Operations.StructuralComputableWitnesses input env env' offset
    (((Gadgets.ToBits.rangeCheck n hn).main input).operations offset)
  unfold Gadgets.ToBits.rangeCheck
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff, and_true]
  show FormalCircuitBase.Operations.StructuralComputableWitnesses input env env' offset
    [.subcircuit ((Gadgets.toBits n hn).toSubcircuit offset input)]
  simp only [FormalCircuitBase.Operations.StructuralComputableWitnesses, and_true]
  rw [FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll]
  unfold GeneralFormalCircuit.toSubcircuit GeneralFormalCircuit.WithHint.toSubcircuit
  rw [Operations.toNested_toFlat, Operations.forAll_toFlat_iff]
  exact toBits_computableWitnesses n hn offset input env env'

open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.provableWitness_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    and_true, implies_true]
  refine ⟨?_, ?_⟩
  · -- the 32 witnessed bytes read only the input value
    intro _ h_input
    have hev : evalEmu env input = evalEmu env' input := evalEmu_eq_of_eval_eq h_input
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, hev]
  · -- forEach rangeCheck: each byte input is a previously-allocated witness cell
    intro i
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Gadgets.ToBits.rangeCheck 8 (by decide)) input _ _ ?_
      (rangeCheck_computableWitnesses 8 (by decide)) env env'
    intro k e1 e2 hle h_agree _
    have hk : offset + coordBytes ≤ k := by
      simp only [circuit_norm, Gadgets.ToBits.rangeCheck, coordBytes] at hle ⊢
      omega
    have hmem := eval_mem_varFromOffset_fields_of_agreesBelow h_agree hk
    rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
    exact hmem _ (Vector.getElem_mem i.isLt)

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

open Challenge.Utils.ComputableWitnessLemmas in
/-- The output of `ToBytes.main` is its first `coordBytes` witness cells (offsets
`[offset, offset + coordBytes)`), so it is stable across environments agreeing
below any `k ≥ offset + circuit.localLength offset`. Consumed by `ScalarMul`,
which feeds these bytes into `Mux`. -/
lemma eval_output_of_agreesBelow (x : Var Emu (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + circuit.localLength x ≤ k) :
    eval env ((main x).output offset) = eval env' ((main x).output offset) := by
  have hk32 : offset + coordBytes ≤ k := by
    have hcl : circuit.localLength x = coordBytes + coordBytes * 8 := by
      simp only [circuit, circuit_norm]
    rw [hcl] at hk
    omega
  have hout : (main x).output offset
      = varFromOffset (fields coordBytes) offset := rfl
  rw [hout, CircuitType.eval_var_fields_prover, CircuitType.eval_var_fields_prover]
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map, Vector.getElem_map]
  exact eval_mem_varFromOffset_fields_of_agreesBelow h_agree hk32 _
    (Vector.getElem_mem hi)

end ToBytes
end Solution.Secp256k1ScalarMulFixedBase
