import Solution.Secp256k1ScalarMul.AddModTheorems

/-!
# Emulated field addition — `AddMod`

`FormalCircuit` computing `c = a + b mod P256` over canonical emulated field
elements.

## Strategy

Witness the reduced sum `r = (a + b) % P256` and the quotient bit
`q = (a + b) / P256` (a single boolean, since `a + b < 2·P256`), then certify

- `q` is boolean (`q · (q − 1) = 0`);
- `r` is normalized (`Normalize`) and canonical (`LessThan` against the
  constant prime limbs);
- `a + b = q · P256 + r` as integers, via `EqViaCarries` on the limb-wise
  coefficient vectors (all coefficients are `< 2^122`, well within the
  `EqViaCarries` bound).

Soundness and completeness are fully proved, with the arithmetic content
factored into `AddModTheorems`.
-/

namespace Solution.Secp256k1ScalarMul
namespace AddMod

/-- Inputs of `AddMod`: the two canonical operands. -/
structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  -- witness r = (a + b) % P256 and the quotient bit q = (a + b) / P256
  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((evalEmu env a + evalEmu env b) % P256)
  let q ← ProvableType.witness (α := field) fun env =>
    (((evalEmu env a + evalEmu env b) / P256 : ℕ) : F circomPrime)

  -- q is boolean
  assertZero (q * (q - 1))

  -- r is normalized and canonical
  Normalize.circuit secpParams r
  LessThan.circuit secpParams { lhs := r, rhs := pConst }

  -- a + b = q·P256 + r as integers, limb-coefficient-wise
  let lhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then q * pConst[k.val]'h + r[k.val]'h else 0
  EqViaCarries.circuit secpParams { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

/-- Preconditions: both operands are canonical emulated field elements. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.a ∧ Fe.Valid input.b

/-- Postcondition: the output is canonical and decodes to the base-field sum. -/
def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧ decodeFe out = decodeFe input.a + decodeFe input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    LessThan.circuit, LessThan.elaborated, LessThan.main,
    LessThan.Assumptions, LessThan.Spec]
  obtain ⟨hq_bool, hr_norm, h_lt_impl, h_eq_impl⟩ := h_holds
  exact soundness_core i₀ env input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 hq_bool hr_norm h_lt_impl h_eq_impl

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
    Normalize.Assumptions, Normalize.Spec,
    EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
    EqViaCarries.Assumptions, EqViaCarries.Spec,
    LessThan.circuit, LessThan.elaborated, LessThan.main,
    LessThan.Assumptions, LessThan.Spec]
  have heva : evalEmu env input_var_a = BigInt.value limbBits input_a := by
    rw [evalEmu, BigInt.value, ← h_input.1]
  have hevb : evalEmu env input_var_b = BigInt.value limbBits input_b := by
    rw [evalEmu, BigInt.value, ← h_input.2]
  rw [heva, hevb] at h_env
  exact completeness_core i₀ env.toEnvironment input_var_a input_var_b input_a input_b
    h_input.1 h_input.2 h_assumptions.1 h_assumptions.2 h_env.1 h_env.2

/-- The `AddMod` formal circuit: `c = a + b mod P256`. -/
def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

theorem evalEmu_stable (x : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env x = eval env' x) :
    evalEmu env x = evalEmu env' x := by
  have hmap :
      x.map (Expression.eval env.toEnvironment) =
        x.map (Expression.eval env'.toEnvironment) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    have hi_eq := congrArg (fun y : Emu (F circomPrime) => y[i]) h
    change (eval env x)[i] = (eval env' x)[i] at hi_eq
    rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
      ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at hi_eq
    exact hi_eq
  simp [evalEmu, hmap]

theorem emuWitnessOutput_stable
    (compute : ProverEnvironment (F circomPrime) → Emu (F circomPrime))
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((ProvableType.witness (α := Emu) compute).output offset) =
      eval env' ((ProvableType.witness (α := Emu) compute).output offset) := by
  apply Vector.ext
  intro i hi
  rw [← ProvableType.getElem_eval_fields_prover (env := env)
      ((ProvableType.witness (α := Emu) compute).output offset) i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env')
      ((ProvableType.witness (α := Emu) compute).output offset) i hi]
  simp only [Circuit.output, ProvableType.witness, ProvableType.varFromOffset_fields,
    Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)

theorem fieldWitnessOutput_stable
    (compute : ProverEnvironment (F circomPrime) → F circomPrime)
    {offset k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset < k) :
    Expression.eval env.toEnvironment
        ((ProvableType.witness (α := field) compute).output offset) =
      Expression.eval env'.toEnvironment
        ((ProvableType.witness (α := field) compute).output offset) := by
  simp [Circuit.output, ProvableType.witness, ProvableType.varFromOffset,
    explicit_provable_type]
  exact h_agree offset hk

theorem assertion_structuralComputableWitnesses_of_condition {Parent Input : TypeMap}
    [CircuitType Parent] [ProvableType Input]
    (circuit : FormalAssertion (F circomPrime) Input) (parentInput : Var Parent (F circomPrime))
    (input : Var Input (F circomPrime)) (n : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)),
      n ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses) :
    ∀ env env',
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' n ((assertion circuit input).operations n) := by
  intro env env'
  rw [Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
  exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
    circuit parentInput input n hinput hcircuit env env'

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  let rCircuit : Circuit (F circomPrime) (Var Emu (F circomPrime)) :=
    ProvableType.witness (α := Emu) fun env =>
      emuOfNat ((evalEmu env input.a + evalEmu env input.b) % P256)
  let r := rCircuit.output offset
  let qOffset := offset + rCircuit.localLength offset
  let qCircuit : Circuit (F circomPrime) (Var field (F circomPrime)) :=
    ProvableType.witness (α := field) fun env =>
      (((evalEmu env input.a + evalEmu env input.b) / P256 : ℕ) : F circomPrime)
  let q := qCircuit.output qOffset
  let boolOffset := qOffset + qCircuit.localLength qOffset
  let normCircuit : Circuit (F circomPrime) Unit :=
    Normalize.circuit secpParams r
  let normOffset := boolOffset + (assertZero (q * (q - 1))).localLength boolOffset
  let ltCircuit : Circuit (F circomPrime) Unit :=
    LessThan.circuit secpParams { lhs := r, rhs := pConst }
  let ltOffset := normOffset + normCircuit.localLength normOffset
  let lhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then input.a[k.val]'h + input.b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then q * pConst[k.val]'h + r[k.val]'h else 0
  have h_r_len : rCircuit.localLength offset = numLimbs := by
    simp [rCircuit, circuit_norm]
  have h_q_len : qCircuit.localLength qOffset = 1 := by
    simp [qCircuit, circuit_norm]
  have h_bool_len : (assertZero (q * (q - 1))).localLength boolOffset = 0 := by
    simp [circuit_norm]
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.provableWitness_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]
  and_intros
  · intro _ h_input
    have ha : evalEmu env input.a = evalEmu env' input.a := by
      apply evalEmu_stable
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
    have hb : evalEmu env input.b = evalEmu env' input.b := by
      apply evalEmu_stable
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
    simp [ha, hb]
  · intro _ h_input
    have ha : evalEmu env input.a = evalEmu env' input.a := by
      apply evalEmu_stable
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) h_input
    have hb : evalEmu env input.b = evalEmu env' input.b := by
      apply evalEmu_stable
      simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) h_input
    simp [ha, hb]
  · trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit secpParams) input r normOffset
      (by
        intro k env env' hle h_agree _h_input
        have hk : offset + numLimbs ≤ k := by
          have hk : offset + numLimbs ≤ k := by
            have hle' := hle
            dsimp [normOffset, boolOffset, qOffset] at hle'
            rw [h_r_len] at hle'
            omega
          exact hk
        have hr := emuWitnessOutput_stable
          (offset := offset) (k := k)
          (fun env => emuOfNat ((evalEmu env input.a + evalEmu env input.b) % P256))
          h_agree hk
        simpa [r, rCircuit] using hr)
      (Normalize.computableWitnesses secpParams) env env'
  · trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
      (LessThan.circuit secpParams) input { lhs := r, rhs := pConst } ltOffset
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm]
        constructor
        · have hk : offset + numLimbs ≤ k := by
            have hbase : offset + numLimbs ≤ ltOffset := by
              dsimp [ltOffset, normOffset, boolOffset, qOffset]
              rw [h_r_len]
              omega
            omega
          have hr := emuWitnessOutput_stable
            (offset := offset) (k := k)
            (fun env => emuOfNat ((evalEmu env input.a + evalEmu env input.b) % P256))
            h_agree hk
          exact eval_mem_of_map_eval_eq (by
            simpa [r, rCircuit] using emu_map_eval_eq_of_eval_eq hr)
        · intro a ha
          rw [pConst, emuConst] at ha
          simp only [Vector.mem_iff_getElem] at ha
          rcases ha with ⟨i, hi, rfl⟩
          rw [Vector.getElem_ofFn hi]
          simp [Expression.eval])
      (LessThan.computableWitnesses secpParams) env env'
  · trivial
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
      (EqViaCarries.circuit secpParams) input { lhs := lhs, rhs := rhs }
      (ltOffset + ltCircuit.localLength ltOffset)
      (by
        intro k env env' hle h_agree h_input
        simp [circuit_norm]
        have h_input_parts :
            (∀ a ∈ input.a, Expression.eval env.toEnvironment a =
                Expression.eval env'.toEnvironment a) ∧
              ∀ a ∈ input.b, Expression.eval env.toEnvironment a =
                Expression.eval env'.toEnvironment a := by
          simpa [circuit_norm, CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using h_input
        constructor
        · have hlhs :
            lhs.map (Expression.eval env.toEnvironment) =
              lhs.map (Expression.eval env'.toEnvironment) := by
            apply Vector.ext
            intro i hi
            simp only [Vector.getElem_map]
            simp only [lhs, Vector.getElem_mapFinRange]
            split
            · have ha : Expression.eval env.toEnvironment input.a[i] =
                  Expression.eval env'.toEnvironment input.a[i] :=
                h_input_parts.1 input.a[i] (by
                  simp only [Vector.mem_iff_getElem]
                  exact ⟨i, by assumption, rfl⟩)
              have hb : Expression.eval env.toEnvironment input.b[i] =
                  Expression.eval env'.toEnvironment input.b[i] :=
                h_input_parts.2 input.b[i] (by
                  simp only [Vector.mem_iff_getElem]
                  exact ⟨i, by assumption, rfl⟩)
              simp [Expression.eval, ha, hb]
            · rfl
          simpa [CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using
              eval_mem_of_map_eval_eq hlhs
        · have hrhs :
            rhs.map (Expression.eval env.toEnvironment) =
              rhs.map (Expression.eval env'.toEnvironment) := by
            apply Vector.ext
            intro i hi
            simp only [Vector.getElem_map]
            simp only [rhs, Vector.getElem_mapFinRange]
            split
            · rename_i hlt
              have hq : Expression.eval env.toEnvironment q =
                  Expression.eval env'.toEnvironment q := by
                exact fieldWitnessOutput_stable
                  (offset := qOffset) (k := k)
                  (fun env => (((evalEmu env input.a + evalEmu env input.b) / P256 : ℕ) :
                    F circomPrime))
                  h_agree (by
                    have hbase : qOffset + 1 ≤ normOffset := by
                      dsimp [normOffset, boolOffset]
                      rw [h_q_len]
                      omega
                    omega)
              have hp : Expression.eval env.toEnvironment pConst[i] =
                  Expression.eval env'.toEnvironment pConst[i] := by
                rw [pConst, emuConst]
                rw [Vector.getElem_ofFn hlt]
                simp [Expression.eval]
              have hr : Expression.eval env.toEnvironment r[i] =
                  Expression.eval env'.toEnvironment r[i] := by
                have hr_vec := emuWitnessOutput_stable
                  (offset := offset) (k := k)
                  (fun env => emuOfNat ((evalEmu env input.a + evalEmu env input.b) % P256))
                  h_agree (by
                    have hbase : offset + numLimbs ≤ normOffset := by
                      dsimp [normOffset, boolOffset, qOffset]
                      rw [h_r_len]
                      omega
                    have hnorm_le_k : normOffset ≤ k := by
                      have hle' := hle
                      dsimp [ltOffset] at hle'
                      omega
                    omega)
                have hr_i : (eval env r)[i] = (eval env' r)[i] := by
                  exact congrArg (fun x : Emu (F circomPrime) => x[i]) (by
                    simpa [r, rCircuit] using hr_vec)
                rw [← ProvableType.getElem_eval_fields_prover (env := env) r i hlt,
                  ← ProvableType.getElem_eval_fields_prover (env := env') r i hlt] at hr_i
                exact hr_i
              simp [Expression.eval, hq, hp, hr]
            · rfl
          simpa [CircuitType.eval_expression_prover_to_verifier,
            CircuitType.eval_expression, ProvableType.eval, explicit_provable_type] using
              eval_mem_of_map_eval_eq hrhs)
      (EqViaCarries.computableWitnesses secpParams) env env'
  · trivial
  · trivial

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

/-- The output of `AddMod.main` is the reduced-sum witness `r`, allocated first at
`offset` and reading only the `numLimbs` cells `[offset, offset + numLimbs)`.
Environments agreeing below any `k ≥ offset + numLimbs` evaluate the output
identically. Consumed by `CompleteAdd`, which feeds these limbs into later
subcircuits. -/
lemma eval_output_of_agreesBelow (input : Var Inputs (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + numLimbs ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  have hout : (main input).output offset
      = (ProvableType.witness (α := Emu) fun env =>
          emuOfNat ((evalEmu env input.a + evalEmu env input.b) % P256)).output offset := rfl
  rw [hout]
  exact emuWitnessOutput_stable _ h_agree hk

end AddMod
end Solution.Secp256k1ScalarMul
