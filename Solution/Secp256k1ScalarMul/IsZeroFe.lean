import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.IsZeroFeTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Clean.Gadgets.IsZeroField

/-!
# Emulated field zero test — `IsZeroFe`

`FormalCircuit` computing the boolean flag `z = 1 ↔ x = 0` for a canonical
emulated field element.

## Strategy

A canonical element is zero iff every limb is zero (`BigInt.value_inj`), so
the flag is the product of the four per-limb `IsZeroField` flags. The two
products are witnessed (one rank-1 row each) to keep the result affine.

Soundness and completeness are fully proved, with the pure limb/decoding
facts factored into `IsZeroFeTheorems.lean`.
-/

namespace Solution.Secp256k1ScalarMul
namespace IsZeroFe

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let z0 ← subcircuit Gadgets.IsZeroField.circuit x[0]
  let z1 ← subcircuit Gadgets.IsZeroField.circuit x[1]
  let z2 ← subcircuit Gadgets.IsZeroField.circuit x[2]
  let z3 ← subcircuit Gadgets.IsZeroField.circuit x[3]
  let t01 <== z0 * z1
  let t23 <== z2 * z3
  let z <== t01 * t23
  return z

instance elaborated : ElaboratedCircuit (F circomPrime) Emu field main := by
  elaborate_circuit

/-- Precondition: the input is a canonical emulated field element. -/
def Assumptions (x : Emu (F circomPrime)) : Prop :=
  Fe.Valid x

/-- Postcondition: the output is the boolean zero flag of the decoded value. -/
def Spec (x : Emu (F circomPrime)) (out : F circomPrime) : Prop :=
  out = if decodeFe x = 0 then 1 else 0

theorem soundness :
    Soundness (Input := Emu) (Output := field) (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  obtain ⟨hz0, hz1, hz2, hz3, ht01, ht23, hz⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 4), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hz0
  rw [hx 1 (by omega)] at hz1
  rw [hx 2 (by omega)] at hz2
  rw [hx 3 (by omega)] at hz3
  rw [hz, ht01, ht23, hz0, hz1, hz2, hz3]
  simp only [decodeFe_eq_zero_iff h_assumptions]
  by_cases h0 : input[0] = 0 <;> by_cases h1 : input[1] = 0 <;>
    by_cases h2 : input[2] = 0 <;> by_cases h3 : input[3] = 0 <;>
    simp [h0, h1, h2, h3]

theorem completeness :
    Completeness (Input := Emu) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start [Gadgets.IsZeroField.circuit, Gadgets.IsZeroField.Assumptions,
    Gadgets.IsZeroField.Spec]
  obtain ⟨-, -, -, -, ht01, ht23, hz⟩ := h_env
  exact ⟨ht01, ht23, hz⟩

/-- The `IsZeroFe` formal circuit: boolean zero flag of a canonical element. -/
def circuit : FormalCircuit (F circomPrime) Emu field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

private theorem equalityComputableWitnesses (M : TypeMap) [ProvableType M] :
    (Gadgets.Equality.circuit (F := F circomPrime) M).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((Gadgets.Equality.circuit (F := F circomPrime) M).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold Gadgets.Equality.circuit Gadgets.Equality.main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff]
  intro _
  trivial

private lemma witnessField_localLength_one
    (compute : ProverEnvironment (F circomPrime) → F circomPrime) (offset : ℕ) :
    (witnessField compute).localLength offset = 1 := by
  unfold Circuit.witnessField
  change ((var <$> witnessVar compute).localLength offset) = 1
  rw [Circuit.map_localLength_eq]
  simp [Circuit.witnessVar, Circuit.localLength, Operations.localLength]

private def xInvCompute (input : Expression (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : F circomPrime :=
  if Expression.eval env.toEnvironment input = 0 then 0
  else (Expression.eval env.toEnvironment input)⁻¹

private def xInvCircuit (input : Expression (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) :=
  witnessField (xInvCompute input)

private def isZeroFieldMain (input : Expression (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let xInv ← xInvCircuit input
  let isZero <== 1 - input * xInv
  isZero * input === 0
  return isZero

private lemma xInvCircuit_localLength_one
    (input : Expression (F circomPrime)) (offset : ℕ) :
    (xInvCircuit input).localLength offset = 1 := by
  exact witnessField_localLength_one (xInvCompute input) offset

private theorem assignEqField_structuralComputableWitnesses_of_condition
    {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (rhs : Expression (F circomPrime)) (offset : ℕ)
    (hrhs : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)),
      offset ≤ k → env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput →
      Expression.eval env.toEnvironment rhs = Expression.eval env'.toEnvironment rhs) :
    ∀ env env',
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' offset ((HasAssignEq.assignEq rhs).operations offset) := by
  intro env env'
  unfold HasAssignEq.assignEq instHasAssignEqExpression
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  constructor
  · intro h_agree h_parent
    exact hrhs offset env env' (Nat.le_refl offset) h_agree h_parent
  · constructor
    · apply Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
      · intro k env env' hk h_agree h_parent
        have hlen :
            (witnessField fun env : ProverEnvironment (F circomPrime) =>
              Expression.eval env.toEnvironment rhs).localLength offset = 1 :=
          witnessField_localLength_one _ offset
        rw [show eval env (((witnessField fun env => Expression.eval env.toEnvironment rhs).output offset, rhs) :
              ProvablePair field field (Expression (F circomPrime))) =
              (eval env ((witnessField fun env => Expression.eval env.toEnvironment rhs).output offset),
                eval env rhs) by
            exact CircuitType.eval_var_pair_prover (M := field) (N := field) env _ _,
          show eval env' (((witnessField fun env => Expression.eval env.toEnvironment rhs).output offset, rhs) :
              ProvablePair field field (Expression (F circomPrime))) =
              (eval env' ((witnessField fun env => Expression.eval env.toEnvironment rhs).output offset),
                eval env' rhs) by
            exact CircuitType.eval_var_pair_prover (M := field) (N := field) env' _ _]
        apply Prod.ext
        · simp only
          rw [CircuitType.eval_expression_prover_to_verifier (M := field),
            CircuitType.eval_expression_prover_to_verifier (M := field)]
          rw [CircuitType.eval_var_field, CircuitType.eval_var_field]
          simp [Circuit.witnessField, Circuit.witnessVar, Circuit.output, Expression.eval]
          exact h_agree offset (by omega)
        · simp only
          rw [CircuitType.eval_expression_prover_to_verifier (M := field),
            CircuitType.eval_expression_prover_to_verifier (M := field)]
          rw [CircuitType.eval_var_field, CircuitType.eval_var_field]
          exact hrhs k env env' (by omega) h_agree h_parent
      · exact equalityComputableWitnesses id
    · trivial

private lemma expression_stable_of_field_eval_eq
    {env env' : ProverEnvironment (F circomPrime)}
    {x : Expression (F circomPrime)}
    (h : eval env x = eval env' x) :
    Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := field),
    CircuitType.eval_expression_prover_to_verifier (M := field)] at h
  rw [CircuitType.eval_var_field, CircuitType.eval_var_field] at h
  exact h

private lemma xInvCompute_stable
    {env env' : ProverEnvironment (F circomPrime)}
    {input : Expression (F circomPrime)}
    (h : eval env input = eval env' input) :
    xInvCompute input env = xInvCompute input env' := by
  have hx := expression_stable_of_field_eval_eq h
  simp [xInvCompute, hx]

private lemma xInv_output_stable
    (input : Expression (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset < k) :
    Expression.eval env.toEnvironment ((xInvCircuit input).output offset) =
      Expression.eval env'.toEnvironment ((xInvCircuit input).output offset) := by
  simp [xInvCircuit, Circuit.witnessField, Circuit.output]
  exact h_agree offset hk

private theorem equalityFieldPair_flatStructural_of_condition
    {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (lhs rhs : Expression (F circomPrime)) (offset : ℕ)
    (hinput : ∀ (k : ℕ) (env env' : ProverEnvironment (F circomPrime)),
      offset ≤ k →
      env.AgreesBelow k env' →
      eval env parentInput = eval env' parentInput →
      eval env ((lhs, rhs) : ProvablePair field field (Expression (F circomPrime))) =
        eval env' ((lhs, rhs) : ProvablePair field field (Expression (F circomPrime)))) :
    ∀ env env',
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' offset
        ((Gadgets.Equality.circuit (F := F circomPrime) id).toSubcircuit offset
          ((lhs, rhs) : ProvablePair field field (Expression (F circomPrime)))).ops.toFlat := by
  exact @Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.subcircuit_flatStructuralComputableWitnesses_of_condition
    (F circomPrime) _ Parent (ProvablePair field field) _ _
    (Gadgets.Equality.circuit (F := F circomPrime) id) parentInput
    ((lhs, rhs) : ProvablePair field field (Expression (F circomPrime)))
    offset hinput (equalityComputableWitnesses id)

private theorem toFlat_append (a b : Operations (F circomPrime)) :
    (a ++ b).toFlat = a.toFlat ++ b.toFlat := by
  induction a using Operations.induct with
  | empty => simp [Operations.toFlat]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | interact _ _ ih =>
    simp [Operations.toFlat, ih]
  | subcircuit s _ ih => simp [Operations.toFlat, ih, List.append_assoc]

private theorem toFlat_flatten (L : List (Operations (F circomPrime))) :
    Operations.toFlat L.flatten = (L.map Operations.toFlat).flatten := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatten_cons, toFlat_append, ih, List.map_cons, List.flatten_cons]

/-- Any flat operation list free of witnesses trivially satisfies the flat
structural computable-witness condition, at any offset (assertions, lookups, and
interactions carry no witness obligation and leave the offset untouched). -/
private theorem flatStructural_of_no_witness
    {Parent : TypeMap} [CircuitType Parent]
    (parentInput : Var Parent (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime)) :
    ∀ (ops : List (FlatOperation (F circomPrime))) (offset : ℕ),
      (∀ x ∈ ops, match x with | .witness _ _ => False | _ => True) →
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' offset ops := by
  intro ops
  induction ops with
  | nil => intro offset _; trivial
  | cons x rest ih =>
    intro offset h
    have h_rest : ∀ y ∈ rest, match y with | .witness _ _ => False | _ => True :=
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases x with
    | witness m c => exact absurd (h _ (List.mem_cons_self ..)) (by simp)
    | assert e =>
      exact ih offset h_rest
    | lookup l =>
      exact ih offset h_rest
    | interact i =>
      exact ih offset h_rest

/-- The flattened operations of the `Equality` assertion carry no witnesses (its
`main` is a `forEach` of `assertZero`s), so its flat structural condition holds
at any pair of offsets. -/
private theorem equalityFieldSubcircuit_flatStructural_any
    {Parent : TypeMap} [CircuitType Parent] {M : TypeMap} [ProvableType M]
    (parentInput : Var Parent (F circomPrime))
    (pair : ProvablePair M M (Expression (F circomPrime)))
    (subOffset structuralOffset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
        parentInput env env' structuralOffset
        ((Gadgets.Equality.circuit (F := F circomPrime) M).toSubcircuit subOffset pair).ops.toFlat := by
  apply flatStructural_of_no_witness
  unfold FormalAssertion.toSubcircuit Gadgets.Equality.circuit
  rw [Operations.toNested_toFlat]
  rcases pair with ⟨lhs, rhs⟩
  simp only [Gadgets.Equality.main]
  intro x hx
  rw [Circuit.forEach.operations_eq, toFlat_flatten, List.map_ofFn, List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  simp only [Function.comp, Circuit.assertZero, circuit_norm, Operations.toFlat,
    List.mem_cons, List.not_mem_nil, or_false] at hxl
  subst hxl
  trivial

private theorem isZeroFieldComputableWitnesses :
    (Gadgets.IsZeroField.circuit (F := F circomPrime)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    (((Gadgets.IsZeroField.circuit (F := F circomPrime)).main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  change
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' offset ((isZeroFieldMain input).operations offset)
  unfold isZeroFieldMain
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    apply Vector.ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using xInvCompute_stable h_input
  · trivial
  · intro h_agree h_input
    apply Vector.ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    have hx := expression_stable_of_field_eval_eq h_input
    have hxInvRaw : Expression.eval env.toEnvironment
          (((witnessField fun env : ProverEnvironment (F circomPrime) =>
            if Expression.eval env.toEnvironment input = 0 then 0
            else (Expression.eval env.toEnvironment input)⁻¹) :
              Circuit (F circomPrime) (Expression (F circomPrime))).output offset) =
        Expression.eval env'.toEnvironment
          (((witnessField fun env : ProverEnvironment (F circomPrime) =>
            if Expression.eval env.toEnvironment input = 0 then 0
            else (Expression.eval env.toEnvironment input)⁻¹) :
              Circuit (F circomPrime) (Expression (F circomPrime))).output offset) := by
      simp [Circuit.witnessField, Circuit.output]
      apply h_agree
      change offset < offset + 1
      omega
    have hscalar :
        1 + -1 * (Expression.eval env.toEnvironment input *
            Expression.eval env.toEnvironment
              (((witnessField fun env : ProverEnvironment (F circomPrime) =>
                if Expression.eval env.toEnvironment input = 0 then 0
                else (Expression.eval env.toEnvironment input)⁻¹) :
                  Circuit (F circomPrime) (Expression (F circomPrime))).output offset)) =
          1 + -1 * (Expression.eval env'.toEnvironment input *
            Expression.eval env'.toEnvironment
              (((witnessField fun env : ProverEnvironment (F circomPrime) =>
                if Expression.eval env.toEnvironment input = 0 then 0
                else (Expression.eval env.toEnvironment input)⁻¹) :
                  Circuit (F circomPrime) (Expression (F circomPrime))).output offset)) := by
      rw [hx, hxInvRaw]
    change
      1 + -1 * (Expression.eval env.toEnvironment input *
        Expression.eval env.toEnvironment
          (((witnessField fun env : ProverEnvironment (F circomPrime) =>
            if Expression.eval env.toEnvironment input = 0 then 0
            else (Expression.eval env.toEnvironment input)⁻¹) :
              Circuit (F circomPrime) (Expression (F circomPrime))).output offset)) =
      1 + -1 * (Expression.eval env'.toEnvironment input *
        Expression.eval env'.toEnvironment
          (((witnessField fun env : ProverEnvironment (F circomPrime) =>
            if Expression.eval env.toEnvironment input = 0 then 0
            else (Expression.eval env.toEnvironment input)⁻¹) :
              Circuit (F circomPrime) (Expression (F circomPrime))).output offset))
    exact hscalar
  ·
    exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
  · trivial
  ·
    exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
  · trivial

/-- The `IsZeroField` subcircuit's output is its second witness cell (offset `+1`);
its value only depends on `env` below `base + 2`, so it is stable across
environments agreeing below any `k > base + 1`. -/
private lemma isZeroField_output_eval_stable (x : Expression (F circomPrime)) {base k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base + 1 < k) :
    Expression.eval env.toEnvironment ((subcircuit Gadgets.IsZeroField.circuit x).output base) =
      Expression.eval env'.toEnvironment ((subcircuit Gadgets.IsZeroField.circuit x).output base) := by
  simp only [circuit_norm, Gadgets.IsZeroField.circuit]
  exact h_agree (base + 1) hk

/-- The output of `let w <== r` is its fresh witness cell (offset `base`); its
value only depends on `env` below `base + 1`, so it is stable across environments
agreeing below any `k > base`. -/
private lemma assignEq_output_eval_stable (r : Var field (F circomPrime)) {base k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : base < k) :
    Expression.eval env.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) =
      Expression.eval env'.toEnvironment
        ((HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).output base) := by
  simp only [circuit_norm, HasAssignEq.assignEq]
  exact h_agree base hk

/-- A limb of a canonical input is stable whenever the whole input value is. -/
private lemma input_limb_stable {input : Var Emu (F circomPrime)} {k : ℕ} (hk : k < numLimbs)
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env input = eval env' input) :
    eval env input[k] = eval env' input[k] := by
  have hmap := emu_map_eval_eq_of_eval_eq h
  have hget : (input.map (Expression.eval env.toEnvironment))[k] =
      (input.map (Expression.eval env'.toEnvironment))[k] := by rw [hmap]
  simp only [Vector.getElem_map] at hget
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  exact hget

theorem computableWitnesses : circuit.base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hL : ∀ (y : Expression (F circomPrime)) (o : ℕ),
      (subcircuit Gadgets.IsZeroField.circuit y).localLength o = 2 := by
    intro y o
    simp only [circuit_norm, Gadgets.IsZeroField.circuit]
  have hA : ∀ (r : Var field (F circomPrime)) (o : ℕ),
      (HasAssignEq.assignEq (β := field (Expression (F circomPrime))) r).localLength o = 1 := by
    intro r o
    simp only [circuit_norm, HasAssignEq.assignEq]
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    hL, hA, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- four `IsZeroField` subcircuits, each on a direct input limb
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[0] offset
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[1] (offset + 2)
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[2] (offset + 2 + 2)
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[3] (offset + 2 + 2 + 2)
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  -- `t01 <== z0 * z1`: witness reads the two prior `IsZeroField` output flags
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      refine congrArg toElements ?_
      have h0 := isZeroField_output_eval_stable (base := offset) input[0] h_agree (by omega)
      have h1 := isZeroField_output_eval_stable (base := offset + 2) input[1] h_agree (by omega)
      simp only [CircuitType.eval_var_field_prover, Expression.eval, h0, h1]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial
  -- `t23 <== z2 * z3`
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      refine congrArg toElements ?_
      have h2 := isZeroField_output_eval_stable (base := offset + 2 + 2) input[2] h_agree (by omega)
      have h3 := isZeroField_output_eval_stable (base := offset + 2 + 2 + 2) input[3] h_agree (by omega)
      simp only [CircuitType.eval_var_field_prover, Expression.eval, h2, h3]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial
  -- `z <== t01 * t23`: witness reads the two prior assignment cells
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      refine congrArg toElements ?_
      have h01 := assignEq_output_eval_stable
        ((subcircuit Gadgets.IsZeroField.circuit input[0]).output offset *
          (subcircuit Gadgets.IsZeroField.circuit input[1]).output (offset + 2))
        (base := offset + 2 + 2 + 2 + 2) h_agree (by omega)
      have h23 := assignEq_output_eval_stable
        ((subcircuit Gadgets.IsZeroField.circuit input[2]).output (offset + 2 + 2) *
          (subcircuit Gadgets.IsZeroField.circuit input[3]).output (offset + 2 + 2 + 2))
        (base := offset + 2 + 2 + 2 + 2 + 1) h_agree (by omega)
      simp only [CircuitType.eval_var_field_prover, Expression.eval, h01, h23]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

/-- The output of `IsZeroFe.main` is the final witnessed flag (offset `+10`); it
only depends on `env` below `offset + 11`, so it is stable across environments
agreeing below any `k ≥ offset + 11`. -/
lemma eval_output_of_agreesBelow (x : Var Emu (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 11 ≤ k) :
    eval env ((main x).output offset) = eval env' ((main x).output offset) := by
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  simp only [main, circuit_norm, Gadgets.IsZeroField.circuit]
  exact h_agree (offset + 10) (by omega)

end IsZeroFe
end Solution.Secp256k1ScalarMul
