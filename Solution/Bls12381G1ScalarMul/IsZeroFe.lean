import Solution.Bls12381G1ScalarMul.Params
import Solution.Bls12381G1ScalarMul.IsZeroFeTheorems
import Challenge.Utils.ComputableWitnessLemmas
import Clean.Gadgets.IsZeroField

/-!
# Emulated field zero test — `IsZeroFe`

`FormalCircuit` computing the boolean flag `z = 1 ↔ x = 0` for a canonical
emulated field element.

## Strategy

A canonical element is zero iff every limb is zero (`BigInt.value_inj`), so
the flag is the product of the per-limb `IsZeroField` flags, combined by a
balanced tree of witnessed products (one rank-1 row each) to keep the result
affine.

Soundness and completeness are fully proved, with the pure limb/decoding
facts factored into `IsZeroFeTheorems.lean`.
-/

namespace Solution.Bls12381G1ScalarMul
namespace IsZeroFe

def main (x : Var Emu (F circomPrime)) :
    Circuit (F circomPrime) (Expression (F circomPrime)) := do
  let z0 ← subcircuit Gadgets.IsZeroField.circuit x[0]
  let z1 ← subcircuit Gadgets.IsZeroField.circuit x[1]
  let z2 ← subcircuit Gadgets.IsZeroField.circuit x[2]
  let z3 ← subcircuit Gadgets.IsZeroField.circuit x[3]
  let z4 ← subcircuit Gadgets.IsZeroField.circuit x[4]
  let z5 ← subcircuit Gadgets.IsZeroField.circuit x[5]
  let t01 <== z0 * z1
  let t23 <== z2 * z3
  let t45 <== z4 * z5
  let t0123 <== t01 * t23
  let z <== t0123 * t45
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
  circuit_proof_start [Gadgets.IsZeroField.circuit]
  obtain ⟨hz0, hz1, hz2, hz3, hz4, hz5, ht01, ht23, ht45, ht0123, hz⟩ := h_holds
  have hx : ∀ (i : ℕ) (hi : i < 6), Expression.eval env input_var[i] = input[i] := by
    intro i hi
    rw [← h_input, Vector.getElem_map]
  rw [hx 0 (by omega)] at hz0
  rw [hx 1 (by omega)] at hz1
  rw [hx 2 (by omega)] at hz2
  rw [hx 3 (by omega)] at hz3
  rw [hx 4 (by omega)] at hz4
  rw [hx 5 (by omega)] at hz5
  rw [hz, ht0123, ht01, ht23, ht45, hz0, hz1, hz2, hz3, hz4, hz5]
  simp only [decodeFe_eq_zero_iff h_assumptions]
  by_cases h0 : input[0] = 0 <;> by_cases h1 : input[1] = 0 <;>
    by_cases h2 : input[2] = 0 <;> by_cases h3 : input[3] = 0 <;>
    by_cases h4 : input[4] = 0 <;> by_cases h5 : input[5] = 0 <;>
    simp [h0, h1, h2, h3, h4, h5]

theorem completeness :
    Completeness (Input := Emu) (Output := field) (F circomPrime) main Assumptions := by
  circuit_proof_start [Gadgets.IsZeroField.circuit]
  obtain ⟨-, -, -, -, -, -, ht01, ht23, ht45, ht0123, hz⟩ := h_env
  exact ⟨ht01 0, ht23 0, ht45 0, ht0123 0, hz 0⟩

/-- The `IsZeroFe` formal circuit: boolean zero flag of a canonical element. -/
def circuit : FormalCircuit (F circomPrime) Emu field where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

private lemma expression_stable_of_field_eval_eq
    {env env' : ProverEnvironment (F circomPrime)}
    {x : Expression (F circomPrime)}
    (h : eval env x = eval env' x) :
    Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := field),
    CircuitType.eval_expression_prover_to_verifier (M := field)] at h
  rw [CircuitType.eval_var_field, CircuitType.eval_var_field] at h
  exact h

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
  simp only [Gadgets.IsZeroField.circuit, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the inverse witness reads only the gadget input
    intro _ h_input
    -- `simp only` (not `rw`): the `Decidable` instance in the witness generator's
    -- `if` mentions the evaluated input, so `rw`'s motive does not typecheck; the
    -- trailing `congr` discharges the leftover instance mismatch
    simp only [h_input]
    congr 5
  · -- the flag witness reads the input and the inverse cell allocated just below
    intro h_agree h_input
    rw [h_input, h_agree offset (by omega)]
  · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
  · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'

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
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    hL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- six `IsZeroField` subcircuits, each on a direct input limb
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
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[4] (offset + 2 + 2 + 2 + 2)
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  · exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Gadgets.IsZeroField.circuit input input[5] (offset + 2 + 2 + 2 + 2 + 2)
      (fun _ _ h => input_limb_stable (by decide) h) isZeroFieldComputableWitnesses env env'
  -- `t01 <== z0 * z1`: witness reads the two prior `IsZeroField` output flags
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      simp only [Witgen.WitgenIR.eval_ofExprs_toElements]
      refine congrArg toElements ?_
      have h0 := isZeroField_output_eval_stable (base := offset) input[0] h_agree (by omega)
      have h1 := isZeroField_output_eval_stable (base := offset + 2) input[1] h_agree (by omega)
      simp only [CircuitType.eval_var_field, Expression.eval, h0, h1]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial
  -- `t23 <== z2 * z3`
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      simp only [Witgen.WitgenIR.eval_ofExprs_toElements]
      refine congrArg toElements ?_
      have h2 := isZeroField_output_eval_stable (base := offset + 2 + 2) input[2] h_agree (by omega)
      have h3 := isZeroField_output_eval_stable (base := offset + 2 + 2 + 2) input[3] h_agree (by omega)
      simp only [CircuitType.eval_var_field, Expression.eval, h2, h3]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial
  -- `t45 <== z4 * z5`
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      simp only [Witgen.WitgenIR.eval_ofExprs_toElements]
      refine congrArg toElements ?_
      have h4 := isZeroField_output_eval_stable
        (base := offset + 2 + 2 + 2 + 2) input[4] h_agree (by omega)
      have h5 := isZeroField_output_eval_stable
        (base := offset + 2 + 2 + 2 + 2 + 2) input[5] h_agree (by omega)
      simp only [CircuitType.eval_var_field, Expression.eval, h4, h5]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial
  -- `t0123 <== t01 * t23`: witness reads the two prior assignment cells
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      simp only [Witgen.WitgenIR.eval_ofExprs_toElements]
      refine congrArg toElements ?_
      simp only [circuit_norm, HasAssignEq.assignEq] at h_agree ⊢
      rw [h_agree (offset + 2 + 2 + 2 + 2 + 2 + 2) (by omega),
        h_agree (offset + 2 + 2 + 2 + 2 + 2 + 2 + 1) (by omega)]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial
  -- `z <== t0123 * t45`: witness reads the two prior assignment cells
  · refine ⟨?_, ?_, ?_⟩
    · intro h_agree _
      simp only [Witgen.WitgenIR.eval_ofExprs_toElements]
      refine congrArg toElements ?_
      simp only [circuit_norm, HasAssignEq.assignEq] at h_agree ⊢
      rw [h_agree (offset + 2 + 2 + 2 + 2 + 2 + 2 + 1 + 1 + 1) (by omega),
        h_agree (offset + 2 + 2 + 2 + 2 + 2 + 2 + 1 + 1) (by omega)]
    · exact equalityFieldSubcircuit_flatStructural_any input _ _ _ env env'
    · trivial

theorem computableWitness : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (circuit := circuit.base) computableWitnesses

/-- The output of `IsZeroFe.main` is the final witnessed flag (offset `+16`); it
only depends on `env` below `offset + 17`, so it is stable across environments
agreeing below any `k ≥ offset + 17`. -/
lemma eval_output_of_agreesBelow (x : Var Emu (F circomPrime)) {offset k : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : offset + 17 ≤ k) :
    eval env ((main x).output offset) = eval env' ((main x).output offset) := by
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover]
  simp only [main, circuit_norm, Gadgets.IsZeroField.circuit]
  exact h_agree (offset + 16) (by omega)

end IsZeroFe
end Solution.Bls12381G1ScalarMul
