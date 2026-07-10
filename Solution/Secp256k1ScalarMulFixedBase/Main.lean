import Solution.Secp256k1ScalarMulFixedBase.ScalarMul
import Solution.Secp256k1ScalarMulFixedBase.MainTheorems
import Solution.Secp256k1ScalarMulFixedBase.Cost
import Challenge.Instances.Secp256k1ScalarMulFixedBase.Interface

/-!
# Top-level circuit — comparator entry point (fixed base)

Adapts the instance Interface (byte-encoded output, SEC1-style big-endian) to
the `ScalarMul` gadget (4×64-bit little-endian limbs) with the base point
fixed to the standard generator `G`, and exports the four comparator
obligations.

The base point is supplied as constant limbs (`MainTheorems.gxConst` /
`gyConst`), so there is no in-circuit packing on the input side and the input
is the scalar bits alone. The output side needs no conversion — the gadget
already produces big-endian bytes with a masked infinity flag, matching
`Interface.Output` field for field.
-/

namespace Solution.Secp256k1ScalarMulFixedBase

open Challenge.Instances.Secp256k1ScalarMulFixedBase

def main (input : Var Interface.Input (F Interface.circomPrime)) :
    Circuit (F Interface.circomPrime) (Var Interface.Output (F Interface.circomPrime)) := do
  let out ← subcircuit ScalarMul.circuit
    { bits := input.bits, px := MainTheorems.gxConst, py := MainTheorems.gyConst }
  return { x := out.x, y := out.y, isInf := out.isInf }

instance elaborated :
    ElaboratedCircuit (F Interface.circomPrime) Interface.Input Interface.Output main := by
  elaborate_circuit

/-- Claimed circuit cost (certified in `Cost.lean` / `mainCost` below). The
generic double-and-add gadget allocates the same cells whether the base point
is an input or a constant, so the cost matches the variable-base circuit. -/
@[reducible] def allocations : Nat := 8182144
@[reducible] def constraints : Nat := 8279944

theorem soundness :
    GeneralFormalCircuit.Soundness (F Interface.circomPrime) main
      Interface.Assumptions Interface.Spec := by
  circuit_proof_start
  simp only [Interface.Assumptions, Interface.IsBits] at h_assumptions
  rw [show ScalarMul.circuit.Assumptions = ScalarMul.Assumptions from rfl,
    show ScalarMul.circuit.Spec = ScalarMul.Spec from rfl] at h_holds
  simp only [ScalarMul.Assumptions, ScalarMul.Spec] at h_holds
  obtain ⟨h_valid, h_spec⟩ := h_holds
    ⟨fun i => MainTheorems.isBool_of_val_lt_two (h_assumptions i),
     MainTheorems.fe_valid_gxConst env,
     MainTheorems.fe_valid_gyConst env,
     by rw [MainTheorems.decodeFe_gxConst, MainTheorems.decodeFe_gyConst]
        exact MainTheorems.G_onCurve⟩
  simp only [circuit_norm, ScalarMul.circuit, ScalarMul.elaborated] at h_valid h_spec
  refine ⟨?_, ?_⟩
  · rw [MainTheorems.decodeFe_gxConst, MainTheorems.decodeFe_gyConst,
        ← MainTheorems.decodeOutput_eq] at h_spec
    exact ⟨MainTheorems.outputValid_of_valid h_valid, h_spec⟩
  · exact Or.inl rfl

theorem completeness :
    GeneralFormalCircuit.Completeness (F Interface.circomPrime) main
      Interface.ProverAssumptions Interface.ProverSpec := by
  circuit_proof_start
  simp only [Interface.ProverAssumptions, Interface.Assumptions, Interface.IsBits]
    at h_assumptions
  rw [show ScalarMul.circuit.Assumptions = ScalarMul.Assumptions from rfl]
  simp only [ScalarMul.Assumptions]
  refine ⟨⟨fun i => MainTheorems.isBool_of_val_lt_two (h_assumptions i),
    MainTheorems.fe_valid_gxConst env.toEnvironment,
    MainTheorems.fe_valid_gyConst env.toEnvironment, ?_⟩, trivial⟩
  rw [MainTheorems.decodeFe_gxConst, MainTheorems.decodeFe_gyConst]
  exact MainTheorems.G_onCurve

section Cost

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMulFixedBase.Cost

-- Keep the trusted R1CS predicates opaque while *applying* the per-gadget
-- certificates (see `Cost.lean`): otherwise the unifier evaluates
-- `r1csProducts` on the asserted expressions and loops on neutral subterms.
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- The constant generator limbs are affine (each is a field constant). -/
private theorem affineW_gxConst : AffineW MainTheorems.gxConst := by
  intro k hk
  simp only [MainTheorems.gxConst, emuConst]
  rw [Vector.getElem_ofFn]
  exact Affine.const _

private theorem affineW_gyConst : AffineW MainTheorems.gyConst := by
  intro k hk
  simp only [MainTheorems.gyConst, emuConst]
  rw [Vector.getElem_ofFn]
  exact Affine.const _

/-- Compositional `CostIs` certificate for the whole circuit: one `ScalarMul`
subcircuit (the constant base-point limbs are not operations) and a pure field
re-wrap. -/
private theorem costIs_main (input : Var Interface.Input (F Interface.circomPrime)) :
    CostIs (main input) ⟨allocations, constraints⟩ := by
  rw [show (⟨allocations, constraints⟩ : Count) = scalarMulCost + Count.zero from by decide]
  unfold main
  exact CostIs.bind (costIs_sub_scalarMul _) fun out => CostIs.pure _

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ :=
  fun input => costIs_main input

/-- Top-level single-row R1CS assembly: the base point is affine (constant),
so the single `ScalarMul` subcircuit invocation is single-row R1CS; the
returned struct is a pure re-wrap. -/
private theorem isR1CS_main_param (input : Var Interface.Input (F Interface.circomPrime))
    (hbits : AffineW input.bits) :
    IsR1CSCirc (main input) := by
  unfold main
  refine IsR1CSCirc.bind_out (isR1CS_sub_scalarMul _ ?_ ?_ ?_) fun nout => ?_
  · exact fun i hi => hbits i hi
  · exact affineW_gxConst
  · exact affineW_gyConst
  exact IsR1CSCirc.pure _

/-- The circuit's output wires are the `ScalarMul` output wires re-wrapped
field-for-field: reindexed fresh `Mux` witness cells plus the fold
accumulator's flag cell — all affine. -/
private theorem affineOutput_main (input : Var Interface.Input (F Interface.circomPrime)) :
    AffineOutput (main input) := by
  intro n
  unfold main
  rw [Circuit.bind_output_eq, Circuit.pure_output_eq]
  have h := affineOut_sub_scalarMul
    { bits := input.bits, px := MainTheorems.gxConst, py := MainTheorems.gyConst } n
  exact affineProvable_interfaceOutput h.1 h.2.1 h.2.2

theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => isR1CS_main_param input (affineInput_components input hinput))
    (fun input _ => affineOutput_main input)

end Cost

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

-- Keep the `ScalarMul` child opaque: unifying the structural goal against the
-- subcircuit lemma would otherwise `whnf` the 256-step fold and overflow the
-- kernel. `unfold main` still works through the equational lemma.
attribute [local irreducible] main ScalarMul.circuit ScalarMul.main

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n
    (fun env : ProverEnvironment (F Interface.circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := by
  intro n input hinput env env'
  change (main input).operations n |>.forAllFlat n
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  have hstruct :
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        input env env' n ((main input).operations n) := by
    unfold main
    simp only [
      Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff, and_true]
    refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      ScalarMul.circuit input
      { bits := input.bits, px := MainTheorems.gxConst, py := MainTheorems.gyConst } n ?_
      ScalarMul.computableWitnesses env env'
    intro e1 e2 h_input_eq
    simp only [circuit_norm, ScalarMul.Inputs.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simpa [circuit_norm] using
        congrArg (fun x : Interface.Input (F Interface.circomPrime) => x.bits) h_input_eq
    · rw [MainTheorems.eval_gxConst, MainTheorems.eval_gxConst]
    · rw [MainTheorems.eval_gyConst, MainTheorems.eval_gyConst]
  -- reduce the flattened structural condition to the target `forAllFlat` condition
  have hflat :=
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
      input env env' hstruct
  unfold Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition at hflat
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  let targetCondition : Condition (F Interface.circomPrime) :=
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  apply FlatOperation.forAll_implies (F := F Interface.circomPrime) n ?_ hflat
  have himplies : ∀ (ops : List (FlatOperation (F Interface.circomPrime))) (off : ℕ),
      n ≤ off →
      FlatOperation.forAll off
        (Condition.implies
          (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
            input env env')
          targetCondition).ignoreSubcircuit
        ops := by
    intro ops off hoff
    induction ops generalizing off with
    | nil => simp [FlatOperation.forAll]
    | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          constructor
          · intro hparent hagree
            exact hparent hagree
              (hinput env env' (ProverEnvironment.agreesBelow_of_le hagree hoff))
          · exact ih (m + off) (by omega)
      | assert e =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | lookup l =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | interact i =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
  exact himplies ((main input).operations n).toFlat n (le_refl n)

end ComputableWitness

-- No `formalCircuit` bundle here: unifying the theorems against the
-- `GeneralFormalCircuit` field types forces a `whnf` of the 256-step fold
-- term and times out, and the comparator only requires `main`, `elaborated`,
-- and the four theorems above.

end Solution.Secp256k1ScalarMulFixedBase
