import Clean.Circuit
import Clean.Utils.Bits
import Challenge.Utils.ComputableWitnessLemmas
import Challenge.Instances.AssertBytes.Interface

/-!
# `Num2Bits` gadget — bit-decomposition range check

`Num2Bits n` is a `FormalAssertion` on a single field element `x`: it witnesses
`n` bits, boolean-constrains each of them, and asserts that `x` equals their
little-endian recomposition `Σ bitᵢ · 2ⁱ`. As a side effect this constrains
`x.val < 2ⁿ`, so it doubles as an `n`-bit range check.

It is written from circuit primitives only (`witnessVector`, `Circuit.forEach`,
`assertZero`) — it does **not** reuse any prebuilt Clean gadget — while reusing
the pure bit-arithmetic helpers in `Clean.Utils.Bits` (`fieldToBits` /
`fieldFromBitsExpr` and their inversion lemmas).

Soundness and completeness are fully proved.
-/

namespace Solution.AssertBytes
namespace Num2Bits

open Challenge.Instances.AssertBytes.Interface
open Utils.Bits
open Challenge.Utils.ComputableWitnessLemmas

/-- The `main` circuit: witness the `n` bits of `x`, boolean-constrain each bit
(`bit · (bit − 1) = 0`), and assert the recomposition equals `x`. No output (it
is an assertion). -/
def main (n : ℕ) (x : Expression (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let bits ← witnessVector n (fun env => fieldToBits n (x.eval env))
  Circuit.forEach bits (fun b => assertZero (b * (b - 1)))
  assertZero (x - fieldFromBitsExpr bits)

instance elaborated (n : ℕ) : ElaboratedCircuit (F circomPrime) field unit (main n) := by
  elaborate_circuit

/-- No preconditions: the assertion is sound on arbitrary `x`. -/
def Assumptions (_x : F circomPrime) : Prop := True

/-- Postcondition: `x` is representable in `n` bits (`x.val < 2ⁿ`). -/
def Spec (n : ℕ) (x : F circomPrime) : Prop := x.val < 2 ^ n

theorem soundness (n : ℕ) :
    FormalAssertion.Soundness (Input := field) (F circomPrime) (main n) Assumptions (Spec n) := by
  circuit_proof_start [main, Spec]
  obtain ⟨h_bool, h_eq⟩ := h_holds
  set bit_vars : Vector (Expression (F circomPrime)) n :=
    Vector.mapRange n (fun i => var ⟨i₀ + i⟩) with hbv
  -- each evaluated bit reads back the witness cell at `i₀ + i`
  have hval : ∀ (i : ℕ) (hi : i < n), (bit_vars.map env)[i] = env.get (i₀ + i) := by
    intro i hi
    simp only [hbv, Vector.getElem_map, Vector.getElem_mapRange]
    rfl
  -- the booleanity constraints force each evaluated bit to be 0 or 1
  have h_bits : ∀ (i : ℕ) (hi : i < n),
      (bit_vars.map env)[i] = 0 ∨ (bit_vars.map env)[i] = 1 := by
    intro i hi
    rw [hval i hi]
    rcases mul_eq_zero.mp (h_bool ⟨i, hi⟩) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (add_neg_eq_zero.mp h1)
  -- the recomposition constraint pins `input` to the value of its bits
  have hin : input = fieldFromBits (bit_vars.map env) := by
    rw [add_neg_eq_zero.mp h_eq]; exact fieldFromBits_eval bit_vars
  rw [hin]
  exact fieldFromBits_lt _ h_bits

theorem completeness (n : ℕ) :
    FormalAssertion.Completeness (Input := field) (F circomPrime) (main n) Assumptions (Spec n) := by
  circuit_proof_start [main, Spec]
  set bit_vars : Vector (Expression (F circomPrime)) n :=
    Vector.mapRange n (fun i => var ⟨i₀ + i⟩) with hbv
  refine ⟨?_, ?_⟩
  · -- booleanity: every witnessed bit is one of `fieldToBits`'s 0/1 entries
    intro i
    rw [h_env i]
    rcases @fieldToBits_bits circomPrime _ n input i.val i.isLt with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring
  · -- recomposition: the witnessed bits recompose to `input` (valid since input < 2ⁿ)
    rw [add_neg_eq_zero]
    have he : Expression.eval env.toEnvironment (fieldFromBitsExpr bit_vars)
        = fieldFromBits (bit_vars.map env.toEnvironment) := fieldFromBits_eval bit_vars
    rw [he]
    have hmap : bit_vars.map env.toEnvironment = fieldToBits n input := by
      apply Vector.ext
      intro i hi
      rw [hbv, Vector.getElem_map, Vector.getElem_mapRange]
      simpa using h_env ⟨i, hi⟩
    have hff := @fieldFromBits_fieldToBits circomPrime _ n input h_spec
    rw [hmap, hff]

def circuit (n : ℕ) : FormalAssertion (F circomPrime) field where
  main := main n
  elaborated := elaborated n
  Assumptions := Assumptions
  Spec := Spec n
  soundness := soundness n
  completeness := completeness n

theorem computableWitnesses (n : ℕ) : (circuit n).ComputableWitnesses := by
  intro offset x env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition x env env')
    ((main n x).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true, implies_true, forall_const]
  -- only the witness-generator obligation survives; it reads only `x`
  intro _ h_input
  have h_eval : Expression.eval env.toEnvironment x =
      Expression.eval env'.toEnvironment x := by
    rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at h_input
    exact h_input
  simpa using congrArg (fieldToBits n) h_eval

theorem computableWitness (n : ℕ) : ∀ offset x,
    ProverEnvironment.OnlyAccessedBelow offset
      (fun env : ProverEnvironment (F circomPrime) => eval env x) →
    (main n x).ComputableWitnesses offset := by
  exact FormalCircuitBase.computableWitnesses_implies (computableWitnesses n)

theorem computableWitnesses_of_onlyAccessedBelow (n offset : ℕ)
    (x : Expression (F circomPrime))
    (hx : ProverEnvironment.OnlyAccessedBelow offset
      (fun env : ProverEnvironment (F circomPrime) => eval env x)) :
    (main n x).ComputableWitnesses offset :=
  computableWitness n offset x hx

end Num2Bits
end Solution.AssertBytes
