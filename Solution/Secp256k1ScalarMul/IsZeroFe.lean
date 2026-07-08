import Solution.Secp256k1ScalarMul.Params
import Solution.Secp256k1ScalarMul.IsZeroFeTheorems
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
  main; elaborated; Assumptions; Spec; soundness; completeness

end IsZeroFe
end Solution.Secp256k1ScalarMul
