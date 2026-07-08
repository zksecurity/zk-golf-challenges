import Solution.Secp256k1ScalarMulFixedBase.AddModTheorems

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

namespace Solution.Secp256k1ScalarMulFixedBase
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
  main; elaborated; Assumptions; Spec; soundness; completeness

end AddMod
end Solution.Secp256k1ScalarMulFixedBase
