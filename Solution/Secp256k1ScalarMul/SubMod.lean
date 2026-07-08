import Solution.Secp256k1ScalarMul.SubModTheorems

/-!
# Emulated field subtraction — `SubMod`

`FormalCircuit` computing `c = a − b mod P256` over canonical emulated field
elements.

## Strategy

Witness the reduced difference `r = (a + P256 − b) % P256` and the borrow bit
`q` characterized by the integer identity

  `r + b = a + q · P256`   (`q = 0` when `b ≤ a`, `q = 1` otherwise),

then certify `q` boolean, `r` normalized and canonical, and the identity via
`EqViaCarries` on the limb-wise coefficient vectors.

Soundness and completeness are fully proved, with the arithmetic content
factored into `SubModTheorems` (on top of the shared `AddModTheorems`).
-/

namespace Solution.Secp256k1ScalarMul
namespace SubMod

/-- Inputs of `SubMod`: minuend `a` and subtrahend `b`, both canonical. -/
structure Inputs (F : Type) where
  a : Emu F
  b : Emu F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Emu (F circomPrime)) := do
  let { a, b } := input

  -- witness r = (a + P256 - b) % P256 and the borrow bit
  let r ← ProvableType.witness (α := Emu) fun env =>
    emuOfNat ((evalEmu env a + P256 - evalEmu env b) % P256)
  let q ← ProvableType.witness (α := field) fun env =>
    (((if evalEmu env a < evalEmu env b then 1 else 0 : ℕ)) : F circomPrime)

  -- q is boolean
  assertZero (q * (q - 1))

  -- r is normalized and canonical
  Normalize.circuit secpParams r
  LessThan.circuit secpParams { lhs := r, rhs := pConst }

  -- r + b = a + q·P256 as integers, limb-coefficient-wise
  let lhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then r[k.val]'h + b[k.val]'h else 0
  let rhs : Vector (Expression (F circomPrime)) (2 * numLimbs - 1) :=
    Vector.mapFinRange (2 * numLimbs - 1) fun k =>
      if h : k.val < numLimbs then a[k.val]'h + q * pConst[k.val]'h else 0
  EqViaCarries.circuit secpParams { lhs := lhs, rhs := rhs }

  return r

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Emu main := by
  elaborate_circuit

/-- Preconditions: both operands are canonical emulated field elements. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  Fe.Valid input.a ∧ Fe.Valid input.b

/-- Postcondition: the output is canonical and decodes to the base-field
difference. -/
def Spec (input : Inputs (F circomPrime)) (out : Emu (F circomPrime)) : Prop :=
  Fe.Valid out ∧ decodeFe out = decodeFe input.a - decodeFe input.b

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

/-- The `SubMod` formal circuit: `c = a − b mod P256`. -/
def circuit : FormalCircuit (F circomPrime) Inputs Emu where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SubMod
end Solution.Secp256k1ScalarMul
