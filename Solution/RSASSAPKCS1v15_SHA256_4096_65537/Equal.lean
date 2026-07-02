import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Theorems

/-!
# RSA big-integer equality gadget — `Equal`

`Equal` is a `FormalAssertion` asserting two normalized big integers are limb-wise
equal (hence denote the same natural number). The `BigInt m` type and its
denotation live in `Circuits.RSA.Theorems`.

Soundness and completeness are fully proved.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ}

/-! ## `Equal`

Assert two normalized big integers are limb-wise equal, hence denote the same
natural number.
-/

namespace Equal

/-- Inputs of `Equal`: the two big integers `lhs` and `rhs` to compare. -/
structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

/-- The `main` circuit of `Equal`: assert the two big integers are limb-wise
equal (`lhs === rhs`). -/
def main (input : Var (Inputs m) (F p)) : Circuit (F p) Unit :=
  input.lhs === input.rhs

instance elaborated : ElaboratedCircuit (F p) (Inputs m) unit main where
  localLength _ := 0

/-- Preconditions: both big integers are normalized. -/
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B

/-- Postcondition: the two big integers denote the same natural number. -/
def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B = input.rhs.value B

/-- The `Equal` formal assertion: two normalized big integers are limb-wise
equal, hence denote the same natural number. -/
def circuit (P : BigIntParams p m) : FormalAssertion (F p) (Inputs m) where
  main := main
  Assumptions := Assumptions P.B
  Spec := Spec P.B
  soundness := by
    circuit_proof_start
    simp only [← h_input]
    rw [h_holds]
  completeness := by
    circuit_proof_start
    simp only [← h_input] at h_assumptions h_spec
    exact BigInt.value_inj h_assumptions.1 h_assumptions.2 h_spec

end Equal

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
