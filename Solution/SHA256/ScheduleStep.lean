import Solution.SHA256.LowerSigma0
import Solution.SHA256.LowerSigma1
import Solution.SHA256.Add32
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^33)]

namespace Solution.SHA256

/-!
# SHA-256 Message-Schedule Step

Computes one new schedule word from the four words a step reads:

  w[j] = σ₁(w[j−2]) + w[j−7] + σ₀(w[j−15]) + w[j−16]   (mod 2^32)

Witness count per step:
  lowerSigma1 = 64, lowerSigma0 = 64, 3 × add32 = 3 × 33 = 99
  Total: 64 + 64 + 99 = 227, output word at relative offset 194.

This is the per-step gadget promoted to a standalone `FormalCircuit`, the analog
of `SHA256Round`. The `Spec` is stated in the **balanced** add32 shape (matching
`Specs.SHA256.messageSchedule` / `valSchedule`); the circuit computes the
left-associated chain, and the reassociation is discharged inside `soundness`, so
callers (`MessageSchedule`) need not reassociate.
-/

namespace ScheduleStep

structure Inputs (F : Type) where
  wm2  : fields 32 F   -- w[j-2]
  wm7  : fields 32 F   -- w[j-7]
  wm15 : fields 32 F   -- w[j-15]
  wm16 : fields 32 F   -- w[j-16]
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let s1   ← LowerSigma1.circuit input.wm2
  let s0   ← LowerSigma0.circuit input.wm15
  let sum0 ← Add32.circuit ⟨s1, input.wm7⟩
  let sum1 ← Add32.circuit ⟨sum0, s0⟩
  Add32.circuit ⟨sum1, input.wm16⟩

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.wm2 ∧ Normalized input.wm7 ∧ Normalized input.wm15 ∧ Normalized input.wm16

def Spec (input : Inputs (F p)) (wj : fields 32 (F p)) : Prop :=
  valueBits wj =
    _root_.add32
      (_root_.add32 (Specs.SHA256.lowerSigma1 (valueBits input.wm2)) (valueBits input.wm7))
      (_root_.add32 (Specs.SHA256.lowerSigma0 (valueBits input.wm15)) (valueBits input.wm16))
  ∧ Normalized wj

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main, LowerSigma1.circuit, LowerSigma0.circuit, Add32.circuit]
  obtain ⟨h_m2, h_m7, h_m15, h_m16⟩ := h_assumptions
  simp only [LowerSigma1.Assumptions, LowerSigma1.Spec, LowerSigma0.Assumptions, LowerSigma0.Spec,
    Add32.Assumptions, Add32.Spec, and_imp] at h_holds
  obtain ⟨c_sig1, c_sig0, c_sum0, c_sum1, c_wj⟩ := h_holds
  have s_sig1 := c_sig1 h_m2
  have s_sig0 := c_sig0 h_m15
  have s_sum0 := c_sum0 s_sig1.2 h_m7
  have s_sum1 := c_sum1 s_sum0.2 s_sig0.2
  have s_wj := c_wj s_sum1.2 h_m16
  refine ⟨?_, s_wj.2⟩
  rw [s_wj.1, s_sum1.1, s_sum0.1, s_sig0.1, s_sig1.1]
  show _ = _root_.add32 (_root_.add32 _ _) (_root_.add32 _ _)
  unfold _root_.add32
  omega

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [main, LowerSigma1.circuit, LowerSigma0.circuit, Add32.circuit]
  obtain ⟨h_m2, h_m7, h_m15, h_m16⟩ := h_assumptions
  simp only [LowerSigma1.Assumptions, LowerSigma1.Spec, LowerSigma0.Assumptions, LowerSigma0.Spec,
    Add32.Assumptions, Add32.Spec, and_imp] at h_env ⊢
  obtain ⟨e_sig1, e_sig0, e_sum0, e_sum1, e_wj⟩ := h_env
  obtain ⟨_, n_sig1⟩ := e_sig1 h_m2
  obtain ⟨_, n_sig0⟩ := e_sig0 h_m15
  obtain ⟨_, n_sum0⟩ := e_sum0 n_sig1 h_m7
  obtain ⟨_, n_sum1⟩ := e_sum1 n_sum0 n_sig0
  refine ⟨h_m2, h_m15, ⟨n_sig1, h_m7⟩, ⟨n_sum0, n_sig0⟩, ⟨n_sum1, h_m16⟩⟩

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end ScheduleStep
end Solution.SHA256
end
