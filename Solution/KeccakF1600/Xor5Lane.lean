import Solution.KeccakF1600.XorLane

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

namespace Xor5Lane

structure Inputs (F : Type) where
  a : fields 64 F
  b : fields 64 F
  c : fields 64 F
  d : fields 64 F
  e : fields 64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let t ← XorLane.circuit ⟨input.a, input.b⟩
  let t ← XorLane.circuit ⟨t, input.c⟩
  let t ← XorLane.circuit ⟨t, input.d⟩
  XorLane.circuit ⟨t, input.e⟩

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c ∧
    Normalized input.d ∧ Normalized input.e

def Spec (input : Inputs (F p)) (z : fields 64 (F p)) : Prop :=
  valueBits z =
    valueBits input.a ^^^ valueBits input.b ^^^ valueBits input.c ^^^
      valueBits input.d ^^^ valueBits input.e
  ∧ Normalized z

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 64) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [XorLane.circuit]
  simp only [XorLane.Assumptions, XorLane.Spec, and_imp] at h_holds
  obtain ⟨ha, hb, hc, hd, he⟩ := h_assumptions
  obtain ⟨c1, c2, c3, c4⟩ := h_holds
  obtain ⟨v1, n1⟩ := c1 ha hb
  obtain ⟨v2, n2⟩ := c2 n1 hc
  obtain ⟨v3, n3⟩ := c3 n2 hd
  obtain ⟨v4, n4⟩ := c4 n3 he
  refine ⟨?_, n4⟩
  rw [v4, v3, v2, v1]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [XorLane.circuit]
  simp only [XorLane.Assumptions, XorLane.Spec, and_imp] at h_env ⊢
  obtain ⟨ha, hb, hc, hd, he⟩ := h_assumptions
  obtain ⟨c1, c2, c3, _⟩ := h_env
  obtain ⟨_, n1⟩ := c1 ha hb
  obtain ⟨_, n2⟩ := c2 n1 hc
  obtain ⟨_, n3⟩ := c3 n2 hd
  exact ⟨⟨ha, hb⟩, ⟨n1, hc⟩, ⟨n2, hd⟩, n3, he⟩

def circuit : FormalCircuit (F p) Inputs (fields 64) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Xor5Lane
end Solution.KeccakF1600
end
