import Challenge.Instances.KeccakP800GF2.Interface

namespace Solution.KeccakP800GF2

open Challenge.Instances.KeccakP800GF2.Interface
open Challenge.F2Bits

theorem eval_input_state {input : Var Input (F p2)}
    {env env' : ProverEnvironment (F p2)} (h : eval env input = eval env' input) :
    eval env input.state = eval env' input.state := by
  obtain ⟨s⟩ := input
  have hstate := congrArg (fun x : Input (F p2) => x.state) h
  simp only [circuit_norm, explicit_provable_type] at hstate ⊢
  exact hstate

/-- Keccak-p[800, 12] unrolled: rounds 10 through 21 of Keccak-f[800], in order. -/
theorem keccakP800_12_unfold {α : Type} [Add α] [Mul α] [Zero α] [One α]
    (s : Specs.KeccakP800.State α) :
    Specs.KeccakP800.keccakP800_12 s =
      Specs.KeccakP800.round 21 (Specs.KeccakP800.round 20 (Specs.KeccakP800.round 19
        (Specs.KeccakP800.round 18 (Specs.KeccakP800.round 17 (Specs.KeccakP800.round 16
        (Specs.KeccakP800.round 15 (Specs.KeccakP800.round 14 (Specs.KeccakP800.round 13
        (Specs.KeccakP800.round 12 (Specs.KeccakP800.round 11 (Specs.KeccakP800.round 10 s))))))))))) := rfl

end Solution.KeccakP800GF2
