import Challenge.Instances.KangarooTwelveGF2.Interface

namespace Solution.KangarooTwelveGF2

open Challenge.Instances.KangarooTwelveGF2.Interface
open Challenge.F2Bits

theorem eval_input_state {input : Var Input (F p2)}
    {env env' : ProverEnvironment (F p2)} (h : eval env input = eval env' input) :
    eval env input.state = eval env' input.state := by
  obtain ⟨s⟩ := input
  have hstate := congrArg (fun x : Input (F p2) => x.state) h
  simp only [circuit_norm, explicit_provable_type] at hstate ⊢
  exact hstate

end Solution.KangarooTwelveGF2
