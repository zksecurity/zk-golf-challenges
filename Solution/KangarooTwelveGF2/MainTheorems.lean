import Challenge.Instances.KangarooTwelveGF2.Interface

namespace Solution.KangarooTwelveGF2

open Challenge.Instances.KangarooTwelveGF2.Interface
open Challenge.F2Bits

theorem eval_input_state {input : Var Input (F p2)}
    {env env' : ProverEnvironment (F p2)} (h : eval env input = eval env' input) :
    eval env input.state = eval env' input.state := by
  rw [CircuitType.eval_var_fields_prover, CircuitType.eval_var_fields_prover]
  have hstate := congrArg (fun x : Input (F p2) => x.state) h
  simpa [circuit_norm] using hstate

end Solution.KangarooTwelveGF2
