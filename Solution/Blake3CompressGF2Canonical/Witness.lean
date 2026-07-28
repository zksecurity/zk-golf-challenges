import Solution.Blake3CompressGF2Canonical.Canonical

/-!
# Computable-witness certificate

Every composite gadget ends in a fresh pinned word, state, quad, or config.
The agreement lemmas below therefore depend only on the final allocation
interval, while witness generation itself follows the small formal-circuit
hierarchy.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.Instances.Blake3CompressGF2Canonical.Interface.Blake3Bits
open Challenge.F2Bits
open Challenge.Utils.ComputableWitnessLemmas

variable {env env' : ProverEnvironment (F p2)}

theorem eval_xorRotate_congr {x y : Word (Expression (F p2))}
    (hx : eval env x = eval env' x) (hy : eval env y = eval env' y) (n : ℕ) :
    eval env (rotRight (xorWord x y) n) =
      eval env' (rotRight (xorWord x y) n) := by
  simp only [circuit_norm] at hx hy ⊢
  rw [eval_rotRight, eval_rotRight, eval_xorWord, eval_xorWord, hx, hy]

theorem eval_stateWord_congr {v : State (Expression (F p2))}
    (hv : eval env v = eval env' v) (i : Fin 16) :
    eval env (stateWord v i) = eval env' (stateWord v i) := by
  simp only [circuit_norm] at hv ⊢
  rw [eval_stateWord, eval_stateWord, hv]

theorem eval_writeQuad_congr {v : State (Expression (F p2))}
    {q : Var Quad (F p2)}
    (hv : eval env v = eval env' v) (hq : eval env q = eval env' q)
    (a b c d : Fin 16) :
    eval env (writeQuad v a b c d q) =
      eval env' (writeQuad v a b c d q) := by
  have hq' : eval env.toEnvironment q = eval env'.toEnvironment q := by
    rw [← CircuitType.eval_expression_prover_to_verifier env q,
      ← CircuitType.eval_expression_prover_to_verifier env' q]
    exact hq
  simp only [circuit_norm] at hv ⊢
  rw [eval_writeQuad, eval_writeQuad, hv, hq']

theorem eval_permuteState_congr {v : State (Expression (F p2))}
    (hv : eval env v = eval env' v) :
    eval env (permuteState v) = eval env' (permuteState v) := by
  simp only [circuit_norm] at hv ⊢
  rw [eval_permuteState, eval_permuteState, hv]

theorem eval_finalizeState_congr {v initial : State (Expression (F p2))}
    (hv : eval env v = eval env' v) (hi : eval env initial = eval env' initial) :
    eval env (finalizeState v initial) =
      eval env' (finalizeState v initial) := by
  simp only [circuit_norm] at hv hi ⊢
  rw [eval_finalizeState, eval_finalizeState, hv, hi]

theorem eval_initialState_congr {bits : Vector (Expression (F p2)) 896}
    (hbits : eval env bits = eval env' bits) :
    eval env (initialState (splitWords 28 bits)) =
      eval env' (initialState (splitWords 28 bits)) := by
  simp only [circuit_norm] at hbits ⊢
  rw [eval_initialState, eval_initialState, eval_splitWords, eval_splitWords, hbits]

theorem eval_initialBlock_congr {bits : Vector (Expression (F p2)) 896}
    (hbits : eval env bits = eval env' bits) :
    eval env (initialBlock (splitWords 28 bits)) =
      eval env' (initialBlock (splitWords 28 bits)) := by
  simp only [circuit_norm] at hbits ⊢
  rw [eval_initialBlock, eval_initialBlock, eval_splitWords, eval_splitWords, hbits]

theorem eval_xorInputs_mk_congr
    {x y : Word (Expression (F p2))}
    (hx : eval env x = eval env' x) (hy : eval env y = eval env' y) :
    eval env (⟨x, y⟩ : Var XorRotateExact.Inputs (F p2)) =
      eval env' (⟨x, y⟩ : Var XorRotateExact.Inputs (F p2)) := by
  simp only [circuit_norm] at hx hy ⊢
  rw [hx, hy]

theorem eval_quad_mk_congr
    {a b c d : Word (Expression (F p2))}
    (ha : eval env a = eval env' a) (hb : eval env b = eval env' b)
    (hc : eval env c = eval env' c) (hd : eval env d = eval env' d) :
    eval env (⟨a, b, c, d⟩ : Var Quad (F p2)) =
      eval env' (⟨a, b, c, d⟩ : Var Quad (F p2)) := by
  simp only [circuit_norm] at ha hb hc hd ⊢
  rw [ha, hb, hc, hd]

theorem eval_gInputs_mk_congr
    {a b c d mx my : Word (Expression (F p2))}
    (ha : eval env a = eval env' a) (hb : eval env b = eval env' b)
    (hc : eval env c = eval env' c) (hd : eval env d = eval env' d)
    (hmx : eval env mx = eval env' mx) (hmy : eval env my = eval env' my) :
    eval env (⟨a, b, c, d, mx, my⟩ : Var GInputs (F p2)) =
      eval env' (⟨a, b, c, d, mx, my⟩ : Var GInputs (F p2)) := by
  simp only [circuit_norm] at ha hb hc hd hmx hmy ⊢
  rw [ha, hb, hc, hd, hmx, hmy]

theorem eval_applyGInputs_mk_congr
    {state : State (Expression (F p2))} {mx my : Word (Expression (F p2))}
    (hs : eval env state = eval env' state)
    (hmx : eval env mx = eval env' mx) (hmy : eval env my = eval env' my) :
    eval env (⟨state, mx, my⟩ : Var ApplyG.Inputs (F p2)) =
      eval env' (⟨state, mx, my⟩ : Var ApplyG.Inputs (F p2)) := by
  simp only [circuit_norm] at hs hmx hmy ⊢
  rw [hs, hmx, hmy]

theorem eval_roundInputs_mk_congr
    {state block : State (Expression (F p2))}
    (hs : eval env state = eval env' state)
    (hb : eval env block = eval env' block) :
    eval env (⟨state, block⟩ : Var Round.Inputs (F p2)) =
      eval env' (⟨state, block⟩ : Var Round.Inputs (F p2)) := by
  simp only [circuit_norm] at hs hb ⊢
  rw [hs, hb]

theorem eval_config_mk_congr
    {state block : State (Expression (F p2))}
    (hs : eval env state = eval env' state)
    (hb : eval env block = eval env' block) :
    eval env (⟨state, block⟩ : Var Config (F p2)) =
      eval env' (⟨state, block⟩ : Var Config (F p2)) := by
  simp only [circuit_norm] at hs hb ⊢
  rw [hs, hb]

theorem eval_finalizeInputs_mk_congr
    {state initial : State (Expression (F p2))}
    (hs : eval env state = eval env' state)
    (hi : eval env initial = eval env' initial) :
    eval env (⟨state, initial⟩ : Var Finalize.Inputs (F p2)) =
      eval env' (⟨state, initial⟩ : Var Finalize.Inputs (F p2)) := by
  simp only [circuit_norm] at hs hi ⊢
  rw [hs, hi]

theorem eval_input_bits_congr {x : Var Input (F p2)}
    (h : eval env x = eval env' x) : eval env x.bits = eval env' x.bits := by
  have hx := congrArg (fun y : Input (F p2) => y.bits) h
  simpa [circuit_norm] using hx

theorem eval_applyG_state_congr {x : Var ApplyG.Inputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.state = eval env' x.state := by
  have hx := congrArg (fun y : ApplyG.Inputs (F p2) => y.state) h
  simpa [circuit_norm] using hx

theorem eval_applyG_mx_congr {x : Var ApplyG.Inputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.mx = eval env' x.mx := by
  have hx := congrArg (fun y : ApplyG.Inputs (F p2) => y.mx) h
  simpa [circuit_norm] using hx

theorem eval_applyG_my_congr {x : Var ApplyG.Inputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.my = eval env' x.my := by
  have hx := congrArg (fun y : ApplyG.Inputs (F p2) => y.my) h
  simpa [circuit_norm] using hx

theorem eval_round_state_congr {x : Var Round.Inputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.state = eval env' x.state := by
  have hx := congrArg (fun y : Round.Inputs (F p2) => y.state) h
  simpa [circuit_norm] using hx

theorem eval_round_block_congr {x : Var Round.Inputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.block = eval env' x.block := by
  have hx := congrArg (fun y : Round.Inputs (F p2) => y.block) h
  simpa [circuit_norm] using hx

theorem eval_config_state_congr {x : Var Config (F p2)}
    (h : eval env x = eval env' x) : eval env x.state = eval env' x.state := by
  have hx := congrArg (fun y : Config (F p2) => y.state) h
  simpa [circuit_norm] using hx

theorem eval_config_block_congr {x : Var Config (F p2)}
    (h : eval env x = eval env' x) : eval env x.block = eval env' x.block := by
  have hx := congrArg (fun y : Config (F p2) => y.block) h
  simpa [circuit_norm] using hx

theorem eval_finalize_state_congr {x : Var Finalize.Inputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.state = eval env' x.state := by
  have hx := congrArg (fun y : Finalize.Inputs (F p2) => y.state) h
  simpa [circuit_norm] using hx

theorem eval_finalize_initial_congr {x : Var Finalize.Inputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.initial = eval env' x.initial := by
  have hx := congrArg (fun y : Finalize.Inputs (F p2) => y.initial) h
  simpa [circuit_norm] using hx

theorem eval_g_a_congr {x : Var GInputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.a = eval env' x.a := by
  have hx := congrArg (fun y : GInputs (F p2) => y.a) h
  simpa [circuit_norm] using hx

theorem eval_g_b_congr {x : Var GInputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.b = eval env' x.b := by
  have hx := congrArg (fun y : GInputs (F p2) => y.b) h
  simpa [circuit_norm] using hx

theorem eval_g_c_congr {x : Var GInputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.c = eval env' x.c := by
  have hx := congrArg (fun y : GInputs (F p2) => y.c) h
  simpa [circuit_norm] using hx

theorem eval_g_d_congr {x : Var GInputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.d = eval env' x.d := by
  have hx := congrArg (fun y : GInputs (F p2) => y.d) h
  simpa [circuit_norm] using hx

theorem eval_g_mx_congr {x : Var GInputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.mx = eval env' x.mx := by
  have hx := congrArg (fun y : GInputs (F p2) => y.mx) h
  simpa [circuit_norm] using hx

theorem eval_g_my_congr {x : Var GInputs (F p2)}
    (h : eval env x = eval env' x) : eval env x.my = eval env' x.my := by
  have hx := congrArg (fun y : GInputs (F p2) => y.my) h
  simpa [circuit_norm] using hx

theorem eval_quad_a_congr {x : Var Quad (F p2)}
    (h : eval env x = eval env' x) : eval env x.a = eval env' x.a := by
  have hx := congrArg (fun y : Quad (F p2) => y.a) h
  simpa [circuit_norm] using hx

theorem eval_quad_b_congr {x : Var Quad (F p2)}
    (h : eval env x = eval env' x) : eval env x.b = eval env' x.b := by
  have hx := congrArg (fun y : Quad (F p2) => y.b) h
  simpa [circuit_norm] using hx

theorem eval_quad_c_congr {x : Var Quad (F p2)}
    (h : eval env x = eval env' x) : eval env x.c = eval env' x.c := by
  have hx := congrArg (fun y : Quad (F p2) => y.c) h
  simpa [circuit_norm] using hx

theorem eval_quad_d_congr {x : Var Quad (F p2)}
    (h : eval env x = eval env' x) : eval env x.d = eval env' x.d := by
  have hx := congrArg (fun y : Quad (F p2) => y.d) h
  simpa [circuit_norm] using hx

theorem eval_freshQuad_of_agreesBelow (offset : ℕ) {k : ℕ}
    (hk : offset + 128 ≤ k) (h_agree : env.AgreesBelow k env') :
    eval env
        ({ a := varFromOffset (fields 32) offset
           b := varFromOffset (fields 32) (offset + 32)
           c := varFromOffset (fields 32) (offset + 64)
           d := varFromOffset (fields 32) (offset + 96) } : Var Quad (F p2)) =
      eval env'
        ({ a := varFromOffset (fields 32) offset
           b := varFromOffset (fields 32) (offset + 32)
           c := varFromOffset (fields 32) (offset + 64)
           d := varFromOffset (fields 32) (offset + 96) } : Var Quad (F p2)) :=
  eval_quad_mk_congr
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))

namespace AddExact

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Add32Canon.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Add32Canon.circuit input input offset (fun _ _ h => h)
      Add32Canon.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Pin32Canon.circuit input _ _ ?_ Pin32Canon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32Canon.eval_subOut_of_agreesBelow input offset
      (by omega) h_agree h_input

theorem subcircuit_localLength (input : Var Add32.Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 94 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Add32.Inputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 94 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      (varFromOffset (fields 32) (n + 62) : Var (fields 32) (F p2)) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

end AddExact

namespace XorRotateExact

theorem computableWitnesses (r : ℕ) : (circuit r).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main r input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    Pin32Canon.circuit input _ offset
    (fun _ _ h => eval_xorRotate_congr
      (by
        have hx := congrArg Inputs.x h
        simpa [circuit_norm] using hx)
      (by
        have hy := congrArg Inputs.y h
        simpa [circuit_norm] using hy) r)
    Pin32Canon.computableWitnesses env env'

theorem subcircuit_localLength (r : ℕ) (input : Var Inputs (F p2)) (n : ℕ) :
    (subcircuit (circuit r) input).localLength n = 32 := rfl

theorem eval_subOut_of_agreesBelow (r : ℕ) (input : Var Inputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 32 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit (circuit r) input).output n) =
      eval env' ((subcircuit (circuit r) input).output n) :=
  Pin32Canon.eval_subOut_of_agreesBelow
    (rotRight (xorWord input.x input.y) r) n hk h_agree

end XorRotateExact

namespace PinQuadExact

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    Pin32Canon.subcircuit_localLength, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Pin32Canon.circuit input _ _ (fun _ _ h => by
        first
        | have hx := congrArg Quad.a h; simpa [circuit_norm] using hx
        | have hx := congrArg Quad.b h; simpa [circuit_norm] using hx
        | have hx := congrArg Quad.c h; simpa [circuit_norm] using hx
        | have hx := congrArg Quad.d h; simpa [circuit_norm] using hx)
      Pin32Canon.computableWitnesses env env'

theorem subcircuit_localLength (input : Var Quad (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 128 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Quad (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 128 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      { a := varFromOffset (fields 32) n
        b := varFromOffset (fields 32) (n + 32)
        c := varFromOffset (fields 32) (n + 64)
        d := varFromOffset (fields 32) (n + 96) } := rfl
  rw [hout]
  exact eval_quad_mk_congr
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))

end PinQuadExact

namespace GFirst

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    AddExact.subcircuit_localLength, XorRotateExact.subcircuit_localLength]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      AddExact.circuit input _ offset
      (fun _ _ h => Add32.eval_mk_congr (eval_g_a_congr h) (eval_g_b_congr h))
      AddExact.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      AddExact.circuit input _ _ ?_ AddExact.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32.eval_mk_congr
      (AddExact.eval_subOut_of_agreesBelow _ offset (by omega) h_agree)
      (eval_g_mx_congr h_input)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (XorRotateExact.circuit 16) input _ _ ?_
      (XorRotateExact.computableWitnesses 16) env env'
    intro kk e e' hle h_agree h_input
    exact eval_xorInputs_mk_congr (eval_g_d_congr h_input)
      (AddExact.eval_subOut_of_agreesBelow _ (offset + 94) (by omega) h_agree)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      AddExact.circuit input _ _ ?_ AddExact.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32.eval_mk_congr (eval_g_c_congr h_input)
      (XorRotateExact.eval_subOut_of_agreesBelow 16 _ (offset + 188)
        (by omega) h_agree)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (XorRotateExact.circuit 12) input _ _ ?_
      (XorRotateExact.computableWitnesses 12) env env'
    intro kk e e' hle h_agree h_input
    exact eval_xorInputs_mk_congr (eval_g_b_congr h_input)
      (AddExact.eval_subOut_of_agreesBelow _ (offset + 220) (by omega) h_agree)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      PinQuadExact.circuit input _ _ ?_ PinQuadExact.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact eval_quad_mk_congr
      (AddExact.eval_subOut_of_agreesBelow _ (offset + 94) (by omega) h_agree)
      (XorRotateExact.eval_subOut_of_agreesBelow 12 _ (offset + 314)
        (by omega) h_agree)
      (AddExact.eval_subOut_of_agreesBelow _ (offset + 220) (by omega) h_agree)
      (XorRotateExact.eval_subOut_of_agreesBelow 16 _ (offset + 188)
        (by omega) h_agree)

theorem subcircuit_localLength (input : Var GInputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 474 := rfl

theorem eval_subOut_of_agreesBelow (input : Var GInputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 474 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      ({ a := varFromOffset (fields 32) (n + 346)
         b := varFromOffset (fields 32) (n + 378)
         c := varFromOffset (fields 32) (n + 410)
         d := varFromOffset (fields 32) (n + 442) } : Var Quad (F p2)) := rfl
  rw [hout]
  exact eval_freshQuad_of_agreesBelow (n + 346) (by omega) h_agree

end GFirst

namespace GSecond

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    AddExact.subcircuit_localLength, XorRotateExact.subcircuit_localLength]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      AddExact.circuit input _ offset
      (fun _ _ h => Add32.eval_mk_congr (eval_g_a_congr h) (eval_g_b_congr h))
      AddExact.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      AddExact.circuit input _ _ ?_ AddExact.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32.eval_mk_congr
      (AddExact.eval_subOut_of_agreesBelow _ offset (by omega) h_agree)
      (eval_g_my_congr h_input)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (XorRotateExact.circuit 8) input _ _ ?_
      (XorRotateExact.computableWitnesses 8) env env'
    intro kk e e' hle h_agree h_input
    exact eval_xorInputs_mk_congr (eval_g_d_congr h_input)
      (AddExact.eval_subOut_of_agreesBelow _ (offset + 94) (by omega) h_agree)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      AddExact.circuit input _ _ ?_ AddExact.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Add32.eval_mk_congr (eval_g_c_congr h_input)
      (XorRotateExact.eval_subOut_of_agreesBelow 8 _ (offset + 188)
        (by omega) h_agree)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (XorRotateExact.circuit 7) input _ _ ?_
      (XorRotateExact.computableWitnesses 7) env env'
    intro kk e e' hle h_agree h_input
    exact eval_xorInputs_mk_congr (eval_g_b_congr h_input)
      (AddExact.eval_subOut_of_agreesBelow _ (offset + 220) (by omega) h_agree)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      PinQuadExact.circuit input _ _ ?_ PinQuadExact.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact eval_quad_mk_congr
      (AddExact.eval_subOut_of_agreesBelow _ (offset + 94) (by omega) h_agree)
      (XorRotateExact.eval_subOut_of_agreesBelow 7 _ (offset + 314)
        (by omega) h_agree)
      (AddExact.eval_subOut_of_agreesBelow _ (offset + 220) (by omega) h_agree)
      (XorRotateExact.eval_subOut_of_agreesBelow 8 _ (offset + 188)
        (by omega) h_agree)

theorem subcircuit_localLength (input : Var GInputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 474 := rfl

theorem eval_subOut_of_agreesBelow (input : Var GInputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 474 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      ({ a := varFromOffset (fields 32) (n + 346)
         b := varFromOffset (fields 32) (n + 378)
         c := varFromOffset (fields 32) (n + 410)
         d := varFromOffset (fields 32) (n + 442) } : Var Quad (F p2)) := rfl
  rw [hout]
  exact eval_freshQuad_of_agreesBelow (n + 346) (by omega) h_agree

end GSecond

namespace G

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    GFirst.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      GFirst.circuit input input offset (fun _ _ h => h)
      GFirst.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      GSecond.circuit input _ _ ?_ GSecond.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hfirst := GFirst.eval_subOut_of_agreesBelow input offset
      (by omega) h_agree
    exact eval_gInputs_mk_congr
      (eval_quad_a_congr hfirst) (eval_quad_b_congr hfirst)
      (eval_quad_c_congr hfirst) (eval_quad_d_congr hfirst)
      (eval_g_mx_congr h_input) (eval_g_my_congr h_input)

theorem subcircuit_localLength (input : Var GInputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 948 := rfl

theorem eval_subOut_of_agreesBelow (input : Var GInputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 948 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      ({ a := varFromOffset (fields 32) (n + 820)
         b := varFromOffset (fields 32) (n + 852)
         c := varFromOffset (fields 32) (n + 884)
         d := varFromOffset (fields 32) (n + 916) } : Var Quad (F p2)) := rfl
  rw [hout]
  exact eval_freshQuad_of_agreesBelow (n + 820) (by omega) h_agree

end G

namespace ApplyG

theorem computableWitnesses (a b c d : Fin 16) :
    (circuit a b c d).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main a b c d input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    G.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      G.circuit input _ offset
      (fun _ _ h => eval_gInputs_mk_congr
        (eval_stateWord_congr (eval_applyG_state_congr h) a)
        (eval_stateWord_congr (eval_applyG_state_congr h) b)
        (eval_stateWord_congr (eval_applyG_state_congr h) c)
        (eval_stateWord_congr (eval_applyG_state_congr h) d)
        (eval_applyG_mx_congr h) (eval_applyG_my_congr h))
      G.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      PinStateCanon.circuit input _ _ ?_
      PinStateCanon.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact eval_writeQuad_congr (eval_applyG_state_congr h_input)
      (G.eval_subOut_of_agreesBelow _ offset (by omega) h_agree) a b c d

theorem subcircuit_localLength (a b c d : Fin 16)
    (input : Var Inputs (F p2)) (n : ℕ) :
    (subcircuit (circuit a b c d) input).localLength n = 1460 := rfl

theorem eval_subOut_of_agreesBelow (a b c d : Fin 16)
    (input : Var Inputs (F p2)) (n : ℕ) {k : ℕ}
    (hk : n + 1460 ≤ k) (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit (circuit a b c d) input).output n) =
      eval env' ((subcircuit (circuit a b c d) input).output n) := by
  have hout : (subcircuit (circuit a b c d) input).output n =
      (varFromOffset (fields 512) (n + 948) : Var State (F p2)) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

end ApplyG

namespace Round.Pair

theorem computableWitnesses
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16) :
    (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    ApplyG.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (ApplyG.circuit a0 b0 c0 d0) input _ offset
      (fun _ _ h => eval_applyGInputs_mk_congr
        (eval_round_state_congr h)
        (eval_stateWord_congr (eval_round_block_congr h) mx0)
        (eval_stateWord_congr (eval_round_block_congr h) my0))
      (ApplyG.computableWitnesses a0 b0 c0 d0) env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (ApplyG.circuit a1 b1 c1 d1) input _ _ ?_
      (ApplyG.computableWitnesses a1 b1 c1 d1) env env'
    intro kk e e' hle h_agree h_input
    exact eval_applyGInputs_mk_congr
      (ApplyG.eval_subOut_of_agreesBelow a0 b0 c0 d0 _ offset
        (by omega) h_agree)
      (eval_stateWord_congr (eval_round_block_congr h_input) mx1)
      (eval_stateWord_congr (eval_round_block_congr h_input) my1)

theorem subcircuit_localLength
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (input : Var Round.Inputs (F p2)) (n : ℕ) :
    (subcircuit
      (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) input).localLength n =
      2920 := rfl

theorem eval_subOut_of_agreesBelow
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (input : Var Round.Inputs (F p2)) (n : ℕ) {k : ℕ}
    (hk : n + 2920 ≤ k) (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit
      (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) input).output n) =
      eval env' ((subcircuit
        (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) input).output n) := by
  have hout : (subcircuit
      (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) input).output n =
      (varFromOffset (fields 512) (n + 2408) : Var State (F p2)) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

end Round.Pair

namespace Round.Columns

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Round.Pair.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (Round.Pair.circuit 0 4 8 12 0 1 1 5 9 13 2 3) input input offset
      (fun _ _ h => h)
      (Round.Pair.computableWitnesses 0 4 8 12 0 1 1 5 9 13 2 3) env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Round.Pair.circuit 2 6 10 14 4 5 3 7 11 15 6 7) input _ _ ?_
      (Round.Pair.computableWitnesses 2 6 10 14 4 5 3 7 11 15 6 7) env env'
    intro kk e e' hle h_agree h_input
    exact eval_roundInputs_mk_congr
      (Round.Pair.eval_subOut_of_agreesBelow
        0 4 8 12 0 1 1 5 9 13 2 3 input offset (by omega) h_agree)
      (eval_round_block_congr h_input)

theorem subcircuit_localLength (input : Var Round.Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 5840 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Round.Inputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 5840 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      (varFromOffset (fields 512) (n + 5328) : Var State (F p2)) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

end Round.Columns

namespace Round.Diagonals

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Round.Pair.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (Round.Pair.circuit 0 5 10 15 8 9 1 6 11 12 10 11) input input offset
      (fun _ _ h => h)
      (Round.Pair.computableWitnesses 0 5 10 15 8 9 1 6 11 12 10 11) env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      (Round.Pair.circuit 2 7 8 13 12 13 3 4 9 14 14 15) input _ _ ?_
      (Round.Pair.computableWitnesses 2 7 8 13 12 13 3 4 9 14 14 15) env env'
    intro kk e e' hle h_agree h_input
    exact eval_roundInputs_mk_congr
      (Round.Pair.eval_subOut_of_agreesBelow
        0 5 10 15 8 9 1 6 11 12 10 11 input offset (by omega) h_agree)
      (eval_round_block_congr h_input)

theorem subcircuit_localLength (input : Var Round.Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 5840 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Round.Inputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 5840 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      (varFromOffset (fields 512) (n + 5328) : Var State (F p2)) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

end Round.Diagonals

namespace Round

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Columns.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Columns.circuit input input offset (fun _ _ h => h)
      Columns.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Diagonals.circuit input _ _ ?_ Diagonals.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact eval_roundInputs_mk_congr
      (Columns.eval_subOut_of_agreesBelow input offset (by omega) h_agree)
      (eval_round_block_congr h_input)

theorem subcircuit_localLength (input : Var Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 11680 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Inputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 11680 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      (varFromOffset (fields 512) (n + 11168) : Var State (F p2)) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)

end Round

namespace Prepare

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    PinStateCanon.subcircuit_localLength, and_true]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      PinStateCanon.circuit input _ offset
      (fun _ _ h => eval_initialState_congr (eval_input_bits_congr h))
      PinStateCanon.computableWitnesses env env'
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      PinStateCanon.circuit input _ _ (fun _ _ _ _ _ h =>
        eval_initialBlock_congr (eval_input_bits_congr h))
      PinStateCanon.computableWitnesses env env'

theorem subcircuit_localLength (input : Var Input (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 1024 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Input (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 1024 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      ({ state := varFromOffset (fields 512) n
         block := varFromOffset (fields 512) (n + 512) } :
        Var Config (F p2)) := rfl
  rw [hout]
  exact eval_config_mk_congr
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))

end Prepare

namespace Step

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    Round.subcircuit_localLength, PinStateCanon.subcircuit_localLength,
    and_true]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Round.circuit input _ offset
      (fun _ _ h => eval_roundInputs_mk_congr
        (eval_config_state_congr h) (eval_config_block_congr h))
      Round.computableWitnesses env env'
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      PinStateCanon.circuit input _ _ (fun _ _ _ _ _ h =>
        eval_permuteState_congr (eval_config_block_congr h))
      PinStateCanon.computableWitnesses env env'

theorem subcircuit_localLength (input : Var Config (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 12192 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Config (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 12192 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      ({ state := varFromOffset (fields 512) (n + 11168)
         block := varFromOffset (fields 512) (n + 11680) } :
        Var Config (F p2)) := rfl
  rw [hout]
  exact eval_config_mk_congr
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))

end Step

namespace Steps2

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Step.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Step.circuit input input offset (fun _ _ h => h)
      Step.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Step.circuit input _ _ ?_ Step.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Step.eval_subOut_of_agreesBelow input offset (by omega) h_agree

theorem subcircuit_localLength (input : Var Config (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 24384 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Config (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 24384 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      ({ state := varFromOffset (fields 512) (n + 23360)
         block := varFromOffset (fields 512) (n + 23872) } :
        Var Config (F p2)) := rfl
  rw [hout]
  exact eval_config_mk_congr
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))

end Steps2

namespace Steps4

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Steps2.subcircuit_localLength]
  constructor
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Steps2.circuit input input offset (fun _ _ h => h)
      Steps2.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Steps2.circuit input _ _ ?_ Steps2.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Steps2.eval_subOut_of_agreesBelow input offset (by omega) h_agree

theorem subcircuit_localLength (input : Var Config (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 48768 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Config (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 48768 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) := by
  have hout : (subcircuit circuit input).output n =
      ({ state := varFromOffset (fields 512) (n + 47744)
         block := varFromOffset (fields 512) (n + 48256) } :
        Var Config (F p2)) := rfl
  rw [hout]
  exact eval_config_mk_congr
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))

end Steps4

namespace Steps7

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Steps4.subcircuit_localLength, Steps2.subcircuit_localLength]
  refine ⟨?_, ?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Steps4.circuit input input offset (fun _ _ h => h)
      Steps4.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Steps2.circuit input _ _ ?_ Steps2.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Steps4.eval_subOut_of_agreesBelow input offset (by omega) h_agree
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Step.circuit input _ _ ?_ Step.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    exact Steps2.eval_subOut_of_agreesBelow _ (offset + 48768)
      (by omega) h_agree

theorem subcircuit_localLength (input : Var Config (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 85344 := rfl

end Steps7

namespace Finalize

theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    PinStateCanon.circuit input _ offset
    (fun _ _ h => eval_finalizeState_congr
      (eval_finalize_state_congr h) (eval_finalize_initial_congr h))
    PinStateCanon.computableWitnesses env env'

theorem subcircuit_localLength (input : Var Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).localLength n = 512 := rfl

theorem eval_subOut_of_agreesBelow (input : Var Inputs (F p2))
    (n : ℕ) {k : ℕ} (hk : n + 512 ≤ k)
    (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit input).output n) =
      eval env' ((subcircuit circuit input).output n) :=
  PinStateCanon.eval_subOut_of_agreesBelow
    (finalizeState input.state input.initial) n hk h_agree

end Finalize

section TopLevel

attribute [local irreducible] Prepare.circuit Steps7.circuit
  Finalize.circuit main

theorem computableWitnessInternal : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p2) => eval env input) →
    Circuit.ComputableWitnesses (main input) n := by
  intro n input hinput env env'
  change (main input).operations n |>.forAllFlat n
    { witness := fun k _ compute =>
        env.AgreesBelow k env' → compute env = compute env' }
  have hstruct : FormalCircuitBase.Operations.StructuralComputableWitnesses
      input env env' n ((main input).operations n) := by
    unfold main
    simp only [Circuit.bind_structuralComputableWitnesses_iff,
      FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
      Circuit.pure_structuralComputableWitnesses_iff,
      Prepare.subcircuit_localLength, Steps7.subcircuit_localLength,
      and_true]
    refine ⟨?_, ?_, ?_⟩
    · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
        Prepare.circuit input input n (fun _ _ h => h)
        Prepare.computableWitnesses env env'
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        Steps7.circuit input _ _ ?_ Steps7.computableWitnesses env env'
      intro kk e e' hle h_agree h_input
      exact Prepare.eval_subOut_of_agreesBelow input n (by omega) h_agree
    · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        Finalize.circuit input _ _ ?_ Finalize.computableWitnesses env env'
      intro kk e e' hle h_agree h_input
      apply eval_finalizeInputs_mk_congr
      · rw [Steps7.output_state_eq]
        exact eval_varFromOffset_of_agreesBelow h_agree (by omega)
      · exact eval_config_state_congr
          (Prepare.eval_subOut_of_agreesBelow input n (by omega) h_agree)
  have hflat :=
    FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
      input env env' hstruct
  unfold FormalCircuitBase.computableWitnessCondition at hflat
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  let targetCondition : Condition (F p2) :=
    { witness := fun k _ compute =>
        env.AgreesBelow k env' → compute env = compute env' }
  apply FlatOperation.forAll_implies (F := F p2) n ?_ hflat
  have himplies : ∀ (ops : List (FlatOperation (F p2))) (off : ℕ),
      n ≤ off →
      FlatOperation.forAll off
        (Condition.implies
          (FormalCircuitBase.computableWitnessCondition input env env')
          targetCondition).ignoreSubcircuit
        ops := by
    intro ops off hoff
    induction ops generalizing off with
    | nil => simp [FlatOperation.forAll]
    | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp only [FlatOperation.forAll, Condition.implies,
            Condition.ignoreSubcircuit]
          constructor
          · intro hparent hagree
            exact hparent hagree
              (hinput env env'
                (ProverEnvironment.agreesBelow_of_le hagree hoff))
          · exact ih (m + off) (by omega)
      | assert e =>
          simp only [FlatOperation.forAll, Condition.implies,
            Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | lookup l =>
          simp only [FlatOperation.forAll, Condition.implies,
            Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | interact i =>
          simp only [FlatOperation.forAll, Condition.implies,
            Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
  exact himplies ((main input).operations n).toFlat n (le_refl n)

end TopLevel

end Solution.Blake3CompressGF2Canonical
