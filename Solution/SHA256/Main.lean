import Challenge.Instances.SHA256.Interface
import Solution.SHA256.Cost
import Solution.SHA256.CompressBlock
import Solution.SHA256.CheckPad
import Solution.SHA256.SelectDigest
import Solution.SHA256.PaddingTheorems
import Solution.SHA256.MainTheorems
import Challenge.Utils.CostR1CS
import Challenge.Utils.ComputableWitnessLemmas

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface

section

def main (input : Var Input (F circomPrime)) : Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  let padded ← witnessVector paddedBitsLen (paddedBitsWitness input)
  let lenFlags ← witnessVector inputBufferLen (lenFlagsWitness input)
  CheckPad.circuit ⟨input.messageLen, input.message, lenFlags, padded⟩
  let state0 : Var SHA256State (F circomPrime) :=
    Vector.ofFn fun i => constWord32 Specs.SHA256.H0[i]
  let state1 ← CompressBlock.circuit ⟨state0, paddedBlock padded 0⟩
  let state2 ← CompressBlock.circuit ⟨state1, paddedBlock padded 1⟩
  let state3 ← CompressBlock.circuit ⟨state2, paddedBlock padded 2⟩
  let state4 ← CompressBlock.circuit ⟨state3, paddedBlock padded 3⟩
  let state5 ← CompressBlock.circuit ⟨state4, paddedBlock padded 4⟩
  let digest ← SelectDigest.circuit ⟨input.messageLen, lenFlags, state1, state2, state3, state4, state5⟩
  return { digest }

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := by
  elaborate_circuit

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main
      Assumptions Spec := by
  circuit_proof_start [CheckPad.circuit, CheckPad.Spec, CheckPad.Assumptions,
    CompressBlock.circuit, CompressBlock.Spec, CompressBlock.Assumptions,
    SelectDigest.circuit, SelectDigest.Spec, SelectDigest.Assumptions]
  obtain ⟨h_cp, h_c1, h_c2, h_c3, h_c4, h_c5, h_sd⟩ := h_holds
  obtain ⟨h_msg_assum, h_len_assum⟩ := h_assumptions
  obtain ⟨h_msg_eq, h_msgLen_eq⟩ := h_input
  -- abbreviations
  set msg := Vector.map ZMod.val input_message with hmsg
  set ℓ := ZMod.val input_messageLen with hℓ
  set pvar : Var SHA256PaddedBits (F circomPrime) :=
    Vector.mapRange paddedBitsLen fun i => var { index := i₀ + i } with hpvar
  -- CheckPad antecedent: message bytes < 256
  have h_cp_assum : ∀ i : Fin inputBufferLen, ZMod.val input_message[i.val] < 256 := by
    intro i
    have := h_msg_assum i
    simpa [fieldElemsToNat, Vector.getElem_map] using this
  obtain ⟨h_len_lt, h_onehot, h_bool, h_byte_eq⟩ := h_cp h_cp_assum
  -- bridge h_byte_eq to (Vector.map (Expression.eval env) pvar)
  have h_byte_eq' : ∀ j : Fin paddedBytesLen,
      paddedByteVal (Vector.map (Expression.eval env) pvar) j = specPaddedByte msg ℓ j.val := by
    intro j
    have := h_byte_eq j
    rw [hmsg, hℓ]
    convert this using 2
  -- bridge h_bool to booleanity of (Vector.map (Expression.eval env) pvar)
  have h_bool' : ∀ i : Fin paddedBitsLen,
      IsBool (Vector.map (Expression.eval env) pvar)[i] := by
    intro i
    have := h_bool i
    rw [hpvar, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange]
    simpa [Expression.eval] using this
  -- per-block value and normalization
  have block_val : ∀ b : Fin paddedBlocksLen,
      Vector.map valueBits (eval env (paddedBlock pvar b)) = specBlock msg ℓ b.val := by
    intro b; exact paddedBlock_value env pvar msg ℓ h_byte_eq' b
  -- chain block 1 (state0 = H0)
  obtain ⟨st1_val, st1_norm⟩ := h_c1
    ⟨(by intro i; exact state0_normalized env i.val i.isLt),
     (by intro i
         have h := paddedBlock_normalized env pvar h_bool' 0 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 0) i.val i.isLt])⟩
  rw [state0_value env, block_val 0] at st1_val
  -- chain block 2
  obtain ⟨st2_val, st2_norm⟩ := h_c2
    ⟨st1_norm,
     (by intro i
         have h := paddedBlock_normalized env pvar h_bool' 1 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 1) i.val i.isLt])⟩
  rw [st1_val, block_val 1] at st2_val
  -- chain block 3
  obtain ⟨st3_val, st3_norm⟩ := h_c3
    ⟨st2_norm,
     (by intro i
         have h := paddedBlock_normalized env pvar h_bool' 2 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 2) i.val i.isLt])⟩
  rw [st2_val, block_val 2] at st3_val
  -- chain block 4
  obtain ⟨st4_val, st4_norm⟩ := h_c4
    ⟨st3_norm,
     (by intro i
         have h := paddedBlock_normalized env pvar h_bool' 3 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 3) i.val i.isLt])⟩
  rw [st3_val, block_val 3] at st4_val
  -- chain block 5
  obtain ⟨st5_val, st5_norm⟩ := h_c5
    ⟨st4_norm,
     (by intro i
         have h := paddedBlock_normalized env pvar h_bool' 4 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 4) i.val i.isLt])⟩
  rw [st4_val, block_val 4] at st5_val
  -- digest via SelectDigest spec
  have h_sd_spec := h_sd ⟨h_len_lt, h_onehot, by
    intro k i
    -- statesVec[k][i] is one of st1..st5, all normalized
    fin_cases k
    · exact st1_norm i
    · exact st2_norm i
    · exact st3_norm i
    · exact st4_norm i
    · exact st5_norm i⟩
  -- Finish
  rw [Specs.SHA256.Spec, dif_pos (le_of_lt h_len_assum)]
  apply Vector.ext
  intro w hw
  simp only [fieldElemsToNat, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  rw [h_sd_spec ⟨w, hw⟩]
  refine digest_final _ msg ℓ (le_of_lt h_len_assum) (fun k => ?_) ⟨w, hw⟩ hw
  fin_cases k
  · exact st1_val
  · exact st2_val
  · exact st3_val
  · exact st4_val
  · exact st5_val

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      ProverAssumptions ProverSpec := by
  circuit_proof_start
  obtain ⟨h_pad_env, h_flags_env, h_c1, h_c2, h_c3, h_c4, h_c5, _h_sd⟩ := h_env
  obtain ⟨⟨h_msg_assum, h_len_assum⟩, _h_pad_zeros⟩ := h_assumptions
  obtain ⟨h_msg_eq, h_msgLen_eq⟩ := h_input
  set msg := Vector.map ZMod.val input_message with hmsg
  set ℓ := ZMod.val input_messageLen with hℓ
  set pvar : Var SHA256PaddedBits (F circomPrime) :=
    Vector.mapRange paddedBitsLen fun i => var { index := i₀ + i } with hpvar
  set fvar : Var (fields inputBufferLen) (F circomPrime) :=
    Vector.mapRange inputBufferLen fun i => var { index := i₀ + paddedBitsLen + i } with hfvar
  have hb : eval env input_var_message = input_message := by
    rw [CircuitType.eval_var_fields_prover]; exact h_msg_eq
  have hbwit : paddedBitsWitness { message := input_var_message, messageLen := input_var_messageLen } env
      = paddedBitsValue msg ℓ := by
    simp only [paddedBitsWitness]
    rw [hb, h_msgLen_eq]
  have hfwit : lenFlagsWitness { message := input_var_message, messageLen := input_var_messageLen } env
      = lenFlagsValue ℓ := by
    simp only [lenFlagsWitness]
    rw [h_msgLen_eq]
  -- padded witness evaluates to paddedBitsValue msg ℓ
  have h_pad_val : Vector.map (Expression.eval env.toEnvironment) pvar = paddedBitsValue msg ℓ := by
    rw [← hbwit]
    apply Vector.ext
    intro i hi
    rw [hpvar, Vector.getElem_map, Vector.getElem_mapRange]
    rw [show Expression.eval env.toEnvironment (var { index := i₀ + i }) = env.get (i₀ + i) from rfl]
    exact h_pad_env ⟨i, hi⟩
  -- lenFlags witness evaluates to lenFlagsValue ℓ
  have h_flags_val : Vector.map (Expression.eval env.toEnvironment) fvar = lenFlagsValue ℓ := by
    rw [← hfwit]
    apply Vector.ext
    intro i hi
    rw [hfvar, Vector.getElem_map, Vector.getElem_mapRange]
    rw [show Expression.eval env.toEnvironment (var { index := i₀ + paddedBitsLen + i }) = env.get (i₀ + paddedBitsLen + i) from rfl]
    exact h_flags_env ⟨i, hi⟩
  -- message bytes < 256
  have h_msg256 : ∀ i : Fin inputBufferLen, msg[i] < 256 := by
    intro i; have := h_msg_assum i
    simpa [hmsg, fieldElemsToNat, Vector.getElem_map] using this
  -- booleanity of evaluated padded bits
  have h_bool' : ∀ i : Fin paddedBitsLen, IsBool (Vector.map (Expression.eval env.toEnvironment) pvar)[i] := by
    intro i; rw [h_pad_val]; exact paddedBitsValue_isBool msg ℓ i
  -- per-byte spec equation
  have h_byte_eq' : ∀ j : Fin paddedBytesLen,
      paddedByteVal (Vector.map (Expression.eval env.toEnvironment) pvar) j = specPaddedByte msg ℓ j.val := by
    intro j; rw [h_pad_val]; exact paddedByteVal_paddedBitsValue msg h_msg256 ℓ j
  -- CheckPad message bytes assumption (in input_message form)
  have h_cp_assum : ∀ i : Fin inputBufferLen, ZMod.val input_message[i.val] < 256 := by
    intro i; have := h_msg_assum i; simpa [fieldElemsToNat, Vector.getElem_map] using this
  -- CheckPad Assumptions (bytes) and Spec
  have h_cp_assum_goal : CheckPad.Assumptions
      { messageLen := input_messageLen, message := input_message,
        lenFlags := Vector.map (Expression.eval env.toEnvironment) fvar,
        padded := Vector.map (Expression.eval env.toEnvironment) pvar } := h_cp_assum
  have h_cp_spec_goal : CheckPad.Spec
      { messageLen := input_messageLen, message := input_message,
        lenFlags := Vector.map (Expression.eval env.toEnvironment) fvar,
        padded := Vector.map (Expression.eval env.toEnvironment) pvar } := by
    refine ⟨h_len_assum, ?_, ?_, ?_⟩
    · rw [h_flags_val]; exact lenFlagsValue_oneHotAt ℓ
    · exact h_bool'
    · exact h_byte_eq'
  -- block normalization antecedents (inline, concrete indices) and chaining
  obtain ⟨_, st1_norm⟩ := h_c1
    ⟨(by intro i; exact state0_normalized env.toEnvironment i.val i.isLt),
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 0 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 0) i.val i.isLt])⟩
  obtain ⟨_, st2_norm⟩ := h_c2
    ⟨st1_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 1 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 1) i.val i.isLt])⟩
  obtain ⟨_, st3_norm⟩ := h_c3
    ⟨st2_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 2 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 2) i.val i.isLt])⟩
  obtain ⟨_, st4_norm⟩ := h_c4
    ⟨st3_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 3 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 3) i.val i.isLt])⟩
  obtain ⟨_, st5_norm⟩ := h_c5
    ⟨st4_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 4 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 4) i.val i.isLt])⟩
  -- assemble the goal
  refine ⟨⟨h_cp_assum_goal, h_cp_spec_goal⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Compress1 Assumptions
    exact ⟨(by intro i; exact state0_normalized env.toEnvironment i.val i.isLt),
      (by intro i
          rw [Fin.getElem_fin]
          have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 0 i.val i.isLt
          rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 0) i.val i.isLt])⟩
  · exact ⟨st1_norm,
      (by intro i
          rw [Fin.getElem_fin]
          have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 1 i.val i.isLt
          rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 1) i.val i.isLt])⟩
  · exact ⟨st2_norm,
      (by intro i
          rw [Fin.getElem_fin]
          have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 2 i.val i.isLt
          rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 2) i.val i.isLt])⟩
  · exact ⟨st3_norm,
      (by intro i
          rw [Fin.getElem_fin]
          have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 3 i.val i.isLt
          rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 3) i.val i.isLt])⟩
  · exact ⟨st4_norm,
      (by intro i
          rw [Fin.getElem_fin]
          have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 4 i.val i.isLt
          rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 4) i.val i.isLt])⟩
  · -- SelectDigest Assumptions
    refine ⟨h_len_assum, ?_, ?_⟩
    · rw [h_flags_val]; exact lenFlagsValue_oneHotAt ℓ
    · intro k i
      fin_cases k
      · exact st1_norm i
      · exact st2_norm i
      · exact st3_norm i
      · exact st4_norm i
      · exact st5_norm i

attribute [local irreducible] main CheckPad.circuit CompressBlock.circuit SelectDigest.circuit

private theorem checkPadComputableWitnesses :
    (CheckPad.circuit (p := circomPrime)).ComputableWitnesses :=
  CheckPad.computableWitnesses

private theorem compressBlockComputableWitnesses :
    (CompressBlock.circuit (p := circomPrime)).ComputableWitnesses :=
  CompressBlock.computableWitnesses

private theorem selectDigestComputableWitnesses :
    (SelectDigest.circuit (p := circomPrime)).ComputableWitnesses :=
  SelectDigest.computableWitnesses

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := by
  intro n input hinput env env'
  change (main input).operations n |>.forAllFlat n
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  have hstruct :
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        input env env' n ((main input).operations n) := by
    unfold main
    let paddedCircuit : Circuit (F circomPrime) (Var SHA256PaddedBits (F circomPrime)) :=
      witnessVector paddedBitsLen (paddedBitsWitness input)
    let padded := paddedCircuit.output n
    let lenFlagsOffset := n + paddedCircuit.localLength n
    let lenFlagsCircuit : Circuit (F circomPrime) (Var (fields inputBufferLen) (F circomPrime)) :=
      witnessVector inputBufferLen (lenFlagsWitness input)
    let lenFlags := lenFlagsCircuit.output lenFlagsOffset
    let checkPadOffset := lenFlagsOffset + lenFlagsCircuit.localLength lenFlagsOffset
    let state0 : Var SHA256State (F circomPrime) :=
      Vector.ofFn fun i => constWord32 Specs.SHA256.H0[i]
    let state1Circuit : Circuit (F circomPrime) (Var SHA256State (F circomPrime)) :=
      CompressBlock.circuit ⟨state0, paddedBlock padded 0⟩
    let state1Offset := checkPadOffset +
      (assertion CheckPad.circuit ⟨input.messageLen, input.message, lenFlags, padded⟩).localLength
        checkPadOffset
    let state1 := state1Circuit.output state1Offset
    let state2Circuit : Circuit (F circomPrime) (Var SHA256State (F circomPrime)) :=
      CompressBlock.circuit ⟨state1, paddedBlock padded 1⟩
    let state2Offset := state1Offset + state1Circuit.localLength state1Offset
    let state2 := state2Circuit.output state2Offset
    let state3Circuit : Circuit (F circomPrime) (Var SHA256State (F circomPrime)) :=
      CompressBlock.circuit ⟨state2, paddedBlock padded 2⟩
    let state3Offset := state2Offset + state2Circuit.localLength state2Offset
    let state3 := state3Circuit.output state3Offset
    let state4Circuit : Circuit (F circomPrime) (Var SHA256State (F circomPrime)) :=
      CompressBlock.circuit ⟨state3, paddedBlock padded 3⟩
    let state4Offset := state3Offset + state3Circuit.localLength state3Offset
    let state4 := state4Circuit.output state4Offset
    let state5Circuit : Circuit (F circomPrime) (Var SHA256State (F circomPrime)) :=
      CompressBlock.circuit ⟨state4, paddedBlock padded 4⟩
    let state5Offset := state4Offset + state4Circuit.localLength state4Offset
    let state5 := state5Circuit.output state5Offset
    let digestOffset := state5Offset + state5Circuit.localLength state5Offset
    let block0 : Fin paddedBlocksLen := 0
    let block1 : Fin paddedBlocksLen := 1
    let block2 : Fin paddedBlocksLen := 2
    let block3 : Fin paddedBlocksLen := 3
    let block4 : Fin paddedBlocksLen := 4
    have h_checkPad := checkPadComputableWitnesses
    have h_compressBlock := compressBlockComputableWitnesses
    have h_selectDigest := selectDigestComputableWitnesses
    have h_padded_before_state1 : n + paddedBitsLen ≤ state1Offset := by
      have hpadded_len : paddedCircuit.localLength n = paddedBitsLen := rfl
      dsimp [state1Offset, checkPadOffset, lenFlagsOffset]
      rw [hpadded_len]
      omega
    have h_padded_before_state2 : n + paddedBitsLen ≤ state2Offset := by
      dsimp [state2Offset]
      omega
    have h_padded_before_state3 : n + paddedBitsLen ≤ state3Offset := by
      dsimp [state3Offset]
      omega
    have h_padded_before_state4 : n + paddedBitsLen ≤ state4Offset := by
      dsimp [state4Offset]
      omega
    have h_padded_before_state5 : n + paddedBitsLen ≤ state5Offset := by
      dsimp [state5Offset]
      omega
    have h_lenFlags_before_digest : lenFlagsOffset + inputBufferLen ≤ digestOffset := by
      have hlen_len : lenFlagsCircuit.localLength lenFlagsOffset = inputBufferLen := rfl
      dsimp [digestOffset, state5Offset, state4Offset, state3Offset, state2Offset,
        state1Offset, checkPadOffset]
      rw [hlen_len]
      omega
    have h_state1_len :
        state1Circuit.localLength state1Offset = 48 * 227 + 64 * 455 + 8 * 33 := by
      simp [state1Circuit, CompressBlock.circuit, circuit_norm]
    have h_state2_len :
        state2Circuit.localLength state2Offset = 48 * 227 + 64 * 455 + 8 * 33 := by
      simp [state2Circuit, CompressBlock.circuit, circuit_norm]
    have h_state3_len :
        state3Circuit.localLength state3Offset = 48 * 227 + 64 * 455 + 8 * 33 := by
      simp [state3Circuit, CompressBlock.circuit, circuit_norm]
    have h_state4_len :
        state4Circuit.localLength state4Offset = 48 * 227 + 64 * 455 + 8 * 33 := by
      simp [state4Circuit, CompressBlock.circuit, circuit_norm]
    have h_state5_len :
        state5Circuit.localLength state5Offset = 48 * 227 + 64 * 455 + 8 * 33 := by
      simp [state5Circuit, CompressBlock.circuit, circuit_norm]
    have h_state1_end_before_state2 :
        state1Offset + (48 * 227 + 64 * 455 + 8 * 33) ≤ state2Offset := by
      dsimp [state2Offset]
      rw [h_state1_len]
    have h_state2_end_before_state3 :
        state2Offset + (48 * 227 + 64 * 455 + 8 * 33) ≤ state3Offset := by
      dsimp [state3Offset]
      rw [h_state2_len]
    have h_state3_end_before_state4 :
        state3Offset + (48 * 227 + 64 * 455 + 8 * 33) ≤ state4Offset := by
      dsimp [state4Offset]
      rw [h_state3_len]
    have h_state4_end_before_state5 :
        state4Offset + (48 * 227 + 64 * 455 + 8 * 33) ≤ state5Offset := by
      dsimp [state5Offset]
      rw [h_state4_len]
    have h_state5_end_before_digest :
        state5Offset + (48 * 227 + 64 * 455 + 8 * 33) ≤ digestOffset := by
      dsimp [digestOffset]
      rw [h_state5_len]
    have h_state2_before_state3 : state2Offset ≤ state3Offset := by
      dsimp [state3Offset]
      omega
    have h_state3_before_state4 : state3Offset ≤ state4Offset := by
      dsimp [state4Offset]
      omega
    have h_state4_before_state5 : state4Offset ≤ state5Offset := by
      dsimp [state5Offset]
      omega
    have h_state5_before_digest : state5Offset ≤ digestOffset := by
      exact le_trans (by omega : state5Offset ≤ state5Offset + (48 * 227 + 64 * 455 + 8 * 33))
        h_state5_end_before_digest
    simp only [
      Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
      and_true]
    and_intros
    · intro _ h_input_eq
      simp only [paddedBitsWitness]
      have h_msg : eval env input.message = eval env' input.message := by
        simpa [circuit_norm] using congrArg (fun x : Input (F circomPrime) => x.message) h_input_eq
      have h_len : Expression.eval env.toEnvironment input.messageLen =
          Expression.eval env'.toEnvironment input.messageLen := by
        simpa [circuit_norm] using congrArg (fun x : Input (F circomPrime) => x.messageLen) h_input_eq
      rw [h_msg, h_len]
    · intro _ h_input_eq
      simp only [lenFlagsWitness]
      have h_len : Expression.eval env.toEnvironment input.messageLen =
          Expression.eval env'.toEnvironment input.messageLen := by
        simpa [circuit_norm] using congrArg (fun x : Input (F circomPrime) => x.messageLen) h_input_eq
      rw [h_len]
    · exact @Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        (F circomPrime) _ Input CheckPad.Inputs _ _
        CheckPad.circuit input ⟨input.messageLen, input.message, lenFlags, padded⟩ checkPadOffset
        (by
          intro k env env' hle h_agree h_input_eq
          simp [circuit_norm] at h_input_eq ⊢
          refine ⟨h_input_eq.2, h_input_eq.1, ?_, ?_⟩
          · exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
              (offset := lenFlagsOffset) (m := inputBufferLen) h_agree (by
                simp [checkPadOffset, lenFlagsCircuit, circuit_norm] at hle ⊢
                omega)
          · exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
              (offset := n) (m := paddedBitsLen) h_agree (by
                simp [checkPadOffset, lenFlagsOffset, paddedCircuit, lenFlagsCircuit,
                  circuit_norm] at hle ⊢
                omega))
        h_checkPad env env'
    · refine @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (F circomPrime) _ Input CompressBlock.Inputs SHA256State _ _ _
        CompressBlock.circuit input ⟨state0, paddedBlock padded 0⟩ state1Offset ?_ h_compressBlock env env'
      ·
          intro k env env' hle h_agree h_input_eq
          simp [circuit_norm] at h_input_eq ⊢
          constructor
          · apply Vector.ext
            intro i hi
            rw [← getElem_eval_vector (α := fields 32) env.toEnvironment state0 i hi,
              ← getElem_eval_vector (α := fields 32) env'.toEnvironment state0 i hi]
            apply Vector.ext
            intro bit hbit
            rw [← ProvableType.getElem_eval_fields env.toEnvironment (state0[i]'hi) bit hbit,
              ← ProvableType.getElem_eval_fields env'.toEnvironment (state0[i]'hi) bit hbit]
            simp only [state0]
            rw [Vector.getElem_ofFn]
            simp [constWord32, Expression.eval]
          · apply Vector.ext
            intro w hw
            have hblock := paddedBlock_varFromOffset_eval_eq_of_agreesBelow
              (offset := n) h_agree (le_trans h_padded_before_state1 hle)
              block0
            have hblock' :
                eval env.toEnvironment (paddedBlock padded 0) =
                  eval env'.toEnvironment (paddedBlock padded 0) := by
              simpa [padded, paddedCircuit, Circuit.witnessVector, circuit_norm] using hblock
            simpa [getElem_eval_vector] using
              congrArg (fun block : SHA256Block (F circomPrime) => block[w]'hw) hblock'
    · refine @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (F circomPrime) _ Input CompressBlock.Inputs SHA256State _ _ _
        CompressBlock.circuit input ⟨state1, paddedBlock padded 1⟩ state2Offset ?_
        h_compressBlock env env'
      ·
          intro k env env' hle h_agree h_input_eq
          simp [circuit_norm] at h_input_eq ⊢
          constructor
          · simpa [state1, state1Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state0, paddedBlock padded 0⟩
                (ProverEnvironment.agreesBelow_of_le h_agree
                  (le_trans h_state1_end_before_state2 hle))
          · show eval env.toEnvironment (paddedBlock padded 1) =
              eval env'.toEnvironment (paddedBlock padded 1)
            simpa [padded, paddedCircuit, Circuit.witnessVector, circuit_norm] using
              (paddedBlock_varFromOffset_eval_eq_of_agreesBelow
                (offset := n) h_agree (le_trans h_padded_before_state2 hle)
                block1)
    · refine @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (F circomPrime) _ Input CompressBlock.Inputs SHA256State _ _ _
        CompressBlock.circuit input ⟨state2, paddedBlock padded 2⟩ state3Offset ?_
        h_compressBlock env env'
      ·
          intro k env env' hle h_agree h_input_eq
          simp [circuit_norm] at h_input_eq ⊢
          constructor
          · simpa [state2, state2Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state1, paddedBlock padded 1⟩
                (ProverEnvironment.agreesBelow_of_le h_agree
                  (le_trans h_state2_end_before_state3 hle))
          · simpa [padded, paddedCircuit, Circuit.witnessVector, circuit_norm] using
              paddedBlock_varFromOffset_eval_eq_of_agreesBelow
                (offset := n) h_agree (le_trans h_padded_before_state3 hle)
                block2
    · refine @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (F circomPrime) _ Input CompressBlock.Inputs SHA256State _ _ _
        CompressBlock.circuit input ⟨state3, paddedBlock padded 3⟩ state4Offset ?_
        h_compressBlock env env'
      ·
          intro k env env' hle h_agree h_input_eq
          simp [circuit_norm] at h_input_eq ⊢
          constructor
          · simpa [state3, state3Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state2, paddedBlock padded 2⟩
                (ProverEnvironment.agreesBelow_of_le h_agree
                  (le_trans h_state3_end_before_state4 hle))
          · simpa [padded, paddedCircuit, Circuit.witnessVector, circuit_norm] using
              paddedBlock_varFromOffset_eval_eq_of_agreesBelow
                (offset := n) h_agree (le_trans h_padded_before_state4 hle)
                block3
    · refine @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (F circomPrime) _ Input CompressBlock.Inputs SHA256State _ _ _
        CompressBlock.circuit input ⟨state4, paddedBlock padded 4⟩ state5Offset ?_
        h_compressBlock env env'
      ·
          intro k env env' hle h_agree h_input_eq
          simp [circuit_norm] at h_input_eq ⊢
          constructor
          · simpa [state4, state4Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state3, paddedBlock padded 3⟩
                (ProverEnvironment.agreesBelow_of_le h_agree
                  (le_trans h_state4_end_before_state5 hle))
          · simpa [padded, paddedCircuit, Circuit.witnessVector, circuit_norm] using
              paddedBlock_varFromOffset_eval_eq_of_agreesBelow
                (offset := n) h_agree (le_trans h_padded_before_state5 hle)
                block4
    · refine @Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (F circomPrime) _ Input SelectDigest.Inputs (fields 8) _ _ _
        SelectDigest.circuit input ⟨input.messageLen, lenFlags, state1, state2, state3, state4, state5⟩
        digestOffset ?_ h_selectDigest env env'
      ·
          intro k env env' hle h_agree h_input_eq
          simp [circuit_norm] at h_input_eq ⊢
          refine ⟨h_input_eq.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
              (offset := lenFlagsOffset) (m := inputBufferLen) h_agree (by
                exact le_trans h_lenFlags_before_digest hle)
          · simpa [state1, state1Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state0, paddedBlock padded 0⟩
                (ProverEnvironment.agreesBelow_of_le h_agree (by
                  exact le_trans
                    (le_trans h_state1_end_before_state2
                      (le_trans h_state2_before_state3
                        (le_trans h_state3_before_state4
                          (le_trans h_state4_before_state5 h_state5_before_digest))))
                    hle))
          · simpa [state2, state2Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state1, paddedBlock padded 1⟩
                (ProverEnvironment.agreesBelow_of_le h_agree (by
                  exact le_trans
                    (le_trans h_state2_end_before_state3
                      (le_trans h_state3_before_state4
                        (le_trans h_state4_before_state5 h_state5_before_digest)))
                    hle))
          · simpa [state3, state3Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state2, paddedBlock padded 2⟩
                (ProverEnvironment.agreesBelow_of_le h_agree (by
                  exact le_trans
                    (le_trans h_state3_end_before_state4
                      (le_trans h_state4_before_state5 h_state5_before_digest))
                    hle))
          · simpa [state4, state4Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state3, paddedBlock padded 3⟩
                (ProverEnvironment.agreesBelow_of_le h_agree (by
                  exact le_trans
                    (le_trans h_state4_end_before_state5 h_state5_before_digest)
                    hle))
          · simpa [state5, state5Circuit] using
              Solution.SHA256.CompressBlock.eval_circuit_output_of_agreesBelow
                ⟨state4, paddedBlock padded 4⟩
                (ProverEnvironment.agreesBelow_of_le h_agree
                  (le_trans h_state5_end_before_digest hle))
  have hflat :=
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
      input env env' hstruct
  unfold Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition at hflat
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  let targetCondition : Condition (F circomPrime) :=
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  apply FlatOperation.forAll_implies (F := F circomPrime) n ?_ hflat
  have himplies : ∀ (ops : List (FlatOperation (F circomPrime))) (off : ℕ),
      n ≤ off →
      FlatOperation.forAll off
        (Condition.implies
          (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
            input env env')
          targetCondition).ignoreSubcircuit
        ops := by
    intro ops off hoff
    induction ops generalizing off with
    | nil => simp [FlatOperation.forAll]
    | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          constructor
          · intro hparent hagree
            exact hparent hagree
              (hinput env env' (ProverEnvironment.agreesBelow_of_le hagree hoff))
          · exact ih (m + off) (by omega)
      | assert e =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | lookup l =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | interact i =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
  exact himplies ((main input).operations n).toFlat n (le_refl n)

end

section
open Challenge.CostR1CS
open Solution.SHA256.Cost

-- `maxRecDepth` controls elaboration stack depth only (not the trusted base and
-- not the heartbeat budget); the deep `do`-blocks here need more than the default.
set_option maxRecDepth 8000

-- Keep the trusted R1CS predicates opaque while *applying* the per-gadget
-- certificates (see `Cost.lean`): otherwise the unifier evaluates `r1csProducts`
-- on the asserted expressions and loops on neutral subterms.
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-! ### Structural cost of the top-level circuit

The per-gadget cost / R1CS leaves live in `Cost.lean`; here we just assemble
`main`'s total count and its single-row R1CS certificate by structural recursion
over `main`'s own `do`-block (no `native_decide`, no `decide`). -/

@[reducible] def allocations : Nat := 204224
@[reducible] def constraints : Nat := 209586

theorem mainCost :
    circuitCost main ⟨allocations, constraints⟩ :=
  fun input =>
  (CostIs.bind (CostIs.witnessVector paddedBitsLen _) fun _ =>
    CostIs.bind (CostIs.witnessVector inputBufferLen _) fun _ =>
    CostIs.bind (Cost.costIs_sub_checkPad _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlock _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlock _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlock _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlock _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlock _) fun _ =>
    CostIs.bind (Cost.costIs_sub_selectDigest _) fun _ =>
    CostIs.pure _
      : CostIs (main input) ⟨allocations, constraints⟩)

/-- Structural single-row R1CS certificate for the circuit *family* `main`,
for every affine symbolic input. Each assert is an affine combination (or
`A·B`/`A·B−C` of affine forms), threaded through the affine message + length
inputs and the witnessed affine padded bits, length flags and compress-block
outputs. -/
theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
  (fun input hinput => by
    refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector paddedBitsLen _) fun npad => ?_
    refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector inputBufferLen _) fun nflags => ?_
    have hpadded : AffineW
        ((Circuit.witnessVector paddedBitsLen
          (paddedBitsWitness input)).output npad) :=
      affineW_witnessVector_output _ _ _
    have hflags : AffineW
        ((Circuit.witnessVector inputBufferLen
          (lenFlagsWitness input)).output nflags) :=
      affineW_witnessVector_output _ _ _
    refine IsR1CSCirc.bind
      (Cost.r1cs_sub_checkPad _ (Cost.affine_input_messageLen input hinput)
        (Cost.affineW_input_message input hinput) hflags hpadded) fun _ => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlock _ Cost.affineW_state0
        (Cost.affineW_paddedBlock _ hpadded 0)) fun n1 => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlock _ (Cost.affineW_subOut_compressBlock _ n1)
        (Cost.affineW_paddedBlock _ hpadded 1)) fun n2 => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlock _ (Cost.affineW_subOut_compressBlock _ n2)
        (Cost.affineW_paddedBlock _ hpadded 2)) fun n3 => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlock _ (Cost.affineW_subOut_compressBlock _ n3)
        (Cost.affineW_paddedBlock _ hpadded 3)) fun n4 => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlock _ (Cost.affineW_subOut_compressBlock _ n4)
        (Cost.affineW_paddedBlock _ hpadded 4)) fun n5 => ?_
    refine IsR1CSCirc.bind (Cost.r1cs_selectDigest _ hflags ?_) fun _ => ?_
    · intro k hk j hj
      have hpad : paddedBlocksLen = 5 := rfl
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with
        rfl | rfl | rfl | rfl | rfl
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlock _ n1 j hj
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlock _ n2 j hj
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlock _ n3 j hj
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlock _ n4 j hj
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlock _ n5 j hj
    exact IsR1CSCirc.pure _)
  (fun input hinput n => by
    intro i hi
    have hi8 : i < 8 := by
      have hsz : size Output = 8 := rfl
      omega
    change Affine (((main input).output n).digest[i])
    simp only [main, Circuit.bind_output_eq, Circuit.pure_output_eq]
    exact Cost.affineW_subOut_selectDigest _ _ i hi8)

end

end Solution.SHA256
