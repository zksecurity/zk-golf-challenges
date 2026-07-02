import Challenge.Instances.SHA256.Interface
import Solution.SHA256.Cost
import Solution.SHA256.CompressBlock
import Solution.SHA256.CheckPad
import Solution.SHA256.SelectDigest
import Solution.SHA256.PaddingTheorems
import Solution.SHA256.MainTheorems
import Challenge.Utils.CostR1CS

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
  simp only [fieldElemsToNat, Vector.getElem_map]
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

@[reducible] def allocations : Nat := 204216
@[reducible] def constraints : Nat := 207538

theorem mainCost :
    circuitCount (main default) = ⟨allocations, constraints⟩ :=
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
      : CostIs (main default) ⟨allocations, constraints⟩) 0

/-- Structural single-row R1CS certificate for the circuit *family* `main`,
allocating the inputs as variables at offset 0 (as `isR1CS` requires). Each assert
is an affine combination (or `A·B`/`A·B−C` of affine forms), threaded through the
symbolic (affine) message + length inputs and the witnessed (affine) padded bits,
length flags and compress-block outputs. -/
theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc (by
    refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector paddedBitsLen _) fun npad => ?_
    refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector inputBufferLen _) fun nflags => ?_
    have hpadded : AffineW
        ((Circuit.witnessVector paddedBitsLen
          (paddedBitsWitness (varFromOffset Input 0))).output npad) :=
      affineW_witnessVector_output _ _ _
    have hflags : AffineW
        ((Circuit.witnessVector inputBufferLen
          (lenFlagsWitness (varFromOffset Input 0))).output nflags) :=
      affineW_witnessVector_output _ _ _
    refine IsR1CSCirc.bind
      (Cost.r1cs_sub_checkPad _ Cost.affine_input_messageLen Cost.affineW_input_message
        hflags hpadded) fun _ => ?_
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
    refine IsR1CSCirc.bind
      (Cost.r1cs_sub_compressBlock _ (Cost.affineW_subOut_compressBlock _ n4)
        (Cost.affineW_paddedBlock _ hpadded 4)) fun _ => ?_
    refine IsR1CSCirc.bind (Cost.r1cs_selectDigest _) fun _ => ?_
    exact IsR1CSCirc.pure _)

end

end Solution.SHA256
