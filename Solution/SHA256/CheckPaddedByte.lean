import Solution.SHA256.PaddingTheorems
import Solution.SHA256.CheckPaddedByteTheorems

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256

/-!
# Padding-byte check (loop body)

A `FormalAssertion` family, one per byte index `j : Fin paddedBytesLen`, asserting
that byte `j % 4` of the witnessed 32-bit `word` equals the expected padded byte
at position `j` for the claimed message and length, selected via the one-hot
`lenFlags`.
-/

namespace CheckPaddedByte

open Challenge.Instances.SHA256.Interface (inputBufferLen)

structure Inputs (F : Type) where
  messageLen : F
  message : fields inputBufferLen F
  lenFlags : fields inputBufferLen F
  word : fields 32 F
deriving ProvableStruct

def main (j : Fin paddedBytesLen) (input : Var Inputs (F p)) : Circuit (F p) Unit :=
  assertZero (byteFromWord input.word ⟨j.val % 4, by omega⟩ -
    expectedPaddedByte input.message input.lenFlags j)

instance elaborated (j : Fin paddedBytesLen) :
    ElaboratedCircuit (F p) Inputs unit (main j) := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin inputBufferLen, input.message[i].val < 256) ∧
  input.messageLen.val < inputBufferLen ∧
  OneHotAt input.lenFlags input.messageLen.val ∧
  (∀ t : Fin 32, IsBool input.word[t])

def Spec (j : Fin paddedBytesLen) (input : Inputs (F p)) : Prop :=
  wordByteVal input.word ⟨j.val % 4, by omega⟩ =
    specPaddedByte (input.message.map ZMod.val) input.messageLen.val j.val

/-! ## Helper lemmas

Gadget-private lemmas live in `CheckPaddedByteTheorems`. -/

/-! ## Soundness and completeness -/

theorem soundness (j : Fin paddedBytesLen) :
    FormalAssertion.Soundness (F p) (main j) Assumptions (Spec j) := by
  circuit_proof_start [main]
  obtain ⟨h_bytes, h_len, h_onehot, h_word⟩ := h_assumptions
  obtain ⟨_, h_msg_eq, h_flags_eq, h_word_eq⟩ := h_input
  set ℓ := input_messageLen.val with hℓ
  have hℓ_lt : ℓ < inputBufferLen := h_len
  -- one-hot on the evaluated lenFlags variable
  have h_onehot' : OneHotAt (Vector.map (Expression.eval env) input_var_lenFlags) ℓ := by
    rw [h_flags_eq]; exact h_onehot
  -- the constraint as a field equation
  have h_eq : Expression.eval env (byteFromWord input_var_word ⟨j.val % 4, by omega⟩) =
      Expression.eval env (expectedPaddedByte input_var_message input_var_lenFlags j) := by
    have := h_holds
    rw [add_neg_eq_zero] at this
    exact this
  rw [eval_byteFromWord, eval_expectedPaddedByte env _ _ j ℓ hℓ_lt h_onehot'] at h_eq
  rw [h_word_eq] at h_eq
  -- both sides are casts of naturals < 256
  by_cases h : j.val < ℓ
  · -- message branch
    have hj2 : j.val < inputBufferLen := Nat.lt_trans h hℓ_lt
    rw [dif_pos h] at h_eq
    -- the message entry equals the cast of its val
    have hmsg_val : (Vector.map (Expression.eval env) input_var_message)[j.val]'hj2 =
        ((input_message[j.val]'hj2).val : F p) := by
      rw [h_msg_eq]
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [hmsg_val] at h_eq
    have hlt_word : wordByteVal input_word ⟨j.val % 4, by omega⟩ < 256 :=
      wordByteVal_lt input_word ⟨j.val % 4, by omega⟩ h_word
    have hlt_msg : (input_message[j.val]'hj2).val < 256 := h_bytes ⟨j.val, hj2⟩
    have hnat := natCast_inj_lt_256 hlt_word hlt_msg h_eq
    rw [hnat]
    unfold specPaddedByte
    rw [dif_pos ⟨h, hj2⟩, Vector.getElem_map]
    rfl
  · -- constant branch
    rw [dif_neg h] at h_eq
    have hlt_word : wordByteVal input_word ⟨j.val % 4, by omega⟩ < 256 :=
      wordByteVal_lt input_word ⟨j.val % 4, by omega⟩ h_word
    have hlt_const : specPaddedByteConst ℓ j.val < 256 := specPaddedByteConst_lt ℓ j.val
    have hnat := natCast_inj_lt_256 hlt_word hlt_const h_eq
    rw [hnat]
    unfold specPaddedByte
    rw [dif_neg (by intro hc; exact h hc.1)]

omit h_large in
theorem completeness (j : Fin paddedBytesLen) :
    FormalAssertion.Completeness (F p) (main j) Assumptions (Spec j) := by
  circuit_proof_start [main]
  obtain ⟨h_bytes, h_len, h_onehot, h_word⟩ := h_assumptions
  obtain ⟨_, h_msg_eq, h_flags_eq, h_word_eq⟩ := h_input
  set ℓ := input_messageLen.val with hℓ
  have hℓ_lt : ℓ < inputBufferLen := h_len
  have h_onehot' : OneHotAt (Vector.map (Expression.eval env.toEnvironment) input_var_lenFlags) ℓ := by
    rw [h_flags_eq]; exact h_onehot
  rw [add_neg_eq_zero]
  rw [eval_byteFromWord, eval_expectedPaddedByte env.toEnvironment _ _ j ℓ hℓ_lt h_onehot']
  rw [h_word_eq]
  -- it suffices to show the two casts agree at the nat level
  by_cases h : j.val < ℓ
  · have hj2 : j.val < inputBufferLen := Nat.lt_trans h hℓ_lt
    rw [dif_pos h]
    have hmsg_val : (Vector.map (Expression.eval env.toEnvironment) input_var_message)[j.val]'hj2 =
        ((input_message[j.val]'hj2).val : F p) := by
      rw [h_msg_eq, ZMod.natCast_val, ZMod.cast_id]
    rw [hmsg_val]
    congr 1
    rw [h_spec]
    unfold specPaddedByte
    rw [dif_pos ⟨h, hj2⟩, Vector.getElem_map]
    rfl
  · rw [dif_neg h]
    congr 1
    rw [h_spec]
    unfold specPaddedByte
    rw [dif_neg (by intro hc; exact h hc.1)]

def circuit (j : Fin paddedBytesLen) : FormalAssertion (F p) Inputs :=
  { main := main j, elaborated := elaborated j, Assumptions, Spec := Spec j,
    soundness := soundness j, completeness := completeness j,
    exposedChannels_eq := by intro _ _ exposed h; simp at h }

end CheckPaddedByte
end Solution.SHA256
end
