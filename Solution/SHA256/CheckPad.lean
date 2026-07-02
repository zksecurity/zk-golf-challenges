import Solution.SHA256.CheckLenFlags
import Solution.SHA256.BitsBool
import Solution.SHA256.CheckPaddedByte

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256

instance : Fact (p > 2) := .mk (by
  have h : (2 : ℕ) < 2^33 := by norm_num
  exact h.trans h_large.out)

namespace CheckPad

open Challenge.Instances.SHA256.Interface (inputBufferLen)

/-!
# Padding-check composition

A `FormalAssertion` bundling the three padding sub-assertions:
* `CheckLenFlags` — `lenFlags` is the one-hot indicator of `messageLen`,
* `BitsBool` over the whole flat `padded` bit-vector — every padded bit is boolean,
* a `Fin paddedBytesLen` family of `CheckPaddedByte` — each padded byte equals the
  spec padded byte for the message and length.

Soundness needs only that the message bytes are `< 256`; the spec then certifies
length-bound, one-hotness, booleanity and the per-byte padding equation.
-/

structure Inputs (F : Type) where
  messageLen : F
  message : fields inputBufferLen F
  lenFlags : fields inputBufferLen F
  padded : fields paddedBitsLen F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) Unit := do
  CheckLenFlags.circuit (p := p) ⟨input.messageLen, input.lenFlags⟩
  BitsBool.circuit paddedBitsLen input.padded
  Circuit.forEach (Vector.finRange paddedBytesLen) fun j =>
    CheckPaddedByte.circuit j
      ⟨input.messageLen, input.message, input.lenFlags, paddedWord input.padded j⟩

instance elaborated : ElaboratedCircuit (F p) Inputs unit main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  ∀ i : Fin inputBufferLen, input.message[i].val < 256

def Spec (input : Inputs (F p)) : Prop :=
  input.messageLen.val < inputBufferLen ∧
  OneHotAt input.lenFlags input.messageLen.val ∧
  (∀ i : Fin paddedBitsLen, IsBool input.padded[i]) ∧
  (∀ j : Fin paddedBytesLen, paddedByteVal input.padded j =
     specPaddedByte (input.message.map ZMod.val) input.messageLen.val j.val)

/-! ## Soundness and completeness -/

theorem soundness : FormalAssertion.Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [CheckLenFlags.circuit, CheckLenFlags.Spec, CheckLenFlags.Assumptions,
    BitsBool.circuit, BitsBool.Spec,
    CheckPaddedByte.circuit, CheckPaddedByte.Spec, CheckPaddedByte.Assumptions]
  obtain ⟨h_msg_eq, h_message_eq, h_flags_eq, h_padded_eq⟩ := h_input
  obtain ⟨h_lenflags, h_bits, h_bytes⟩ := h_holds
  -- CheckLenFlags spec (Assumptions = True were already discharged)
  obtain ⟨h_len_lt, h_onehot⟩ := h_lenflags
  -- BitsBool spec: every padded bit is boolean (already on `input_padded`)
  -- Booleanity in terms of the evaluated padded vector, needed for `paddedWord_isBool`.
  have h_padded_bool : ∀ i : Fin paddedBitsLen,
      IsBool (Vector.map (Expression.eval env) input_var_padded)[i] := by
    intro i
    rw [h_padded_eq]
    exact h_bits i
  refine ⟨h_len_lt, h_onehot, h_bits, ?_⟩
  intro j
  -- assemble CheckPaddedByte's assumptions for this j
  have h_word_bool : ∀ t : Fin 32,
      IsBool (Expression.eval env (paddedWord input_var_padded j)[t]) := by
    intro t
    have := paddedWord_isBool env input_var_padded j h_padded_bool t
    simp only [Fin.getElem_fin, Vector.getElem_map] at this ⊢
    exact this
  have h_spec_j := (h_bytes j) ⟨h_assumptions, h_len_lt, h_onehot, h_word_bool⟩
  -- h_spec_j : wordByteVal (eval (paddedWord ...)) ⟨j%4⟩ = specPaddedByte (map ...) msgLen.val j
  rw [wordByteVal_paddedWord env input_var_padded j, h_padded_eq] at h_spec_j
  exact h_spec_j

theorem completeness : FormalAssertion.Completeness (F p) main Assumptions Spec := by
  circuit_proof_start [CheckLenFlags.circuit, CheckLenFlags.Spec, CheckLenFlags.Assumptions,
    BitsBool.circuit, BitsBool.Spec,
    CheckPaddedByte.circuit, CheckPaddedByte.Spec, CheckPaddedByte.Assumptions]
  obtain ⟨h_msg_eq, h_message_eq, h_flags_eq, h_padded_eq⟩ := h_input
  obtain ⟨h_len_lt, h_onehot, h_padded_bool, h_byte_eq⟩ := h_spec
  -- booleanity of the evaluated padded vector, needed for `paddedWord_isBool`
  have h_padded_bool' : ∀ i : Fin paddedBitsLen,
      IsBool (Vector.map (Expression.eval env.toEnvironment) input_var_padded)[i] := by
    intro i
    rw [h_padded_eq]
    exact h_padded_bool i
  refine ⟨⟨h_len_lt, h_onehot⟩, h_padded_bool, ?_⟩
  -- per-byte CheckPaddedByte: Assumptions ∧ Spec
  intro j
  have h_word_bool : ∀ t : Fin 32,
      IsBool (Expression.eval env.toEnvironment (paddedWord input_var_padded j)[t]) := by
    intro t
    have := paddedWord_isBool env.toEnvironment input_var_padded j h_padded_bool' t
    simp only [Fin.getElem_fin, Vector.getElem_map] at this ⊢
    exact this
  refine ⟨⟨h_assumptions, h_len_lt, h_onehot, h_word_bool⟩, ?_⟩
  -- Spec j : wordByteVal (eval (paddedWord ...)) ⟨j%4⟩ = specPaddedByte (map ...) msgLen.val j
  rw [wordByteVal_paddedWord env.toEnvironment input_var_padded j, h_padded_eq]
  exact h_byte_eq j

def circuit : FormalAssertion (F p) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end CheckPad
end Solution.SHA256
end
