import Solution.SHA256.Common
import Solution.SHA256.CheckLenFlagsTheorems

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256

/-!
# Length-flag check

A `FormalAssertion` that the `lenFlags` vector is the one-hot indicator of the
claimed message length:
- every flag is boolean,
- the flags sum to one,
- the flag-weighted sum of indices equals `messageLen`.

Soundness needs no assumptions: the constraints force `messageLen.val <
inputBufferLen` and the one-hot property.
-/

namespace CheckLenFlags

open Challenge.Instances.SHA256.Interface (inputBufferLen)

structure Inputs (F : Type) where
  messageLen : F
  lenFlags : fields inputBufferLen F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) Unit := do
  Circuit.forEach (Vector.finRange inputBufferLen) fun i =>
    assertZero (input.lenFlags[i] * (input.lenFlags[i] - 1))
  let flagSum :=
    Fin.foldl inputBufferLen (fun acc i => acc + input.lenFlags[i])
      (0 : Expression (F p))
  assertZero (flagSum - 1)
  let lenValue :=
    Fin.foldl inputBufferLen
      (fun acc i => acc + input.lenFlags[i] * (((i.val : ℕ) : F p) : Expression (F p)))
      (0 : Expression (F p))
  assertZero (input.messageLen - lenValue)

instance elaborated : ElaboratedCircuit (F p) Inputs unit main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F p)) : Prop := True

def Spec (input : Inputs (F p)) : Prop :=
  input.messageLen.val < inputBufferLen ∧
  OneHotAt input.lenFlags input.messageLen.val

/-! ## Helper lemmas

Gadget-private lemmas live in `CheckLenFlagsTheorems`. -/

theorem soundness : FormalAssertion.Soundness (F p) main Assumptions Spec := by
  circuit_proof_start
  -- name the flag values
  set flags := input_lenFlags with hflags
  -- relate evaluated variables to input values
  have h_flag : ∀ i : Fin inputBufferLen,
      Expression.eval env input_var_lenFlags[i.val] = flags[i.val] := by
    intro i
    have := Vector.ext_iff.mp h_input.2 i.val i.isLt
    simpa [Vector.getElem_map] using this
  obtain ⟨h_bool_raw, h_sum_raw, h_wt_raw⟩ := h_holds
  -- booleanity of each flag
  have h_bool : ∀ i : Fin inputBufferLen, IsBool flags[i.val] := by
    intro i
    have := h_bool_raw i
    rw [h_flag i] at this
    rw [IsBool.iff_mul_sub_one]
    rw [show flags[i.val] - 1 = flags[i.val] + -1 from by ring]
    exact this
  -- the field sum of flags equals 1
  have h_sum : (∑ i : Fin inputBufferLen, flags[i.val]) = 1 := by
    rw [eval_foldl_sum] at h_sum_raw
    have : (∑ i : Fin inputBufferLen, Expression.eval env input_var_lenFlags[i.val]) = 1 := by
      have := h_sum_raw
      simp only [add_neg_eq_zero] at this
      exact this
    rw [← this]
    apply Finset.sum_congr rfl
    intro i _
    exact (h_flag i).symm
  -- the weighted sum equals messageLen
  have h_wt : input_messageLen = ∑ i : Fin inputBufferLen, flags[i.val] * ((i.val : ℕ) : F p) := by
    rw [eval_foldl_sum] at h_wt_raw
    have heq : (∑ i : Fin inputBufferLen,
        Expression.eval env (input_var_lenFlags[i.val] * Expression.const ((i.val : ℕ) : F p)))
        = ∑ i : Fin inputBufferLen, flags[i.val] * ((i.val : ℕ) : F p) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Expression.eval]
      rw [h_flag i]
    rw [heq] at h_wt_raw
    rw [add_neg_eq_zero] at h_wt_raw
    exact h_wt_raw
  exact onehot_from_constraints flags input_messageLen h_bool h_sum h_wt

omit h_large in
theorem completeness : FormalAssertion.Completeness (F p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_msg_lt, h_onehot⟩ := h_spec
  -- relate evaluated variables to input values
  have h_flag : ∀ i : Fin inputBufferLen,
      Expression.eval env input_var_lenFlags[i.val] = input_lenFlags[i.val] := by
    intro i
    have := Vector.ext_iff.mp h_input.2 i.val i.isLt
    simpa [Vector.getElem_map] using this
  -- one-hot value of each flag
  have h_flag_val : ∀ k : Fin inputBufferLen,
      Expression.eval env input_var_lenFlags[k.val] =
        if k.val = input_messageLen.val then 1 else 0 := by
    intro k
    rw [h_flag k]
    exact h_onehot k
  refine ⟨?_, ?_, ?_⟩
  · -- booleanity
    intro i
    rw [h_flag_val i]
    by_cases h : i.val = input_messageLen.val <;> simp [h]
  · -- flags sum to 1
    rw [eval_foldl_sum]
    have : (∑ i : Fin inputBufferLen, Expression.eval env.toEnvironment input_var_lenFlags[i.val]) = 1 := by
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h_flag_val i)]
      rw [Finset.sum_eq_single (⟨input_messageLen.val, h_msg_lt⟩ : Fin inputBufferLen)]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h))]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]; ring
  · -- weighted sum equals messageLen
    rw [eval_foldl_sum]
    have hsum : (∑ i : Fin inputBufferLen,
        Expression.eval env (input_var_lenFlags[i.val] * Expression.const ((i.val : ℕ) : F p)))
        = ((input_messageLen.val : ℕ) : F p) := by
      have hstep : ∀ i : Fin inputBufferLen,
          Expression.eval env.toEnvironment (input_var_lenFlags[i.val] * Expression.const ((i.val : ℕ) : F p))
          = (if i.val = input_messageLen.val then 1 else 0) * ((i.val : ℕ) : F p) := by
        intro i
        simp only [Expression.eval]
        rw [h_flag_val i]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i)]
      rw [Finset.sum_eq_single ⟨input_messageLen.val, h_msg_lt⟩]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h))]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum]
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring

def circuit : FormalAssertion (F p) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end CheckLenFlags
end Solution.SHA256
end
