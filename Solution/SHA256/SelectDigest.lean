import Solution.SHA256.PaddingTheorems
import Solution.SHA256.Theorems
import Solution.SHA256.SelectDigestTheorems
import Challenge.Utils.ComputableWitnessLemmas

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256
namespace SelectDigest

open Challenge.Instances.SHA256.Interface (inputBufferLen)

structure Inputs (F : Type) where
  messageLen : F
  lenFlags : fields inputBufferLen F
  s1 : SHA256State F
  s2 : SHA256State F
  s3 : SHA256State F
  s4 : SHA256State F
  s5 : SHA256State F
deriving ProvableStruct

/-- The five candidate states bundled as a vector. -/
def statesVec {F : Type} (input : Inputs F) : Vector (SHA256State F) paddedBlocksLen :=
  #v[input.s1, input.s2, input.s3, input.s4, input.s5]

def selectedWordExpr (input : Var Inputs (F p)) (w : Fin 8) (len : Fin inputBufferLen) :
    Expression (F p) :=
  fromBitsExpr (stateForLen (statesVec input) len.val)[w]

def selectedDigestExpr (input : Var Inputs (F p)) (w : Fin 8) : Expression (F p) :=
  Fin.foldl inputBufferLen
    (fun acc len => acc + input.lenFlags[len] * selectedWordExpr input w len)
    0

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 8) (F p)) := do
  let digest ← witnessVector 8 fun env =>
    Vector.ofFn fun w => env (selectedDigestExpr input w)
  Circuit.forEach (Vector.finRange 8) fun w =>
    Circuit.forEach (Vector.finRange inputBufferLen) fun len =>
      assertZero (input.lenFlags[len] * (digest[w] - selectedWordExpr input w len))
  return digest

def Assumptions (input : Inputs (F p)) : Prop :=
  input.messageLen.val < inputBufferLen ∧
  OneHotAt input.lenFlags input.messageLen.val ∧
  (∀ k : Fin paddedBlocksLen, ∀ i : Fin 8, Normalized (statesVec input)[k][i])

def Spec (input : Inputs (F p)) (out : fields 8 (F p)) : Prop :=
  ∀ w : Fin 8, out[w].val = valueBits ((stateForLen (statesVec input) input.messageLen.val)[w])

@[reducible] instance elaborated : ElaboratedCircuit (F p) Inputs (fields 8) main := by
  elaborate_circuit

/-! Gadget-private lemmas live in `SelectDigestTheorems`. -/

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start
  intro w
  obtain ⟨h_len, h_onehot, h_norm⟩ := h_assumptions
  obtain ⟨h_msg, h_flags, h_s1, h_s2, h_s3, h_s4, h_s5⟩ := h_input
  set varRec : Inputs (Expression (F p)) :=
    { messageLen := input_var_messageLen, lenFlags := input_var_lenFlags,
      s1 := input_var_s1, s2 := input_var_s2, s3 := input_var_s3,
      s4 := input_var_s4, s5 := input_var_s5 } with hvarRec
  set valRec : Inputs (F p) :=
    { messageLen := input_messageLen, lenFlags := input_lenFlags,
      s1 := input_s1, s2 := input_s2, s3 := input_s3, s4 := input_s4, s5 := input_s5 } with hvalRec
  let selectedLen : Fin inputBufferLen := ⟨input_messageLen.val, h_len⟩
  have hflag_eval :
      Expression.eval env input_var_lenFlags[selectedLen.val] = input_lenFlags[selectedLen] := by
    simp [← h_flags, Vector.getElem_map]
  have hflag_one : input_lenFlags[selectedLen] = 1 := by
    have := h_onehot selectedLen
    simpa [selectedLen] using this
  have hrow := h_holds w selectedLen
  rw [hflag_eval, hflag_one, one_mul] at hrow
  rw [← sub_eq_add_neg] at hrow
  have hdigest :
      env.get (i₀ + w.val) = Expression.eval env (selectedWordExpr varRec w selectedLen) :=
    sub_eq_zero.mp hrow
  -- each state variable evaluates (componentwise) to its value
  have estate : ∀ (sv : SHA256State (Expression (F p))) (s : SHA256State (F p)),
      eval env sv = s → sv.map (Vector.map (Expression.eval env)) = s := by
    intro sv s h
    rw [← h, eval_vector]
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_map, CircuitType.eval_var_fields]
  have e1 := estate _ _ h_s1
  have e2 := estate _ _ h_s2
  have e3 := estate _ _ h_s3
  have e4 := estate _ _ h_s4
  have e5 := estate _ _ h_s5
  -- Bridge: the selected word at the variable level evaluates to the value-level word.
  have hword : ((stateForLen (statesVec varRec) selectedLen.val)[w]).map (Expression.eval env) =
      (stateForLen (statesVec valRec) selectedLen.val)[w] := by
    have hsv : (statesVec varRec).map (fun st => st.map (Vector.map (Expression.eval env)))
        = statesVec valRec := by
      simp only [statesVec, hvarRec, hvalRec, Vector.map_mk, List.map_toArray, List.map_cons,
        List.map_nil, e1, e2, e3, e4, e5]
    have hsfl := stateForLen_map (fun st : SHA256State (Expression (F p)) =>
      st.map (Vector.map (Expression.eval env))) (statesVec varRec) selectedLen.val
    rw [hsv] at hsfl
    have hget := congrArg (fun st : SHA256State (F p) => st[w]) hsfl.symm
    have houter :
        (Vector.map (fun word : fields 32 (Expression (F p)) =>
          word.map (Expression.eval env)) (stateForLen (statesVec varRec) selectedLen.val))[w] =
          ((stateForLen (statesVec varRec) selectedLen.val)[w]).map (Expression.eval env) :=
      Vector.getElem_map
        (fun word : fields 32 (Expression (F p)) => word.map (Expression.eval env))
        (xs := stateForLen (statesVec varRec) selectedLen.val) w.isLt
    change
      (Vector.map (fun word : fields 32 (Expression (F p)) => word.map (Expression.eval env))
        (stateForLen (statesVec varRec) selectedLen.val))[w] =
        (stateForLen (statesVec valRec) selectedLen.val)[w] at hget
    rw [houter] at hget
    exact hget
  have hword_eval :
      Expression.eval env (selectedWordExpr varRec w selectedLen) =
        Utils.Bits.fieldFromBits (stateForLen (statesVec valRec) selectedLen.val)[w] := by
    simp only [selectedWordExpr, fromBitsExpr, Utils.Bits.fieldFromBits_eval]
    rw [hword]
  rw [hdigest, hword_eval]
  have hnw : Normalized (stateForLen (statesVec valRec) selectedLen.val)[w] := by
    obtain ⟨k, hk⟩ := stateForLen_mem (statesVec valRec) selectedLen.val
    rw [hk]
    exact h_norm k w
  exact val_fieldFromBits _ hnw

omit h_large in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start
  obtain ⟨h_len, h_onehot, _h_norm⟩ := h_assumptions
  obtain ⟨_h_msg, h_flags, _h_s1, _h_s2, _h_s3, _h_s4, _h_s5⟩ := h_input
  set varRec : Inputs (Expression (F p)) :=
    { messageLen := input_var_messageLen, lenFlags := input_var_lenFlags,
      s1 := input_var_s1, s2 := input_var_s2,
      s3 := input_var_s3, s4 := input_var_s4, s5 := input_var_s5 } with hvarRec
  intro w len
  set g : Fin inputBufferLen → F p :=
    fun i => Expression.eval env.toEnvironment (selectedWordExpr varRec w i) with hg
  have hflag_eval : ∀ i : Fin inputBufferLen,
      Expression.eval env.toEnvironment input_var_lenFlags[i.val] = input_lenFlags[i] := by
    intro i
    simp [← h_flags, Vector.getElem_map]
  have hdigest : env.get (i₀ + w.val) = ∑ i : Fin inputBufferLen, input_lenFlags[i] * g i := by
    rw [h_env w, Vector.getElem_ofFn]
    rw [selectedDigestExpr, eval_finFoldl_add]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Expression.eval]
    have hflag_var :
        Expression.eval env.toEnvironment varRec.lenFlags[i] = input_lenFlags[i] := by
      rw [hvarRec]
      exact hflag_eval i
    rw [hflag_var, hg]
  rw [hflag_eval len, h_onehot len]
  by_cases hsel : len.val = input_messageLen.val
  · have hlen_eq : len = (⟨input_messageLen.val, h_len⟩ : Fin inputBufferLen) := Fin.ext hsel
    rw [if_pos hsel, one_mul]
    rw [hdigest, oneHot_mul_sum h_onehot h_len g, ← hlen_eq]
    ring
  · rw [if_neg hsel, zero_mul]

def circuit : FormalCircuit (F p) Inputs (fields 8) where
  main; elaborated; Assumptions; Spec; soundness; completeness

attribute [local irreducible] main

theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    simp [circuit_norm] at h_input
    have estate : ∀ sv : SHA256State (Expression (F p)),
        eval env.toEnvironment sv = eval env'.toEnvironment sv →
        sv.map (Vector.map (Expression.eval env.toEnvironment)) =
          sv.map (Vector.map (Expression.eval env'.toEnvironment)) := by
      intro sv h
      calc
        sv.map (Vector.map (Expression.eval env.toEnvironment)) = eval env.toEnvironment sv := by
          rw [eval_vector]
          apply Vector.ext
          intro i hi
          rw [Vector.getElem_map, Vector.getElem_map, CircuitType.eval_var_fields]
        _ = eval env'.toEnvironment sv := h
        _ = sv.map (Vector.map (Expression.eval env'.toEnvironment)) := by
          rw [eval_vector]
          apply Vector.ext
          intro i hi
          rw [Vector.getElem_map, Vector.getElem_map, CircuitType.eval_var_fields]
    have hword : ∀ (w : Fin 8) (len : Fin inputBufferLen),
        Expression.eval env.toEnvironment (selectedWordExpr input w len) =
          Expression.eval env'.toEnvironment (selectedWordExpr input w len) := by
      intro w len
      have hstates :
          (statesVec input).map (fun st =>
              st.map (Vector.map (Expression.eval env.toEnvironment))) =
            (statesVec input).map (fun st =>
              st.map (Vector.map (Expression.eval env'.toEnvironment))) := by
        simp only [statesVec, Vector.map_mk, List.map_toArray, List.map_cons,
          List.map_nil,
          estate input.s1 h_input.2.2.1,
          estate input.s2 h_input.2.2.2.1,
          estate input.s3 h_input.2.2.2.2.1,
          estate input.s4 h_input.2.2.2.2.2.1,
          estate input.s5 h_input.2.2.2.2.2.2]
      have hselected :=
        congrArg (fun v : Vector (SHA256State (F p)) paddedBlocksLen =>
          (stateForLen v len.val)[w]) hstates
      have hselected' :
          ((stateForLen (statesVec input) len.val)[w]).map
              (Expression.eval env.toEnvironment) =
            ((stateForLen (statesVec input) len.val)[w]).map
              (Expression.eval env'.toEnvironment) := by
        simp only [stateForLen_map] at hselected
        change
          (Vector.map (Vector.map (Expression.eval env.toEnvironment))
            (stateForLen (statesVec input) len.val))[w.val]'w.isLt =
          (Vector.map (Vector.map (Expression.eval env'.toEnvironment))
            (stateForLen (statesVec input) len.val))[w.val]'w.isLt at hselected
        rw [Vector.getElem_map, Vector.getElem_map] at hselected
        exact hselected
      simp only [selectedWordExpr, fromBitsExpr, Utils.Bits.fieldFromBits_eval]
      exact congrArg Utils.Bits.fieldFromBits hselected'
    apply Vector.ext
    intro w hw
    simp only [Vector.getElem_ofFn]
    unfold selectedDigestExpr
    rw [eval_finFoldl_add, eval_finFoldl_add]
    apply Finset.sum_congr rfl
    intro len _
    simp only [Expression.eval]
    congr 1
    · exact h_input.2.1 input.lenFlags[len] (Vector.getElem_mem _)
    · exact hword ⟨w, hw⟩ len
  · intro _ _
    trivial

end SelectDigest
end Solution.SHA256
end
