import Solution.SHA256.PaddingTheorems
import Solution.SHA256.Theorems
import Solution.SHA256.SelectDigestTheorems

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

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 8) (F p)) :=
  pure (Vector.ofFn fun (w : Fin 8) =>
    Fin.foldl inputBufferLen
      (fun acc len =>
        acc + input.lenFlags[len] * fromBitsExpr (stateForLen (statesVec input) len.val)[w])
      0)

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
  rw [Vector.getElem_ofFn]
  rw [eval_finFoldl_add]
  simp only [Expression.eval]
  set varRec : Inputs (Expression (F p)) :=
    { messageLen := input_var_messageLen, lenFlags := input_var_lenFlags,
      s1 := input_var_s1, s2 := input_var_s2, s3 := input_var_s3,
      s4 := input_var_s4, s5 := input_var_s5 } with hvarRec
  set valRec : Inputs (F p) :=
    { messageLen := input_messageLen, lenFlags := input_lenFlags,
      s1 := input_s1, s2 := input_s2, s3 := input_s3, s4 := input_s4, s5 := input_s5 } with hvalRec
  -- The candidate word selected at length `i`, evaluated to the value level.
  set g : Fin inputBufferLen → F p :=
    fun i => Expression.eval env (fromBitsExpr (stateForLen (statesVec varRec) i.val)[w.val]) with hg
  -- Rewrite the summand flags to the value-level flags.
  have hsum : (∑ x : Fin inputBufferLen, Expression.eval env input_var_lenFlags[x.val] *
        Expression.eval env (fromBitsExpr (stateForLen (statesVec varRec) x.val)[w.val]))
      = ∑ i : Fin inputBufferLen, input_lenFlags[i] * g i := by
    apply Finset.sum_congr rfl
    intro i _
    have hflag : Expression.eval env input_var_lenFlags[i.val] = input_lenFlags[i] := by
      simp [← h_flags, Vector.getElem_map]
    rw [hflag]
  rw [hsum, oneHot_mul_sum h_onehot h_len g, hg]
  simp only []
  set ℓ := ZMod.val input_messageLen with hℓ
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
  have hword : (stateForLen (statesVec varRec) ℓ)[w.val].map (Expression.eval env) =
      (stateForLen (statesVec valRec) ℓ)[w.val] := by
    have hsv : (statesVec varRec).map (fun st => st.map (Vector.map (Expression.eval env)))
        = statesVec valRec := by
      simp only [statesVec, hvarRec, hvalRec, Vector.map_mk, List.map_toArray, List.map_cons,
        List.map_nil, e1, e2, e3, e4, e5]
    have hsfl := stateForLen_map (fun st : SHA256State (Expression (F p)) =>
      st.map (Vector.map (Expression.eval env))) (statesVec varRec) ℓ
    rw [hsv] at hsfl
    have hget := congrArg (fun st : SHA256State (F p) => st[w.val]'(by omega)) hsfl.symm
    simp only [Vector.getElem_map] at hget
    exact hget
  simp only [fromBitsExpr, Utils.Bits.fieldFromBits_eval, hword]
  have hnw : Normalized (stateForLen (statesVec valRec) ℓ)[w.val] := by
    obtain ⟨k, hk⟩ := stateForLen_mem (statesVec valRec) ℓ
    rw [hk]
    exact h_norm k w
  exact val_fieldFromBits _ hnw

omit h_large in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit (F p) Inputs (fields 8) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SelectDigest
end Solution.SHA256
end
