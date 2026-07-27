import Solution.SHA256CompressGF2.ScheduleStep
import Mathlib.Tactic.IntervalCases

/-!
# `Round`: one SHA-256 round over GF(2)

Input `v = a‖b‖c‖d‖e‖f‖g‖h‖w` (`fields 288`), parameterized by the round
constant `k : ℕ`. Computes `t1 = h + Σ₁(e) + Ch(e,f,g) + K + w`,
`t2 = Σ₀(a) + Maj(a,b,c)`, pins the new `a` and `e` words, and returns the
shifted state `a'‖a‖b‖c‖e'‖e‖f‖g`. Cost: 7·31 + 32 + 32 + 2·32 = 345.
-/

namespace Solution.SHA256CompressGF2

open Challenge.Instances.SHA256CompressGF2Canonical.Interface
open Challenge.F2Bits
open Challenge.CostR1CS

/-- Plain total accessor into a 288-vector. -/
def a288 {α : Type} (v : Vector α 288) (k : ℕ) : α :=
  v[k % 288]'(Nat.mod_lt _ (by norm_num))

/-- Word `k` (32 bits) of a 288-vector. -/
def w288 (v : Var (fields 288) (F p2)) (k : ℕ) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => a288 v (32 * k + i.val)

/-- The bits of a constant word (e.g. a round constant), as constant expressions. -/
def constW (n : ℕ) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 =>
    Expression.const (if (n >>> i.val) &&& 1 == 1 then 1 else 0)

/-- Assemble the shifted output state `a'‖a‖b‖c‖e'‖e‖f‖g` from the pinned new
words and the input state. -/
def outState (A E : Var (fields 32) (F p2)) (v : Var (fields 288) (F p2)) :
    Var (fields 256) (F p2) :=
  Vector.ofFn fun i : Fin 256 =>
    if i.val < 32 then b32 A i.val
    else if i.val < 128 then a288 v (i.val - 32)
    else if i.val < 160 then b32 E i.val
    else a288 v (i.val - 32)

/-! ## `toNat`/`wordAt` bridges for the assembly maps -/

/-- The bit-selection boolean in `constW` is `Nat.testBit`. -/
theorem beq_and_one_eq_testBit (n i : ℕ) : ((n >>> i) &&& 1 == 1) = n.testBit i := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;>
    simp [h, Nat.testBit, Nat.shiftRight_eq_div_pow]

/-- `toNat` of the evaluated constant word is `n % 2^32`. -/
theorem toNat_eval_constW (env : Environment (F p2)) (n : ℕ) :
    toNat (Vector.map (Expression.eval env) (constW n)) = n % 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · have hentry : (Vector.map (Expression.eval env) (constW n))[i]'hi
        = (if ((n >>> i) &&& 1) == 1 then 1 else 0) := by
      rw [Vector.getElem_map]
      unfold constW
      rw [Vector.getElem_ofFn]
      split <;> rfl
    rw [testBit_toNat _ i hi, Nat.testBit_mod_two_pow, hentry, ← beq_and_one_eq_testBit n i]
    rcases Bool.eq_false_or_eq_true ((n >>> i) &&& 1 == 1) with h | h
    · rw [h]; simp [hi]; decide
    · rw [h]; simp [hi]
  · rw [testBit_toNat_ge _ i (by omega), Nat.testBit_mod_two_pow]
    simp [hi]

/-- Word `t` of the evaluated `c96 x y z` is `toNat` of the evaluated component. -/
theorem wordAt_eval_c96_0 (env : Environment (F p2)) (x y z : Var (fields 32) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (c96 x y z)) 0
      = toNat (Vector.map (Expression.eval env) x) := by
  refine wordAt_map_eval_eq_toNat _ x 0 (by norm_num) ?_
  intro j hj
  unfold c96 b32
  rw [Vector.getElem_ofFn]
  rw [if_pos (by omega : 32 * 0 + j < 32)]
  simp only [show (32 * 0 + j) % 32 = j from by omega]

theorem wordAt_eval_c96_1 (env : Environment (F p2)) (x y z : Var (fields 32) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (c96 x y z)) 1
      = toNat (Vector.map (Expression.eval env) y) := by
  refine wordAt_map_eval_eq_toNat _ y 1 (by norm_num) ?_
  intro j hj
  unfold c96 b32
  rw [Vector.getElem_ofFn]
  rw [if_neg (by omega : ¬ 32 * 1 + j < 32), if_pos (by omega : 32 * 1 + j < 64)]
  simp only [show (32 * 1 + j) % 32 = j from by omega]

theorem wordAt_eval_c96_2 (env : Environment (F p2)) (x y z : Var (fields 32) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (c96 x y z)) 2
      = toNat (Vector.map (Expression.eval env) z) := by
  refine wordAt_map_eval_eq_toNat _ z 2 (by norm_num) ?_
  intro j hj
  unfold c96 b32
  rw [Vector.getElem_ofFn]
  rw [if_neg (by omega : ¬ 32 * 2 + j < 32), if_neg (by omega : ¬ 32 * 2 + j < 64)]
  simp only [show (32 * 2 + j) % 32 = j from by omega]

/-- Word 0 of the evaluated `outState A E v` is the pinned `A`. -/
theorem wordAt_eval_outState_0 (env : Environment (F p2))
    (A E : Var (fields 32) (F p2)) (v : Var (fields 288) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (outState A E v)) 0
      = toNat (Vector.map (Expression.eval env) A) := by
  refine wordAt_map_eval_eq_toNat _ A 0 (by norm_num) ?_
  intro j hj
  unfold outState b32
  rw [Vector.getElem_ofFn]
  rw [if_pos (by omega : 32 * 0 + j < 32)]
  simp only [show (32 * 0 + j) % 32 = j from by omega]

/-- Word 4 of the evaluated `outState A E v` is the pinned `E`. -/
theorem wordAt_eval_outState_4 (env : Environment (F p2))
    (A E : Var (fields 32) (F p2)) (v : Var (fields 288) (F p2)) :
    wordAt 32 (Vector.map (Expression.eval env) (outState A E v)) 4
      = toNat (Vector.map (Expression.eval env) E) := by
  refine wordAt_map_eval_eq_toNat _ E 4 (by norm_num) ?_
  intro j hj
  unfold outState b32
  rw [Vector.getElem_ofFn]
  rw [if_neg (by omega : ¬ 32 * 4 + j < 32), if_neg (by omega : ¬ 32 * 4 + j < 128),
    if_pos (by omega : 32 * 4 + j < 160)]
  simp only [show (32 * 4 + j) % 32 = j from by omega]

/-! ### `sha256Round` as an explicit vector (kernel-friendly getElem lemmas) -/

theorem vec8_0 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[0] = x0 := rfl
theorem vec8_1 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[1] = x1 := rfl
theorem vec8_2 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[2] = x2 := rfl
theorem vec8_3 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[3] = x3 := rfl
theorem vec8_4 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[4] = x4 := rfl
theorem vec8_5 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[5] = x5 := rfl
theorem vec8_6 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[6] = x6 := rfl
theorem vec8_7 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[7] = x7 := rfl

/-- `sha256Round` written out as an explicit 8-vector (definitional). -/
theorem sha256Round_eq (state : Vector ℕ 8) (k w : ℕ) :
    Specs.SHA256.sha256Round state k w
      = #v[_root_.add32
              (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 state[7]
                (Specs.SHA256.upperSigma1 state[4]))
                (Specs.SHA256.Ch state[4] state[5] state[6])) k) w)
              (_root_.add32 (Specs.SHA256.upperSigma0 state[0])
                (Specs.SHA256.Maj state[0] state[1] state[2])),
          state[0], state[1], state[2],
          _root_.add32 state[3]
            (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 state[7]
              (Specs.SHA256.upperSigma1 state[4]))
              (Specs.SHA256.Ch state[4] state[5] state[6])) k) w),
          state[4], state[5], state[6]] := rfl

/-- Words `1,2,3,5,6,7` of the evaluated `outState A E v` pass through the
input state words `c − 1`. -/
theorem wordAt_eval_outState_pass (env : Environment (F p2))
    (A E : Var (fields 32) (F p2)) (v : Var (fields 288) (F p2))
    (input : fields 288 (F p2))
    (hv : ∀ (m : ℕ) (hm : m < 288), Expression.eval env (v[m]'hm) = input[m]'hm)
    (c : ℕ) (hc1 : 1 ≤ c) (hc : c < 8) (hne : c ≠ 4) :
    wordAt 32 (Vector.map (Expression.eval env) (outState A E v)) c
      = wordAt 32 input (c - 1) := by
  interval_cases c
  · refine wordAt_map_eval_eq_wordAt _ input 1 (1 - 1) (by norm_num) (by norm_num) ?_
    intro j hj
    unfold outState a288
    rw [Vector.getElem_ofFn]
    rw [if_neg (by omega : ¬ 32 * 1 + j < 32), if_pos (by omega : 32 * 1 + j < 128)]
    simp only [show (32 * 1 + j - 32) % 288 = 32 * (1 - 1) + j from by omega]
    exact hv _ (by omega)
  · refine wordAt_map_eval_eq_wordAt _ input 2 (2 - 1) (by norm_num) (by norm_num) ?_
    intro j hj
    unfold outState a288
    rw [Vector.getElem_ofFn]
    rw [if_neg (by omega : ¬ 32 * 2 + j < 32), if_pos (by omega : 32 * 2 + j < 128)]
    simp only [show (32 * 2 + j - 32) % 288 = 32 * (2 - 1) + j from by omega]
    exact hv _ (by omega)
  · refine wordAt_map_eval_eq_wordAt _ input 3 (3 - 1) (by norm_num) (by norm_num) ?_
    intro j hj
    unfold outState a288
    rw [Vector.getElem_ofFn]
    rw [if_neg (by omega : ¬ 32 * 3 + j < 32), if_pos (by omega : 32 * 3 + j < 128)]
    simp only [show (32 * 3 + j - 32) % 288 = 32 * (3 - 1) + j from by omega]
    exact hv _ (by omega)
  · exact absurd rfl hne
  · refine wordAt_map_eval_eq_wordAt _ input 5 (5 - 1) (by norm_num) (by norm_num) ?_
    intro j hj
    unfold outState a288
    rw [Vector.getElem_ofFn]
    rw [if_neg (by omega : ¬ 32 * 5 + j < 32), if_neg (by omega : ¬ 32 * 5 + j < 128),
      if_neg (by omega : ¬ 32 * 5 + j < 160)]
    simp only [show (32 * 5 + j - 32) % 288 = 32 * (5 - 1) + j from by omega]
    exact hv _ (by omega)
  · refine wordAt_map_eval_eq_wordAt _ input 6 (6 - 1) (by norm_num) (by norm_num) ?_
    intro j hj
    unfold outState a288
    rw [Vector.getElem_ofFn]
    rw [if_neg (by omega : ¬ 32 * 6 + j < 32), if_neg (by omega : ¬ 32 * 6 + j < 128),
      if_neg (by omega : ¬ 32 * 6 + j < 160)]
    simp only [show (32 * 6 + j - 32) % 288 = 32 * (6 - 1) + j from by omega]
    exact hv _ (by omega)
  · refine wordAt_map_eval_eq_wordAt _ input 7 (7 - 1) (by norm_num) (by norm_num) ?_
    intro j hj
    unfold outState a288
    rw [Vector.getElem_ofFn]
    rw [if_neg (by omega : ¬ 32 * 7 + j < 32), if_neg (by omega : ¬ 32 * 7 + j < 128),
      if_neg (by omega : ¬ 32 * 7 + j < 160)]
    simp only [show (32 * 7 + j - 32) % 288 = 32 * (7 - 1) + j from by omega]
    exact hv _ (by omega)

/-! ## `eval`-agreement congruences for the round assembly maps -/

section EvalCongr

variable {env env' : ProverEnvironment (F p2)}

theorem eval_w288_congr {v : Var (fields 288) (F p2)} (h : eval env v = eval env' v) (k : ℕ) :
    eval env (w288 v k) = eval env' (w288 v k) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold w288 a288
  rw [Vector.getElem_ofFn]
  exact eval_getElem_congr h _ _

/-- The round constant is closed, so it evaluates the same in any environment. -/
theorem eval_constW_congr (n : ℕ) : eval env (constW n) = eval env' (constW n) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold constW
  rw [Vector.getElem_ofFn]
  rfl

theorem eval_outState_congr {A E : Var (fields 32) (F p2)} {v : Var (fields 288) (F p2)}
    (hA : eval env A = eval env' A) (hE : eval env E = eval env' E)
    (hv : eval env v = eval env' v) :
    eval env (outState A E v) = eval env' (outState A E v) := by
  refine eval_fields_of_getElem fun i hi => ?_
  unfold outState b32 a288
  rw [Vector.getElem_ofFn]
  split
  · exact eval_getElem_congr hA _ _
  · split
    · exact eval_getElem_congr hv _ _
    · split
      · exact eval_getElem_congr hE _ _
      · exact eval_getElem_congr hv _ _

end EvalCongr

namespace Round

/-- One round with constant `k`. State words: `a=0 … h=7`, `w=8`. -/
def main (k : ℕ) (v : Var (fields 288) (F p2)) :
    Circuit (F p2) (Var (fields 256) (F p2)) := do
  let ch ← Ch32.circuit (c96 (w288 v 4) (w288 v 5) (w288 v 6))
  let maj ← Maj32.circuit (c96 (w288 v 0) (w288 v 1) (w288 v 2))
  let t1a ← Add32.circuit ⟨w288 v 7, upperSigma1E (w288 v 4)⟩
  let t1b ← Add32.circuit ⟨t1a, ch⟩
  let t1c ← Add32.circuit ⟨t1b, constW k⟩
  let t1 ← Add32.circuit ⟨t1c, w288 v 8⟩
  let t2 ← Add32.circuit ⟨upperSigma0E (w288 v 0), maj⟩
  let en ← Add32.circuit ⟨w288 v 3, t1⟩
  let an ← Add32.circuit ⟨t1, t2⟩
  let A ← Pin32.circuit an
  let E ← Pin32.circuit en
  return outState A E v

instance elaborated (k : ℕ) :
    ElaboratedCircuit (F p2) (fields 288) (fields 256) (main k) := by
  elaborate_circuit

def Assumptions (_ : fields 288 (F p2)) : Prop := True

/-- Word-level round function (`Specs.SHA256.sha256Round` on the packed words). -/
def Spec (k : ℕ) (v : fields 288 (F p2)) (out : fields 256 (F p2)) : Prop :=
  Vector.ofFn (fun i : Fin 8 => wordAt 32 out i.val)
    = Specs.SHA256.sha256Round (Vector.ofFn fun i : Fin 8 => wordAt 32 v i.val)
        k (wordAt 32 v 8)

theorem soundness (k : ℕ) : Soundness (F p2) (main k) Assumptions (Spec k) := by
  circuit_proof_start [main, Spec, Add32.circuit, Pin32.circuit, Ch32.circuit, Maj32.circuit,
    Add32.Assumptions, Pin32.Assumptions, Ch32.Assumptions, Maj32.Assumptions,
    Add32.Spec, Pin32.Spec, Ch32.Spec, Maj32.Spec]
  obtain ⟨hch, hmaj, ht1a, ht1b, ht1c, ht1, ht2, hen, han, hA, hE⟩ := h_holds
  have hv : ∀ (m : ℕ) (hm : m < 288),
      Expression.eval env (input_var[m]'hm) = input[m]'hm := by
    intro m hm
    have h := Vector.ext_iff.mp h_input m hm
    rwa [Vector.getElem_map] at h
  have hw : ∀ l : ℕ, 32 * l + 32 ≤ 288 →
      toNat (Vector.map (Expression.eval env) (w288 input_var l)) = wordAt 32 input l := by
    intro l hl
    refine toNat_map_eval_window _ input l hl ?_
    intro j hj
    unfold w288 a288
    rw [Vector.getElem_ofFn]
    have hlt : 32 * l + j < 288 := by omega
    simp only [Nat.mod_eq_of_lt hlt]
    exact hv _ hlt
  rw [wordAt_eval_c96_0, wordAt_eval_c96_1, wordAt_eval_c96_2,
    hw 4 (by norm_num), hw 5 (by norm_num), hw 6 (by norm_num)] at hch
  rw [wordAt_eval_c96_0, wordAt_eval_c96_1, wordAt_eval_c96_2,
    hw 0 (by norm_num), hw 1 (by norm_num), hw 2 (by norm_num)] at hmaj
  rw [toNat_eval_upperSigma1E, hw 4 (by norm_num), hw 7 (by norm_num)] at ht1a
  rw [ht1a, hch] at ht1b
  rw [ht1b, toNat_eval_constW, Nat.add_mod_mod] at ht1c
  rw [ht1c, hw 8 (by norm_num)] at ht1
  rw [toNat_eval_upperSigma0E, hw 0 (by norm_num), hmaj] at ht2
  rw [ht1, hw 3 (by norm_num)] at hen
  rw [ht1, ht2] at han
  rw [sha256Round_eq]
  simp only [Vector.getElem_ofFn]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_ofFn]
  interval_cases i
  · rw [vec8_0, wordAt_eval_outState_0, hA, han]
    simp only [show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [vec8_1, wordAt_eval_outState_pass env _ _ _ input hv 1 (by omega) (by omega) (by omega)]
  · rw [vec8_2, wordAt_eval_outState_pass env _ _ _ input hv 2 (by omega) (by omega) (by omega)]
  · rw [vec8_3, wordAt_eval_outState_pass env _ _ _ input hv 3 (by omega) (by omega) (by omega)]
  · rw [vec8_4, wordAt_eval_outState_4, hE, hen]
    simp only [show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
  · rw [vec8_5, wordAt_eval_outState_pass env _ _ _ input hv 5 (by omega) (by omega) (by omega)]
  · rw [vec8_6, wordAt_eval_outState_pass env _ _ _ input hv 6 (by omega) (by omega) (by omega)]
  · rw [vec8_7, wordAt_eval_outState_pass env _ _ _ input hv 7 (by omega) (by omega) (by omega)]

theorem completeness (k : ℕ) : Completeness (F p2) (main k) Assumptions := by
  circuit_proof_start
  simp only [Add32.circuit, Add32.Assumptions, Pin32.circuit, Pin32.Assumptions,
    Ch32.circuit, Ch32.Assumptions, Maj32.circuit, Maj32.Assumptions, and_self]

def circuit (k : ℕ) : FormalCircuit (F p2) (fields 288) (fields 256) :=
  { main := main k, elaborated := elaborated k, Assumptions, Spec := Spec k,
    soundness := soundness k, completeness := completeness k }

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

theorem computableWitnesses (k : ℕ) : (circuit k).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main k input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    Ch32.subcircuit_localLength, Maj32.subcircuit_localLength,
    Add32.subcircuit_localLength, Pin32.subcircuit_localLength,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Ch32.circuit input _ (offset)
      (fun _ _ h => eval_c96_congr (eval_w288_congr h 4) (eval_w288_congr h 5)
        (eval_w288_congr h 6))
      Ch32.computableWitnesses env env'
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Maj32.circuit input _ (offset + 32)
      (fun _ _ h => eval_c96_congr (eval_w288_congr h 0) (eval_w288_congr h 1)
        (eval_w288_congr h 2))
      Maj32.computableWitnesses env env'
  · exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
      Add32.circuit input _ (offset + 32 + 32)
      (fun _ _ h => Add32.eval_mk_congr (eval_w288_congr h 7)
        (eval_upperSigma1E_congr (eval_w288_congr h 4)))
      Add32.computableWitnesses env env'
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32.circuit input _ _ ?_ Add32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
    have ht1a := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    exact Add32.eval_mk_congr ht1a hch
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32.circuit input _ _ ?_ Add32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
    have ht1a := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    exact Add32.eval_mk_congr ht1b (eval_constW_congr k)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32.circuit input _ _ ?_ Add32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
    have ht1a := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    exact Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8)
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32.circuit input _ _ ?_ Add32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hmaj := Maj32.eval_subOut_of_agreesBelow
      (c96 (w288 input 0) (w288 input 1) (w288 input 2)) (offset + 32) (by omega) h_agree
    exact Add32.eval_mk_congr (eval_upperSigma0E_congr (eval_w288_congr h_input 0)) hmaj
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32.circuit input _ _ ?_ Add32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
    have ht1a := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    have ht1 := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8))
    exact Add32.eval_mk_congr (eval_w288_congr h_input 3) ht1
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Add32.circuit input _ _ ?_ Add32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
    have hmaj := Maj32.eval_subOut_of_agreesBelow
      (c96 (w288 input 0) (w288 input 1) (w288 input 2)) (offset + 32) (by omega) h_agree
    have ht1a := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    have ht1 := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8))
    have ht2 := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr (eval_upperSigma0E_congr (eval_w288_congr h_input 0)) hmaj)
    exact Add32.eval_mk_congr ht1 ht2
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Pin32.circuit input _ _ ?_ Pin32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
    have hmaj := Maj32.eval_subOut_of_agreesBelow
      (c96 (w288 input 0) (w288 input 1) (w288 input 2)) (offset + 32) (by omega) h_agree
    have ht1a := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    have ht1 := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8))
    have ht2 := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr (eval_upperSigma0E_congr (eval_w288_congr h_input 0)) hmaj)
    have han := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31 + 31 + 31 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1 ht2)
    exact han
  · refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
      Pin32.circuit input _ _ ?_ Pin32.computableWitnesses env env'
    intro kk e e' hle h_agree h_input
    have hch := Ch32.eval_subOut_of_agreesBelow
      (c96 (w288 input 4) (w288 input 5) (w288 input 6)) (offset) (by omega) h_agree
    have ht1a := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 7)
        (eval_upperSigma1E_congr (eval_w288_congr h_input 4)))
    have ht1b := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1a hch)
    have ht1c := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1b (eval_constW_congr k))
    have ht1 := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr ht1c (eval_w288_congr h_input 8))
    have hen := Add32.eval_subOut_of_agreesBelow _ (offset + 32 + 32 + 31 + 31 + 31 + 31 + 31) (by omega) h_agree
      (Add32.eval_mk_congr (eval_w288_congr h_input 3) ht1)
    exact hen

theorem subcircuit_localLength (k : ℕ) (v : Var (fields 288) (F p2)) (m : ℕ) :
    (subcircuit (circuit k) v).localLength m = 345 := rfl

/-- The round's output mixes the two pinned words (fresh witnesses at relative
offsets 281 and 313) with pass-through words of the input state. -/
theorem eval_subOut_of_agreesBelow (k : ℕ) (v : Var (fields 288) (F p2)) (n : ℕ) {kk : ℕ}
    (hk : n + 345 ≤ kk) {env env' : ProverEnvironment (F p2)}
    (h_agree : env.AgreesBelow kk env') (h_input : eval env v = eval env' v) :
    eval env ((subcircuit (circuit k) v).output n)
      = eval env' ((subcircuit (circuit k) v).output n) := by
  have hout : (subcircuit (circuit k) v).output n
      = outState (varFromOffset (fields 32) (n + 281))
          (varFromOffset (fields 32) (n + 313)) v := by
    simp only [circuit_norm, subcircuit, circuit, elaborated]
  rw [hout]
  exact eval_outState_congr
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    (eval_varFromOffset_of_agreesBelow h_agree (by omega))
    h_input

end ComputableWitness

end Round

end Solution.SHA256CompressGF2
