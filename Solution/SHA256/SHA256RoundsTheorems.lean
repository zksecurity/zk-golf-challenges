import Solution.SHA256.SHA256Round
import Challenge.Utils.ComputableWitnessLemmas
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^33)]

namespace Solution.SHA256
namespace SHA256Rounds

/-!
# Helper definitions and lemmas for `SHA256Rounds`

The variable- and value-level descriptions of the 64-round accumulator, plus the
lemmas relating the `foldl` accumulator and the spec to them. These are gadget
support for `SHA256Rounds`; the gadget file keeps the six required declarations.
-/

/-- The variable-level state after `k` rounds. Used as the explicit `output` for the
    SHA256Rounds elaborated instance, mirroring how Keccak Permutation provides `stateVar`. -/
def stateVar (i₀ : ℕ) (input_var_state : Var SHA256State (F p)) :
    ℕ → Var SHA256State (F p)
  | 0 => input_var_state
  | k + 1 =>
    let prev := stateVar i₀ input_var_state k
    #v[Vector.mapRange 32 fun j => var { index := i₀ + k * 455 + 389 + j },
       prev[0], prev[1], prev[2],
       Vector.mapRange 32 fun j => var { index := i₀ + k * 455 + 422 + j },
       prev[4], prev[5], prev[6]]

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 33)] in
/-- Generic version of `output_eq`: for any bound `k`, the `Fin.foldl k` over our round body
    equals `stateVar i₀ input_var_state k`. -/
lemma fin_foldl_eq_stateVar (i₀ : ℕ) (input_var_state : Var SHA256State (F p)) (k : ℕ) :
    Fin.foldl k
      (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
        #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 455 + 389 + i_1 },
           acc[0], acc[1], acc[2],
           Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 455 + 422 + i_1 },
           acc[4], acc[5], acc[6]]) input_var_state =
      stateVar i₀ input_var_state k := by
  induction k with
  | zero => simp [stateVar, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last]
    rw [stateVar]
    rw [show Fin.foldl k
        (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
          #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 455 + 389 + i_1 },
             acc[0], acc[1], acc[2],
             Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 455 + 422 + i_1 },
             acc[4], acc[5], acc[6]]) input_var_state =
        Fin.foldl k
          (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
            #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 455 + 389 + i_1 },
               acc[0], acc[1], acc[2],
               Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 455 + 422 + i_1 },
               acc[4], acc[5], acc[6]]) input_var_state from rfl, ih]

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 64` equals `stateVar i₀ input_var_state k`.

    Uses `SHA256State (Expression (F p))` for the accumulator type (not the
    `Var SHA256State (F p)` alias) so the lemma's pattern matches `h_holds`
    syntactically — `rw` can't see through the alias. -/
lemma foldlAcc_eq_stateVar (i₀ : ℕ)
    (input_var_state : SHA256State (Expression (F p)))
    (input_var_schedule : SHA256Schedule (Expression (F p)))
    (k : ℕ) (h : k < 64) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀ (Vector.finRange 64)
      (fun s (i : Fin 64) => subcircuit SHA256Round.circuit
        { state := s,
          k := constWord32 (Specs.SHA256.K[i.val]'i.isLt).toNat,
          w := input_var_schedule[i.val]'i.isLt })
      input_var_state ⟨k, h⟩ =
        stateVar i₀ input_var_state k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVar _ _ _

lemma foldlAcc_eq_stateVar_main (i₀ : ℕ)
    (input_var_state : SHA256State (Expression (F p)))
    (input_var_schedule : SHA256Schedule (Expression (F p)))
    (i : Fin 64) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀ (Vector.finRange 64)
      (fun s i => subcircuit SHA256Round.circuit
        { state := s,
          k := constWord32 (Specs.SHA256.K[i].toNat),
          w := input_var_schedule[i] })
      input_var_state i =
        stateVar i₀ input_var_state i.val := by
  simpa only using foldlAcc_eq_stateVar i₀ input_var_state input_var_schedule i.val i.isLt

omit [Fact (p > 2 ^ 33)] in
lemma eval_mem_stateVar_of_agreesBelow {offset k : ℕ}
    {env env' : ProverEnvironment (F p)}
    {input_var_state : SHA256State (Expression (F p))}
    (hk : k ≤ 64)
    (h_agree : env.AgreesBelow (offset + k * 455) env')
    (h_input_state : eval env.toEnvironment input_var_state =
      eval env'.toEnvironment input_var_state) :
    ∀ (j : ℕ) (hj : j < 8),
      ∀ a ∈ (stateVar offset input_var_state k)[j]'hj,
        Expression.eval env.toEnvironment a =
          Expression.eval env'.toEnvironment a := by
  induction k with
  | zero =>
      intro j hj a ha
      have hword : Vector.map (Expression.eval env.toEnvironment) (input_var_state[j]'hj) =
          Vector.map (Expression.eval env'.toEnvironment) (input_var_state[j]'hj) := by
        rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[j]'hj),
          ← CircuitType.eval_var_fields env'.toEnvironment (input_var_state[j]'hj)]
        have h := congrArg (fun s : SHA256State (F p) => s[j]'hj) h_input_state
        simpa [getElem_eval_vector] using h
      simp only [Vector.mem_iff_getElem] at ha
      rcases ha with ⟨i, hi, hget⟩
      rw [← hget]
      simpa [Vector.getElem_map] using Vector.ext_iff.mp hword i hi
  | succ k ih =>
      intro j hj a ha
      have hprev : env.AgreesBelow (offset + k * 455) env' :=
        ProverEnvironment.agreesBelow_of_le h_agree (by omega)
      have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
          j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
      rcases hj_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [stateVar] at ha
        exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
          (offset := offset + k * 455 + 389) (m := 32) h_agree (by omega) a ha
      · simpa [stateVar] using ih (by omega) hprev 0 (by omega) a ha
      · simpa [stateVar] using ih (by omega) hprev 1 (by omega) a ha
      · simpa [stateVar] using ih (by omega) hprev 2 (by omega) a ha
      · simp [stateVar] at ha
        exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
          (offset := offset + k * 455 + 422) (m := 32) h_agree (by omega) a ha
      · simpa [stateVar] using ih (by omega) hprev 4 (by omega) a ha
      · simpa [stateVar] using ih (by omega) hprev 5 (by omega) a ha
      · simpa [stateVar] using ih (by omega) hprev 6 (by omega) a ha

omit [Fact (p > 2 ^ 33)] in
/-- Helper: `constWord32 n` evaluated is always normalized (bits are 0 or 1). -/
lemma normalized_constWord32 (env : Environment (F p)) (n : ℕ) :
    Normalized (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) := by
  intro i
  have h : (n / 2^i.val % 2 : ℕ) = 0 ∨ (n / 2^i.val % 2 : ℕ) = 1 := by omega
  rcases h with h | h
  · left
    simp [constWord32, Expression.eval, h]
  · right
    simp [constWord32, Expression.eval, h]

/-- valueBits of `constWord32 n` equals `n` modulo `2^32`. -/
lemma valueBits_constWord32 (env : Environment (F p)) (n : ℕ) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) = n % 2^32 := by
  simp only [valueBits, constWord32]
  have h2 : ∀ i : Fin 32, ((n / 2^i.val % 2 : ℕ) : F p).val = n / 2^i.val % 2 := by
    intro i
    have hp : 2^33 < p := Fact.out
    have hle : (n / 2^i.val % 2 : ℕ) ≤ 1 := by omega
    have hlt : (n / 2^i.val % 2 : ℕ) < p := by omega
    exact ZMod.val_natCast_of_lt hlt
  have heq : (∑ i : Fin 32, (Vector.map (Expression.eval env)
        (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F p))))[i].val * 2^i.val)
      = ∑ i : Fin 32, (n / 2^i.val % 2) * 2^i.val := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [show (Vector.map (Expression.eval env)
          (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F p))))[i] =
        ((n / 2^i.val % 2 : ℕ) : F p) from by
      simp [Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]]
    rw [h2 i]
  rw [heq]
  -- Standard bit-decomposition: ∑ i < 32, (n / 2^i % 2) * 2^i = n % 2^32
  have key : ∀ (m : ℕ), ∑ i : Fin m, (n / 2^i.val % 2) * 2^i.val = n % 2^m := by
    intro m
    induction m with
    | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty, pow_zero, Nat.mod_one]
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ih, Nat.mod_pow_succ]
      ring
  exact key 32

/-- For `n < 2^32`, valueBits of `constWord32 n` is `n`. -/
lemma valueBits_constWord32_of_lt (env : Environment (F p)) {n : ℕ} (h : n < 2^32) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) = n := by
  rw [valueBits_constWord32, Nat.mod_eq_of_lt h]

/-- The value-level state at the end of round `k`. -/
def valStateAfterRound (input_state : Vector ℕ 8)
    (input_schedule : Vector ℕ 64) : ℕ → Vector ℕ 8
  | 0 => input_state
  | k + 1 =>
    if h : k < 64 then
      let prev := valStateAfterRound input_state input_schedule k
      Specs.SHA256.sha256Round prev (Specs.SHA256.K[k]'h).toNat (input_schedule[k]'h)
    else
      valStateAfterRound input_state input_schedule k

/-- `sha256Compress` equals our `valStateAfterRound` at index 64. -/
lemma sha256Compress_eq_valStateAfterRound
    (input_state : Vector ℕ 8) (input_schedule : Vector ℕ 64) :
    Specs.SHA256.sha256Compress input_state input_schedule =
      valStateAfterRound input_state input_schedule 64 := by
  simp only [Specs.SHA256.sha256Compress]
  suffices h : ∀ k (hk : k ≤ 64),
      Fin.foldl k
        (fun s (i : Fin k) =>
          Specs.SHA256.sha256Round s
            (Specs.SHA256.K[i.val]'(by have := i.isLt; omega)).toNat
            (input_schedule[i.val]'(by have := i.isLt; omega))) input_state =
        valStateAfterRound input_state input_schedule k by
    have := h 64 (le_refl 64)
    convert this using 1
  intro k hk
  induction k with
  | zero => simp [valStateAfterRound, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, valStateAfterRound]
    rw [dif_pos (by omega : k < 64)]
    have hk' : k ≤ 64 := by omega
    specialize ih hk'
    rw [show Fin.foldl k
          (fun s (i : Fin k) =>
            Specs.SHA256.sha256Round s
              (Specs.SHA256.K[i.castSucc.val]'(by have := i.isLt; omega)).toNat
              (input_schedule[i.castSucc.val]'(by have := i.isLt; omega))) input_state =
        Fin.foldl k
          (fun s (i : Fin k) =>
            Specs.SHA256.sha256Round s
              (Specs.SHA256.K[i.val]'(by have := i.isLt; omega)).toNat
              (input_schedule[i.val]'(by have := i.isLt; omega))) input_state from rfl, ih]
    simp [Fin.val_last]

end SHA256Rounds
end Solution.SHA256
end
