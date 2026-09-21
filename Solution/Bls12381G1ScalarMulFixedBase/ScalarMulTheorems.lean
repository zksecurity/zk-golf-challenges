import Solution.Bls12381G1ScalarMulFixedBase.Step
import Solution.Bls12381G1ScalarMulFixedBase.ToBytes

/-!
# Helper lemmas for `ScalarMul`

Gadget support for the `ScalarMul` soundness/completeness proofs, mirroring the
`SHA256Rounds`/`SHA256RoundsTheorems` split:

* concrete-offset descriptions of the subcircuit outputs (`step_output`,
  `toBytes_output`, `mux_output`) and lengths (`step_localLength`, ...);
* `accVar`, the variable-level fold accumulator after `k` steps, with the
  bridging lemmas from `Circuit.FoldlM.foldlAcc` / `Fin.foldl`;
* `specAcc`, the value-level accumulator of the trusted spec, with the
  bridge to `Specs.ShortWeierstrass.scalarMul`;
* `fold_sound`, the fold induction shared by soundness and completeness:
  if every step satisfies `Step.circuit`'s spec, the evaluated accumulator
  stays `Valid` and decodes to the spec-level partial scalar multiple;
* byte-vector value lemmas for the output boundary (`fromLimbs` of a
  reversed/zero byte vector).
-/

namespace Solution.Bls12381G1ScalarMulFixedBase
namespace ScalarMul

/-! ## The output encoding -/

/-- Outputs of `ScalarMul`: each coordinate as 48 big-endian bytes (`x[0]` is
the most significant byte), plus the boolean is-infinity flag. Coordinate
bytes are zero when the flag is set. -/
structure Outputs (F : Type) where
  x : Vector F coordBytes
  y : Vector F coordBytes
  isInf : F
deriving ProvableStruct

/-- Natural-number value of a big-endian byte-encoded coordinate. -/
def coordVal (v : Vector (F circomPrime) coordBytes) : ℕ :=
  Limbs.fromLimbs 8 ((v.toList.map ZMod.val).reverse)

/-- Well-formed output encoding: all coordinate entries are bytes, the
encoded values are canonical (`< P381`), the flag is boolean, and the
coordinate bytes are zero when the flag is set — so each group element has
exactly one wire encoding. -/
def Outputs.Valid (out : Outputs (F circomPrime)) : Prop :=
  (∀ i : Fin coordBytes, (out.x[i]).val < 256) ∧
  (∀ i : Fin coordBytes, (out.y[i]).val < 256) ∧
  IsBool out.isInf ∧
  coordVal out.x < P381 ∧ coordVal out.y < P381 ∧
  (out.isInf = 1 →
    (∀ i : Fin coordBytes, out.x[i] = 0) ∧ (∀ i : Fin coordBytes, out.y[i] = 0))

/-- Decode the byte-encoded output to a spec-level group point. -/
def decodeOutput (out : Outputs (F circomPrime)) :
    Specs.ShortWeierstrass.GroupPoint Specs.Bls12381G1.Fp :=
  if out.isInf = 1 then .infinity
  else .affine
    { x := ((coordVal out.x : ℕ) : Specs.Bls12381G1.Fp),
      y := ((coordVal out.y : ℕ) : Specs.Bls12381G1.Fp) }

/-! ## Concrete offsets of the subcircuits -/

lemma step_localLength (inp : Var Step.Inputs (F circomPrime)) :
    Step.circuit.localLength inp = 49099 := rfl

set_option maxRecDepth 8192 in
lemma step_output (inp : Var Step.Inputs (F circomPrime)) (n : ℕ) :
    Step.circuit.output inp n = varFromOffset FlaggedPoint (n + 49086) := by
  show Step.elaborated.output inp n = _
  congr 1
  rfl

/-- `varFromOffset` on a `FlaggedPoint`, written out as a record of witness
blocks. The `varFromOffset` spelling does not reduce cheaply (it goes through the
`ProvableStruct` `fromComponents`/`Vector.take` machinery), so a struct field
holding it makes the `circuit_norm` struct-eval simprocs — which validate their
rewrites by `isDefEq` at `.all` transparency — blow the whnf budget. The record
form reduces in constant time. -/
lemma flaggedPointVar_mk (m : ℕ) :
    ({ x := Vector.mapRange numLimbs fun j => var { index := m + j },
       y := Vector.mapRange numLimbs fun j => var { index := m + numLimbs + j },
       isInf := var { index := m + numLimbs + numLimbs } } :
      Var FlaggedPoint (F circomPrime)) = varFromOffset FlaggedPoint m := by
  simp only [circuit_norm, explicit_provable_type]

set_option maxRecDepth 8192 in
/-- `Step`'s output in the record form of `flaggedPointVar_mk`. Fed to
`circuit_proof_start` so the fold body of `ScalarMul.main` normalizes to a term
that ignores the running accumulator and is cheap to `whnf`; without it the
struct-eval simprocs have to reduce a 255-fold nesting of `Step.circuit.output`
applications. -/
lemma step_output_mk (inp : Var Step.Inputs (F circomPrime)) (n : ℕ) :
    Step.circuit.output inp n =
      ({ x := Vector.mapRange numLimbs fun j => var { index := n + 49086 + j },
         y := Vector.mapRange numLimbs fun j => var { index := n + 49086 + numLimbs + j },
         isInf := var { index := n + 49086 + numLimbs + numLimbs } } :
        FlaggedPoint (Expression (F circomPrime))) := by
  rw [step_output, flaggedPointVar_mk]

/-- `eval` of a `FlaggedPoint` variable, decomposed field-wise. The struct-eval
simprocs keep `eval` of a non-literal folded as a row-level atom, so bridge it
explicitly wherever a field-wise statement is needed. -/
lemma eval_flaggedPoint_mk (env : Environment (F circomPrime))
    (v : Var FlaggedPoint (F circomPrime)) :
    ProvableStruct.eval env v =
      { x := Vector.map (Expression.eval env) v.x,
        y := Vector.map (Expression.eval env) v.y,
        isInf := Expression.eval env v.isInf } := by
  obtain ⟨x, y, isInf⟩ := v
  simp only [circuit_norm]

lemma toBytes_localLength (x : Var Emu (F circomPrime)) :
    ToBytes.circuit.localLength x = 432 := rfl

lemma toBytes_output (x : Var Emu (F circomPrime)) (n : ℕ) :
    ToBytes.circuit.output x n = varFromOffset (fields coordBytes) n := rfl

lemma mux_localLength (inp : Var (Mux.Inputs (fields coordBytes)) (F circomPrime)) :
    (Mux.circuit (M := fields coordBytes)).localLength inp = 48 := rfl

lemma mux_output (inp : Var (Mux.Inputs (fields coordBytes)) (F circomPrime)) (n : ℕ) :
    (Mux.circuit (M := fields coordBytes)).output inp n
      = varFromOffset (fields coordBytes) n := rfl

/-! ## The variable-level fold accumulator -/

/-- The variable-level accumulator after `k` fold steps: the initial constant
point at infinity for `k = 0`, and step `k`'s output witness block (`Step`'s
output lives at offset `49086` within its `49099` cells) afterwards. -/
def accVar (i₀ : ℕ) : ℕ → Var FlaggedPoint (F circomPrime)
  | 0 => infConst
  | k + 1 => varFromOffset FlaggedPoint (i₀ + k * 49099 + 49086)

/-- `Step`'s output at the `k`-th fold offset is the `k+1`-st accumulator. -/
lemma step_output_accVar (inp : Var Step.Inputs (F circomPrime)) (i₀ k : ℕ) :
    Step.circuit.output inp (i₀ + k * 49099) = accVar i₀ (k + 1) :=
  step_output inp _

/-- A `Fin.foldl` whose body ignores the accumulator returns the last value. -/
private lemma fin_foldl_ignore_acc {α : Type} (k : ℕ) (f : ℕ → α) (init : α) :
    Fin.foldl (k + 1) (fun _ i => f i.val) init = f k := by
  rw [Fin.foldl_succ_last]
  simp

/-- The concrete `Fin.foldl` over step outputs equals `accVar` (the binder is
annotated `FlaggedPoint (Expression _)`, not the `Var` alias, to match goals
syntactically). -/
lemma fin_foldl_eq_accVar (i₀ : ℕ) (k : ℕ) :
    Fin.foldl k (fun (_ : FlaggedPoint (Expression (F circomPrime))) (j : Fin k) =>
      varFromOffset FlaggedPoint (i₀ + j.val * 49099 + 49086)) infConst = accVar i₀ k := by
  cases k with
  | zero => simp [Fin.foldl_zero, accVar]
  | succ k => exact fin_foldl_ignore_acc k (fun v => varFromOffset FlaggedPoint (i₀ + v * 49099 + 49086)) infConst

set_option maxRecDepth 8192 in
/-- The is-infinity flag of the final accumulator is the last cell of the last
step's witness block. Used to state `ScalarMul.elaborated`'s output without a
`FlaggedPoint` projection (which `whnf` cannot reduce cheaply). -/
lemma accVar_isInf (i₀ : ℕ) :
    (accVar i₀ Specs.Bls12381G1.scalarBits).isInf
      = (var { index := i₀ + 12520232 + 12 } : Expression (F circomPrime)) := by
  rw [show accVar i₀ Specs.Bls12381G1.scalarBits
      = varFromOffset FlaggedPoint (i₀ + 12520232) from rfl]
  simp only [circuit_norm, explicit_provable_type]
  norm_num [numLimbs]

set_option maxRecDepth 8192 in
/-- `accVar_isInf` in the evaluated form the goal carries after
`circuit_proof_start` (which normalizes `Expression.eval env (var _)` to
`Environment.get`). -/
lemma env_get_eq_accVar_isInf (env : Environment (F circomPrime)) (i₀ : ℕ) :
    env.get (i₀ + 12520232 + 12) = Expression.eval env (accVar i₀ 255).isInf := by
  rw [show (255 : ℕ) = Specs.Bls12381G1.scalarBits from rfl, accVar_isInf]
  rfl

/-- `Circuit.FoldlM.foldlAcc` of the `ScalarMul` fold body equals `accVar`.
Stated over a generic `i : Fin scalarBits` so it can rewrite under binders.

Uses `FlaggedPoint (Expression (F circomPrime))` for the accumulator type (not
the `Var FlaggedPoint (F circomPrime)` alias) so the pattern matches `h_holds`
syntactically — `simp`/`rw` can't see through the alias in binder types. -/
lemma foldlAcc_eq_accVar (i₀ : ℕ) (px py : Emu (Expression (F circomPrime)))
    (bits : Vector (Expression (F circomPrime)) Specs.Bls12381G1.scalarBits)
    (i : Fin Specs.Bls12381G1.scalarBits) :
    Circuit.FoldlM.foldlAcc (β := FlaggedPoint (Expression (F circomPrime))) i₀
      (Vector.finRange Specs.Bls12381G1.scalarBits)
      (fun acc j => subcircuit Step.circuit { acc := acc, px := px, py := py, bit := bits[j.val] })
      infConst i = accVar i₀ i.val := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  simp only [circuit_norm]
  simp only [step_localLength, step_output]
  exact fin_foldl_eq_accVar i₀ i.val

/-- `Circuit.FoldlM.foldlAcc` of the `ScalarMul` fold body equals `accVar`,
stated with the loop binder `bit := bits[j]` (`Fin`-indexed), matching the
`main` fold body syntactically for the `computableWitnesses` proof. -/
lemma foldlAcc_eq_accVar_main (i₀ : ℕ) (px py : Emu (Expression (F circomPrime)))
    (bits : Vector (Expression (F circomPrime)) Specs.Bls12381G1.scalarBits)
    (i : Fin Specs.Bls12381G1.scalarBits) :
    Circuit.FoldlM.foldlAcc (β := Var FlaggedPoint (F circomPrime)) i₀
      (Vector.finRange Specs.Bls12381G1.scalarBits)
      (fun (acc : Var FlaggedPoint (F circomPrime)) (j : Fin Specs.Bls12381G1.scalarBits) =>
        subcircuit Step.circuit { acc := acc, px := px, py := py, bit := bits[j] })
      infConst i = accVar i₀ i.val := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  simp only [circuit_norm]
  simp only [step_localLength, step_output]
  exact fin_foldl_eq_accVar i₀ i.val

/-! ## Computable-witness support -/

/-- A fresh `FlaggedPoint` witness block reads only its own `size FlaggedPoint`
cells, so it is stable across environments agreeing below `off + size`. -/
private lemma fpVar_stable {off k : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow k env') (hk : off + 13 ≤ k) :
    eval env ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))))
      = eval env' ((varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime)))) := by
  rw [CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint),
    CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint), ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi,
    ← ProvableType.getElem_eval_toElements
      (varFromOffset FlaggedPoint off : FlaggedPoint (Expression (F circomPrime))) i hi]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange,
    Expression.eval]
  have hsz : size FlaggedPoint = 13 := rfl
  rw [hsz] at hi
  exact h_agree (off + i) (by omega)

/-- The variable-level fold accumulator after `k` steps is stable across
environments agreeing below `i₀ + k * 49099` (the offset just past step `k`'s
witness block): for `k = 0` it is the constant point at infinity, and for
`k ≥ 1` it is a fresh 13-cell block ending exactly at `i₀ + k * 49099`. -/
lemma eval_accVar_of_agreesBelow (i₀ k : ℕ) {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow (i₀ + k * 49099) env') :
    eval env (accVar i₀ k) = eval env' (accVar i₀ k) := by
  cases k with
  | zero =>
    simp only [accVar]
    rw [CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint),
      CircuitType.eval_expression_prover_to_verifier (M := FlaggedPoint), ProvableType.ext_iff]
    intro i hi
    rw [← ProvableType.getElem_eval_toElements
        (infConst : Var FlaggedPoint (F circomPrime)) i hi,
      ← ProvableType.getElem_eval_toElements
        (infConst : Var FlaggedPoint (F circomPrime)) i hi]
    have hsz : size FlaggedPoint = 13 := rfl
    rw [hsz] at hi
    rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|i <;> first | rfl | omega
  | succ k =>
    simp only [accVar]
    exact fpVar_stable h_agree (by omega)

/-- The `x` coordinate of the fold accumulator is stable under agreement. -/
lemma eval_accVar_x_of_agreesBelow (i₀ k : ℕ) {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow (i₀ + k * 49099) env') :
    eval env (accVar i₀ k).x = eval env' (accVar i₀ k).x := by
  exact (eval_flaggedPoint_parts (eval_accVar_of_agreesBelow i₀ k h_agree)).1

/-- The `y` coordinate of the fold accumulator is stable under agreement. -/
lemma eval_accVar_y_of_agreesBelow (i₀ k : ℕ) {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow (i₀ + k * 49099) env') :
    eval env (accVar i₀ k).y = eval env' (accVar i₀ k).y := by
  exact (eval_flaggedPoint_parts (eval_accVar_of_agreesBelow i₀ k h_agree)).2.1

/-- The is-infinity flag of the fold accumulator is stable under agreement. -/
lemma eval_accVar_isInf_of_agreesBelow (i₀ k : ℕ) {env env' : ProverEnvironment (F circomPrime)}
    (h_agree : env.AgreesBelow (i₀ + k * 49099) env') :
    Expression.eval env.toEnvironment (accVar i₀ k).isInf
      = Expression.eval env'.toEnvironment (accVar i₀ k).isInf := by
  exact (eval_flaggedPoint_parts (eval_accVar_of_agreesBelow i₀ k h_agree)).2.2

set_option maxRecDepth 8192 in
/-- The fold term as it appears in the *goal* after `circuit_proof_start` +
numeral normalization (the elaborated output unfolds `varFromOffset` to
`Vector.mapRange`, with the step offset split as `24543 + 24543`), rewritten
to `accVar`. -/
lemma fin_foldl_goal_eq_accVar (i₀ : ℕ) :
    Fin.foldl Specs.Bls12381G1.scalarBits
      (fun (_ : FlaggedPoint (Expression (F circomPrime)))
           (i : Fin Specs.Bls12381G1.scalarBits) =>
        ({ x := Vector.mapRange numLimbs
             (fun j => var { index := i₀ + i.val * 49099 + 24543 + 24543 + j }),
           y := Vector.mapRange numLimbs
             (fun j => var { index := i₀ + i.val * 49099 + 24543 + 24543 + 6 + j }),
           isInf := var { index := i₀ + i.val * 49099 + 24543 + 24543 + 6 + 6 } } :
          FlaggedPoint (Expression (F circomPrime))))
      infConst = accVar i₀ Specs.Bls12381G1.scalarBits := by
  rw [show (Specs.Bls12381G1.scalarBits : ℕ) = 254 + 1 from rfl,
    fin_foldl_ignore_acc 254
      (fun v =>
        ({ x := Vector.mapRange numLimbs
                  (fun j => var { index := i₀ + v * 49099 + 24543 + 24543 + j }),
           y := Vector.mapRange numLimbs
                  (fun j => var { index := i₀ + v * 49099 + 24543 + 24543 + 6 + j }),
           isInf := var { index := i₀ + v * 49099 + 24543 + 24543 + 6 + 6 } } :
          FlaggedPoint (Expression (F circomPrime))))]
  show _ = varFromOffset FlaggedPoint (i₀ + 254 * 49099 + 49086)
  simp only [circuit_norm, explicit_provable_type, FlaggedPoint.mk.injEq]
  norm_num [numLimbs]

/-! ## The value-level spec accumulator -/

/-- The spec-level accumulator after `k` double-and-add steps, the value
mirror of `accVar` (cf. `valStateAfterRound` in `SHA256Rounds`). -/
def specAcc (bits : Vector ℕ Specs.Bls12381G1.scalarBits)
    (P : Specs.ShortWeierstrass.Point Specs.Bls12381G1.Fp) :
    ℕ → Specs.ShortWeierstrass.GroupPoint Specs.Bls12381G1.Fp
  | 0 => .infinity
  | k + 1 =>
    if h : k < Specs.Bls12381G1.scalarBits then
      Specs.ShortWeierstrass.step Specs.Bls12381G1.curve P (specAcc bits P k) (bits[k]'h)
    else specAcc bits P k

/-- `Fin.foldl` as a `List.foldl` over `List.finRange`. Restated locally: clean's
`Utils/Misc.lean` dropped `Fin.foldl_eq_foldl_finRange` in the 4.32 bump. -/
private lemma fin_foldl_eq_foldl_finRange {α : Type} (n : ℕ) (f : α → Fin n → α) (init : α) :
    Fin.foldl n f init = (List.finRange n).foldl f init := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    simp only [Fin.foldl_succ, List.finRange_succ, List.foldl_cons]
    specialize ih (fun x i => f x i.succ) (f init 0)
    rw [ih, List.foldl_map]

private lemma vector_foldl_eq_fin_foldl {α β : Type} {n : ℕ} (v : Vector α n)
    (f : β → α → β) (init : β) :
    v.foldl f init = Fin.foldl n (fun acc i => f acc v[i]) init := by
  have h1 : v.foldl f init = v.toList.foldl f init := by
    cases v; simp [Vector.foldl, Array.foldl_toList]
  have h2 : List.map (fun i : Fin n => v[i]) (List.finRange n) = v.toList := by
    apply List.ext_getElem <;> simp
  rw [h1, ← h2, List.foldl_map, fin_foldl_eq_foldl_finRange]

/-- The trusted spec's `scalarMul` is `specAcc` at the full bit length. -/
lemma scalarMul_eq_specAcc (bits : Vector ℕ Specs.Bls12381G1.scalarBits)
    (P : Specs.ShortWeierstrass.Point Specs.Bls12381G1.Fp) :
    Specs.ShortWeierstrass.scalarMul Specs.Bls12381G1.curve bits P =
      specAcc bits P Specs.Bls12381G1.scalarBits := by
  rw [Specs.ShortWeierstrass.scalarMul, vector_foldl_eq_fin_foldl]
  suffices h : ∀ k (hk : k ≤ Specs.Bls12381G1.scalarBits),
      Fin.foldl k (fun acc (i : Fin k) =>
        Specs.ShortWeierstrass.step Specs.Bls12381G1.curve P acc
          (bits[i.val]'(by have := i.isLt; omega))) .infinity
        = specAcc bits P k by
    exact h Specs.Bls12381G1.scalarBits (le_refl _)
  intro k hk
  induction k with
  | zero => simp [specAcc, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, specAcc,
      dif_pos (by omega : k < Specs.Bls12381G1.scalarBits)]
    have hk' : k ≤ Specs.Bls12381G1.scalarBits := by omega
    rw [show Fin.foldl k (fun acc (i : Fin k) =>
        Specs.ShortWeierstrass.step Specs.Bls12381G1.curve P acc
          (bits[i.castSucc.val]'(by have := i.isLt; omega))) .infinity =
      Fin.foldl k (fun acc (i : Fin k) =>
        Specs.ShortWeierstrass.step Specs.Bls12381G1.curve P acc
          (bits[i.val]'(by have := i.isLt; omega))) .infinity from rfl, ih hk']
    simp [Fin.val_last]

/-! ## The initial accumulator -/

/-- The evaluated initial accumulator is a valid flagged point. -/
lemma evalInf_valid (env : Environment (F circomPrime)) :
    FlaggedPoint.Valid
      { x := Vector.map (Expression.eval env) infConst.x,
        y := Vector.map (Expression.eval env) infConst.y,
        isInf := Expression.eval env infConst.isInf } := by
  have hx : Vector.map (Expression.eval env) infConst.x = emuOfNat 0 :=
    DivOrZero.eval_zeroConst env
  have hy : Vector.map (Expression.eval env) infConst.y = emuOfNat 0 :=
    DivOrZero.eval_zeroConst env
  have h1 : Expression.eval env infConst.isInf = 1 := rfl
  rw [hx, hy, h1]
  exact ⟨Or.inr rfl, DivOrZero.fe_valid_emuOfNat DivOrZero.P381_pos,
    DivOrZero.fe_valid_emuOfNat DivOrZero.P381_pos,
    fun h => absurd h one_ne_zero⟩

/-- The evaluated initial accumulator decodes to the point at infinity. -/
lemma decode_evalInf (env : Environment (F circomPrime)) :
    decodePoint
      { x := Vector.map (Expression.eval env) infConst.x,
        y := Vector.map (Expression.eval env) infConst.y,
        isInf := Expression.eval env infConst.isInf } = .infinity := by
  rw [decodePoint]
  exact if_pos rfl

/-! ## Output-boundary byte lemmas -/

/-- The big-endian reindexing in the goal (`var {index := M + (47 - i)}`) is
the pointwise big-endian view of the evaluated mux output block. -/
lemma map_eval_ofFn_rev (env : Environment (F circomPrime)) (M : ℕ) :
    Vector.map (Expression.eval env)
      (Vector.ofFn fun i : Fin coordBytes =>
        (var { index := M + (47 - i.val) } : Expression (F circomPrime))) =
    Vector.ofFn (fun i : Fin coordBytes =>
      (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) M))[47 - i.val]'(by
          simp only [coordBytes]; omega)) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map, Vector.getElem_ofFn,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange]

/-- `fromLimbs` of the reversed big-endian reindexing is `fromLimbs` of the
underlying little-endian vector (the `coordVal` output-boundary bridge). -/
lemma fromLimbs_rev_ofFn (w : Vector (F circomPrime) coordBytes) :
    Limbs.fromLimbs 8
      (((Vector.ofFn fun i : Fin coordBytes =>
          w[47 - i.val]'(by simp only [coordBytes]; omega)).toList.map
        ZMod.val).reverse) =
      Limbs.fromLimbs 8 (w.toList.map ZMod.val) := by
  refine congrArg (Limbs.fromLimbs 8) ?_
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_reverse, List.getElem_map, Vector.toList_ofFn,
      List.getElem_ofFn, Vector.getElem_toList]
    simp only [List.length_map, List.length_ofFn, List.length_reverse,
      Vector.length_toList, coordBytes] at h1 h2 ⊢
    simp only [show (47 : ℕ) - (48 - 1 - j) = j from by omega]

/-- `fromLimbs` of an all-zero list is zero. -/
lemma fromLimbs_replicate_zero (B n : ℕ) :
    Limbs.fromLimbs B (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Limbs.fromLimbs, List.foldr_cons,
      show List.foldr (fun limb acc => limb + acc * 2 ^ B) 0 (List.replicate n 0)
        = Limbs.fromLimbs B (List.replicate n 0) from rfl, ih]
    simp

/-- The evaluated `zeroBytes` constant is the all-zero byte vector. -/
lemma eval_zeroBytes_getElem (env : Environment (F circomPrime))
    (v : Var (fields coordBytes) (F circomPrime))
    (h : v = Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime)))
    (j : ℕ) (hj : j < coordBytes) :
    (Vector.map (Expression.eval env) v)[j]'hj = 0 := by
  subst h
  simp [Vector.getElem_ofFn, Expression.eval]

/-- The evaluated `zeroBytes` constant recomposes to zero. -/
lemma fromLimbs_eval_zeroBytes (env : Environment (F circomPrime))
    (v : Var (fields coordBytes) (F circomPrime))
    (h : v = Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime))) :
    Limbs.fromLimbs 8
      ((Vector.map (Expression.eval env) v).toList.map ZMod.val) = 0 := by
  subst h
  rw [show (Vector.map (Expression.eval env)
        (Vector.ofFn fun _ =>
          ((0 : F circomPrime) : Expression (F circomPrime)))).toList.map ZMod.val
      = List.replicate coordBytes 0 by
    apply List.ext_getElem <;> simp [Expression.eval]]
  exact fromLimbs_replicate_zero 8 coordBytes

/-! ## The fold invariant and the output boundary

The soundness argument, factored into standalone lemmas so each gets its own
heartbeat budget (the whole argument inside the single `soundness` theorem
exceeds the default limit, which this project does not raise). -/

set_option maxRecDepth 8192 in
/-- One step of the fold invariant: `Step.circuit`'s spec carries the
invariant from `k` to `k + 1` (factored out of `fold_invariant` for its own
heartbeat budget). -/
lemma fold_step (i₀ : ℕ) (env : Environment (F circomPrime))
    (input_bits : Vector (F circomPrime) Specs.Bls12381G1.scalarBits)
    (input_px input_py : Emu (F circomPrime))
    (input_var_bits : Vector (Expression (F circomPrime)) Specs.Bls12381G1.scalarBits)
    (h_bits : Vector.map (Expression.eval env) input_var_bits = input_bits)
    (hbits_bool : ∀ i : Fin Specs.Bls12381G1.scalarBits, IsBool input_bits[i])
    (hpx_valid : Fe.Valid input_px) (hpy_valid : Fe.Valid input_py)
    (honcurve : Specs.ShortWeierstrass.OnCurve Specs.Bls12381G1.curve
      { x := decodeFe input_px, y := decodeFe input_py })
    (k : ℕ) (hk'' : k < Specs.Bls12381G1.scalarBits)
    (ih_bool : IsBool (Expression.eval env (accVar i₀ k).isInf))
    (ih_fx : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ k).x))
    (ih_fy : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ k).y))
    (ih_curve : Expression.eval env (accVar i₀ k).isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Bls12381G1.curve
        { x := decodeFe (Vector.map (Expression.eval env) (accVar i₀ k).x),
          y := decodeFe (Vector.map (Expression.eval env) (accVar i₀ k).y) })
    (ih_dec : decodePoint
        { x := Vector.map (Expression.eval env) (accVar i₀ k).x,
          y := Vector.map (Expression.eval env) (accVar i₀ k).y,
          isInf := Expression.eval env (accVar i₀ k).isInf } =
      specAcc (Vector.map ZMod.val input_bits)
        { x := decodeFe input_px, y := decodeFe input_py } k)
    (h_step : Step.circuit.Assumptions
        { acc :=
            { x := Vector.map (Expression.eval env) (accVar i₀ k).x,
              y := Vector.map (Expression.eval env) (accVar i₀ k).y,
              isInf := Expression.eval env (accVar i₀ k).isInf },
          px := input_px, py := input_py,
          bit := Expression.eval env (input_var_bits[k]'hk'') } →
      Step.circuit.Spec
        { acc :=
            { x := Vector.map (Expression.eval env) (accVar i₀ k).x,
              y := Vector.map (Expression.eval env) (accVar i₀ k).y,
              isInf := Expression.eval env (accVar i₀ k).isInf },
          px := input_px, py := input_py,
          bit := Expression.eval env (input_var_bits[k]'hk'') }
        { x := Vector.map (Expression.eval env)
            (varFromOffset FlaggedPoint (i₀ + k * 49099 + 49086)).x,
          y := Vector.map (Expression.eval env)
            (varFromOffset FlaggedPoint (i₀ + k * 49099 + 49086)).y,
          isInf := Expression.eval env
            (varFromOffset FlaggedPoint (i₀ + k * 49099 + 49086)).isInf }) :
    IsBool (Expression.eval env (accVar i₀ (k + 1)).isInf) ∧
    Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ (k + 1)).x) ∧
    Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ (k + 1)).y) ∧
    (Expression.eval env (accVar i₀ (k + 1)).isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Bls12381G1.curve
        { x := decodeFe (Vector.map (Expression.eval env) (accVar i₀ (k + 1)).x),
          y := decodeFe (Vector.map (Expression.eval env) (accVar i₀ (k + 1)).y) }) ∧
    decodePoint
      { x := Vector.map (Expression.eval env) (accVar i₀ (k + 1)).x,
        y := Vector.map (Expression.eval env) (accVar i₀ (k + 1)).y,
        isInf := Expression.eval env (accVar i₀ (k + 1)).isInf } =
      specAcc (Vector.map ZMod.val input_bits)
        { x := decodeFe input_px, y := decodeFe input_py } (k + 1) := by
  unfold Step.circuit Step.Assumptions Step.Spec FlaggedPoint.Valid at h_step
  dsimp only [] at h_step
  have hbit : IsBool (Expression.eval env (input_var_bits[k]'hk'')) := by
    have h := hbits_bool ⟨k, hk''⟩
    rwa [← h_bits, Fin.getElem_fin, Vector.getElem_map] at h
  obtain ⟨hout_valid, hout_dec⟩ :=
    h_step ⟨⟨ih_bool, ih_fx, ih_fy, ih_curve⟩, hbit, hpx_valid, hpy_valid, honcurve⟩
  have hbits' : (Vector.map ZMod.val input_bits)[k]'hk'' =
      ZMod.val (Expression.eval env (input_var_bits[k]'hk'')) := by
    rw [← h_bits, Vector.getElem_map, Vector.getElem_map]
  simp only [accVar, specAcc, dif_pos hk'']
  refine ⟨hout_valid.1, hout_valid.2.1, hout_valid.2.2.1, hout_valid.2.2.2, ?_⟩
  rw [hout_dec, ih_dec, hbits']

/-- The inductive invariant along the double-and-add fold: after `k` steps
the evaluated accumulator is a well-formed flagged point that decodes to the
spec-level partial multiple `specAcc … k`. -/
lemma fold_invariant (i₀ : ℕ) (env : Environment (F circomPrime))
    (input_bits : Vector (F circomPrime) Specs.Bls12381G1.scalarBits)
    (input_px input_py : Emu (F circomPrime))
    (input_var_bits : Vector (Expression (F circomPrime)) Specs.Bls12381G1.scalarBits)
    (h_bits : Vector.map (Expression.eval env) input_var_bits = input_bits)
    (hbits_bool : ∀ i : Fin Specs.Bls12381G1.scalarBits, IsBool input_bits[i])
    (hpx_valid : Fe.Valid input_px) (hpy_valid : Fe.Valid input_py)
    (honcurve : Specs.ShortWeierstrass.OnCurve Specs.Bls12381G1.curve
      { x := decodeFe input_px, y := decodeFe input_py })
    (h_steps : ∀ i : Fin Specs.Bls12381G1.scalarBits,
      Step.circuit.Assumptions
        { acc :=
            { x := Vector.map (Expression.eval env) (accVar i₀ i.val).x,
              y := Vector.map (Expression.eval env) (accVar i₀ i.val).y,
              isInf := Expression.eval env (accVar i₀ i.val).isInf },
          px := input_px, py := input_py,
          bit := Expression.eval env input_var_bits[i.val] } →
      Step.circuit.Spec
        { acc :=
            { x := Vector.map (Expression.eval env) (accVar i₀ i.val).x,
              y := Vector.map (Expression.eval env) (accVar i₀ i.val).y,
              isInf := Expression.eval env (accVar i₀ i.val).isInf },
          px := input_px, py := input_py,
          bit := Expression.eval env input_var_bits[i.val] }
        { x := Vector.map (Expression.eval env)
            (varFromOffset FlaggedPoint (i₀ + i.val * 49099 + 49086)).x,
          y := Vector.map (Expression.eval env)
            (varFromOffset FlaggedPoint (i₀ + i.val * 49099 + 49086)).y,
          isInf := Expression.eval env
            (varFromOffset FlaggedPoint (i₀ + i.val * 49099 + 49086)).isInf }) :
    ∀ k, k ≤ Specs.Bls12381G1.scalarBits →
      IsBool (Expression.eval env (accVar i₀ k).isInf) ∧
      Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ k).x) ∧
      Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ k).y) ∧
      (Expression.eval env (accVar i₀ k).isInf = 0 →
        Specs.ShortWeierstrass.OnCurve Specs.Bls12381G1.curve
          { x := decodeFe (Vector.map (Expression.eval env) (accVar i₀ k).x),
            y := decodeFe (Vector.map (Expression.eval env) (accVar i₀ k).y) }) ∧
      decodePoint
        { x := Vector.map (Expression.eval env) (accVar i₀ k).x,
          y := Vector.map (Expression.eval env) (accVar i₀ k).y,
          isInf := Expression.eval env (accVar i₀ k).isInf } =
        specAcc (Vector.map ZMod.val input_bits)
          { x := decodeFe input_px, y := decodeFe input_py } k := by
  intro k hk
  induction k with
  | zero =>
    simp only [accVar]
    have hv := evalInf_valid env
    exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, by rw [decode_evalInf]; rfl⟩
  | succ k ih =>
    have hk' : k ≤ Specs.Bls12381G1.scalarBits := by omega
    have hk'' : k < Specs.Bls12381G1.scalarBits := by omega
    obtain ⟨ih_bool, ih_fx, ih_fy, ih_curve, ih_dec⟩ := ih hk'
    exact fold_step i₀ env input_bits input_px input_py input_var_bits h_bits
      hbits_bool hpx_valid hpy_valid honcurve k hk''
      ih_bool ih_fx ih_fy ih_curve ih_dec (h_steps ⟨k, hk''⟩)

/-! ## The output boundary -/

section OutputBoundary

variable (i₀ : ℕ) (env : Environment (F circomPrime))

set_option maxRecDepth 8192 in
/-- Output validity at the boundary: the big-endian reindexed, zero-masked
byte output is a well-formed encoding. -/
lemma output_valid
    (zb : Var (fields coordBytes) (F circomPrime))
    (hzb : zb = Vector.ofFn fun _ => ((0 : F circomPrime) : Expression (F circomPrime)))
    (hbool : IsBool (Expression.eval env (accVar i₀ 255).isInf))
    (hfx : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ 255).x))
    (hfy : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ 255).y))
    (hxb_bytes : ∀ i : Fin coordBytes,
      ZMod.val (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245)))[i] < 256)
    (hxb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 12520245))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 255).x))
    (hyb_bytes : ∀ i : Fin coordBytes,
      ZMod.val (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432)))[i] < 256)
    (hyb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 255).y))
    (hmx : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432 + 432)) =
      if Expression.eval env (accVar i₀ 255).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245)))
    (hmy : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432 + 432 + 48)) =
      if Expression.eval env (accVar i₀ 255).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432))) :
    Outputs.Valid
      { x := Vector.map (Expression.eval env)
          (Vector.ofFn fun i =>
            (var { index := i₀ + 12520245 + 432 + 432 + (47 - i.val) } :
              Expression (F circomPrime))),
        y := Vector.map (Expression.eval env)
          (Vector.ofFn fun i =>
            (var { index := i₀ + 12520245 + 432 + 432 + 48 + (47 - i.val) } :
              Expression (F circomPrime))),
        isInf := Expression.eval env (accVar i₀ 255).isInf } := by
  rw [map_eval_ofFn_rev env (i₀ + 12520245 + 432 + 432),
    map_eval_ofFn_rev env (i₀ + 12520245 + 432 + 432 + 48), hmx, hmy]
  simp only [Outputs.Valid]
  rcases hbool with hinf0 | hinf1
  · rw [hinf0, if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime))]
    refine ⟨?_, ?_, Or.inl rfl, ?_, ?_,
      fun h => absurd h (zero_ne_one (α := F circomPrime))⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact hxb_bytes ⟨47 - i.val, by simp only [coordBytes]; omega⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact hyb_bytes ⟨47 - i.val, by simp only [coordBytes]; omega⟩
    · simp only [coordVal, fromLimbs_rev_ofFn, hxb_val]
      exact hfx.2
    · simp only [coordVal, fromLimbs_rev_ofFn, hyb_val]
      exact hfy.2
  · rw [hinf1, if_pos rfl, if_pos rfl]
    refine ⟨?_, ?_, Or.inr rfl, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]
      simp
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]
      simp
    · simp only [coordVal, fromLimbs_rev_ofFn, fromLimbs_eval_zeroBytes env zb hzb]
      exact DivOrZero.P381_pos
    · simp only [coordVal, fromLimbs_rev_ofFn, fromLimbs_eval_zeroBytes env zb hzb]
      exact DivOrZero.P381_pos
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]

set_option maxRecDepth 8192 in
/-- The decoded output at the boundary satisfies the trusted total spec. -/
lemma output_spec
    (input_bits : Vector (F circomPrime) Specs.Bls12381G1.scalarBits)
    (input_px input_py : Emu (F circomPrime))
    (zb : Var (fields coordBytes) (F circomPrime))
    (hbool : IsBool (Expression.eval env (accVar i₀ 255).isInf))
    (hdec256 : decodePoint
        { x := Vector.map (Expression.eval env) (accVar i₀ 255).x,
          y := Vector.map (Expression.eval env) (accVar i₀ 255).y,
          isInf := Expression.eval env (accVar i₀ 255).isInf } =
      specAcc (Vector.map ZMod.val input_bits)
        { x := decodeFe input_px, y := decodeFe input_py } 255)
    (hxb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 12520245))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 255).x))
    (hyb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 255).y))
    (hmx : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432 + 432)) =
      if Expression.eval env (accVar i₀ 255).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245)))
    (hmy : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432 + 432 + 48)) =
      if Expression.eval env (accVar i₀ 255).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 12520245 + 432))) :
    Specs.ShortWeierstrass.Spec Specs.Bls12381G1.curve
      (Vector.map ZMod.val input_bits)
      { x := decodeFe input_px, y := decodeFe input_py }
      (decodeOutput
        { x := Vector.map (Expression.eval env)
            (Vector.ofFn fun i =>
              (var { index := i₀ + 12520245 + 432 + 432 + (47 - i.val) } :
                Expression (F circomPrime))),
          y := Vector.map (Expression.eval env)
            (Vector.ofFn fun i =>
              (var { index := i₀ + 12520245 + 432 + 432 + 48 + (47 - i.val) } :
                Expression (F circomPrime))),
          isInf := Expression.eval env (accVar i₀ 255).isInf }) := by
  rw [map_eval_ofFn_rev env (i₀ + 12520245 + 432 + 432),
    map_eval_ofFn_rev env (i₀ + 12520245 + 432 + 432 + 48)]
  unfold Specs.ShortWeierstrass.Spec
    decodeOutput
  unfold decodePoint at hdec256
  rw [scalarMul_eq_specAcc, hmx, hmy]
  rcases hbool with hinf0 | hinf1
  · rw [hinf0] at hdec256 ⊢
    rw [if_neg (zero_ne_one (α := F circomPrime))] at hdec256
    rw [if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime))]
    rw [show specAcc (Vector.map ZMod.val input_bits)
          { x := decodeFe input_px, y := decodeFe input_py }
          Specs.Bls12381G1.scalarBits =
        specAcc (Vector.map ZMod.val input_bits)
          { x := decodeFe input_px, y := decodeFe input_py } 255 from rfl,
      ← hdec256]
    simp only [coordVal, fromLimbs_rev_ofFn, hxb_val, hyb_val, decodeFe]
  · rw [hinf1] at hdec256 ⊢
    rw [if_pos rfl] at hdec256
    rw [if_pos rfl]
    rw [show specAcc (Vector.map ZMod.val input_bits)
          { x := decodeFe input_px, y := decodeFe input_py }
          Specs.Bls12381G1.scalarBits =
        specAcc (Vector.map ZMod.val input_bits)
          { x := decodeFe input_px, y := decodeFe input_py } 255 from rfl]
    exact hdec256.symm
end OutputBoundary

end ScalarMul
end Solution.Bls12381G1ScalarMulFixedBase
