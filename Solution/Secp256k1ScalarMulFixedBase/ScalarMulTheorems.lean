import Solution.Secp256k1ScalarMulFixedBase.Step
import Solution.Secp256k1ScalarMulFixedBase.ToBytes

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

namespace Solution.Secp256k1ScalarMulFixedBase
namespace ScalarMul

/-! ## The output encoding -/

/-- Outputs of `ScalarMul`: each coordinate as 32 big-endian bytes (`x[0]` is
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
encoded values are canonical (`< P256`), the flag is boolean, and the
coordinate bytes are zero when the flag is set — so each group element has
exactly one wire encoding. -/
def Outputs.Valid (out : Outputs (F circomPrime)) : Prop :=
  (∀ i : Fin coordBytes, (out.x[i]).val < 256) ∧
  (∀ i : Fin coordBytes, (out.y[i]).val < 256) ∧
  IsBool out.isInf ∧
  coordVal out.x < P256 ∧ coordVal out.y < P256 ∧
  (out.isInf = 1 →
    (∀ i : Fin coordBytes, out.x[i] = 0) ∧ (∀ i : Fin coordBytes, out.y[i] = 0))

/-- Decode the byte-encoded output to a spec-level group point. -/
def decodeOutput (out : Outputs (F circomPrime)) :
    Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp :=
  if out.isInf = 1 then .infinity
  else .affine
    { x := ((coordVal out.x : ℕ) : Specs.Secp256k1.Fp),
      y := ((coordVal out.y : ℕ) : Specs.Secp256k1.Fp) }

/-! ## Concrete offsets of the subcircuits -/

lemma step_localLength (inp : Var Step.Inputs (F circomPrime)) :
    Step.circuit.localLength inp = 31959 := rfl

lemma step_output (inp : Var Step.Inputs (F circomPrime)) (n : ℕ) :
    Step.circuit.output inp n = varFromOffset FlaggedPoint (n + 31950) := by
  show Step.elaborated.output inp n = _
  simp only [Step.elaborated]
  norm_num [secpParams, numLimbs, limbBits]
  congr 1

lemma toBytes_localLength (x : Var Emu (F circomPrime)) :
    ToBytes.circuit.localLength x = 288 := rfl

lemma toBytes_output (x : Var Emu (F circomPrime)) (n : ℕ) :
    ToBytes.circuit.output x n = varFromOffset (fields coordBytes) n := rfl

lemma mux_localLength (inp : Var (Mux.Inputs (fields coordBytes)) (F circomPrime)) :
    (Mux.circuit (M := fields coordBytes)).localLength inp = 32 := rfl

lemma mux_output (inp : Var (Mux.Inputs (fields coordBytes)) (F circomPrime)) (n : ℕ) :
    (Mux.circuit (M := fields coordBytes)).output inp n
      = varFromOffset (fields coordBytes) n := rfl

/-! ## The variable-level fold accumulator -/

/-- The variable-level accumulator after `k` fold steps: the initial constant
point at infinity for `k = 0`, and step `k`'s output witness block (`Step`'s
output lives at offset `31950` within its `31959` cells) afterwards. -/
def accVar (i₀ : ℕ) : ℕ → Var FlaggedPoint (F circomPrime)
  | 0 => infConst
  | k + 1 => varFromOffset FlaggedPoint (i₀ + k * 31959 + 31950)

/-- `Step`'s output at the `k`-th fold offset is the `k+1`-st accumulator. -/
lemma step_output_accVar (inp : Var Step.Inputs (F circomPrime)) (i₀ k : ℕ) :
    Step.circuit.output inp (i₀ + k * 31959) = accVar i₀ (k + 1) :=
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
      varFromOffset FlaggedPoint (i₀ + j.val * 31959 + 31950)) infConst = accVar i₀ k := by
  cases k with
  | zero => simp [Fin.foldl_zero, accVar]
  | succ k => exact fin_foldl_ignore_acc k (fun v => varFromOffset FlaggedPoint (i₀ + v * 31959 + 31950)) infConst

/-- `Circuit.FoldlM.foldlAcc` of the `ScalarMul` fold body equals `accVar`.
Stated over a generic `i : Fin scalarBits` so it can rewrite under binders.

Uses `FlaggedPoint (Expression (F circomPrime))` for the accumulator type (not
the `Var FlaggedPoint (F circomPrime)` alias) so the pattern matches `h_holds`
syntactically — `simp`/`rw` can't see through the alias in binder types. -/
lemma foldlAcc_eq_accVar (i₀ : ℕ) (px py : Emu (Expression (F circomPrime)))
    (bits : Vector (Expression (F circomPrime)) Specs.Secp256k1.scalarBits)
    (i : Fin Specs.Secp256k1.scalarBits) :
    Circuit.FoldlM.foldlAcc (β := FlaggedPoint (Expression (F circomPrime))) i₀
      (Vector.finRange Specs.Secp256k1.scalarBits)
      (fun acc j => subcircuit Step.circuit { acc := acc, px := px, py := py, bit := bits[j.val] })
      infConst i = accVar i₀ i.val := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  simp only [circuit_norm]
  simp only [step_localLength, step_output]
  exact fin_foldl_eq_accVar i₀ i.val

/-- The fold term as it appears in the *goal* after `circuit_proof_start` +
numeral normalization (the elaborated output unfolds `varFromOffset` to
`Vector.mapRange`, with the step offset split as `15975 + 15975`), rewritten
to `accVar`. -/
lemma fin_foldl_goal_eq_accVar (i₀ : ℕ) :
    Fin.foldl Specs.Secp256k1.scalarBits
      (fun (_ : FlaggedPoint (Expression (F circomPrime)))
           (i : Fin Specs.Secp256k1.scalarBits) =>
        ({ x := Vector.mapRange numLimbs
             (fun j => var { index := i₀ + i.val * 31959 + 15975 + 15975 + j }),
           y := Vector.mapRange numLimbs
             (fun j => var { index := i₀ + i.val * 31959 + 15975 + 15975 + 4 + j }),
           isInf := var { index := i₀ + i.val * 31959 + 15975 + 15975 + 4 + 4 } } :
          FlaggedPoint (Expression (F circomPrime))))
      infConst = accVar i₀ Specs.Secp256k1.scalarBits := by
  rw [show (Specs.Secp256k1.scalarBits : ℕ) = 255 + 1 from rfl,
    fin_foldl_ignore_acc 255
      (fun v =>
        ({ x := Vector.mapRange numLimbs
                  (fun j => var { index := i₀ + v * 31959 + 15975 + 15975 + j }),
           y := Vector.mapRange numLimbs
                  (fun j => var { index := i₀ + v * 31959 + 15975 + 15975 + 4 + j }),
           isInf := var { index := i₀ + v * 31959 + 15975 + 15975 + 4 + 4 } } :
          FlaggedPoint (Expression (F circomPrime))))]
  show _ = varFromOffset FlaggedPoint (i₀ + 255 * 31959 + 31950)
  simp only [circuit_norm, explicit_provable_type, FlaggedPoint.mk.injEq]
  norm_num [numLimbs]

/-! ## The value-level spec accumulator -/

/-- The spec-level accumulator after `k` double-and-add steps, the value
mirror of `accVar` (cf. `valStateAfterRound` in `SHA256Rounds`). -/
def specAcc (bits : Vector ℕ Specs.Secp256k1.scalarBits)
    (P : Specs.ShortWeierstrass.Point Specs.Secp256k1.Fp) :
    ℕ → Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp
  | 0 => .infinity
  | k + 1 =>
    if h : k < Specs.Secp256k1.scalarBits then
      Specs.ShortWeierstrass.step Specs.Secp256k1.curve P (specAcc bits P k) (bits[k]'h)
    else specAcc bits P k

private lemma vector_foldl_eq_fin_foldl {α β : Type} {n : ℕ} (v : Vector α n)
    (f : β → α → β) (init : β) :
    v.foldl f init = Fin.foldl n (fun acc i => f acc v[i]) init := by
  have h1 : v.foldl f init = v.toList.foldl f init := by
    cases v; simp [Vector.foldl, Array.foldl_toList]
  have h2 : List.map (fun i : Fin n => v[i]) (List.finRange n) = v.toList := by
    apply List.ext_getElem <;> simp
  rw [h1, ← h2, List.foldl_map, Fin.foldl_eq_foldl_finRange]

/-- The trusted spec's `scalarMul` is `specAcc` at the full bit length. -/
lemma scalarMul_eq_specAcc (bits : Vector ℕ Specs.Secp256k1.scalarBits)
    (P : Specs.ShortWeierstrass.Point Specs.Secp256k1.Fp) :
    Specs.ShortWeierstrass.scalarMul Specs.Secp256k1.curve bits P =
      specAcc bits P Specs.Secp256k1.scalarBits := by
  rw [Specs.ShortWeierstrass.scalarMul, vector_foldl_eq_fin_foldl]
  suffices h : ∀ k (hk : k ≤ Specs.Secp256k1.scalarBits),
      Fin.foldl k (fun acc (i : Fin k) =>
        Specs.ShortWeierstrass.step Specs.Secp256k1.curve P acc
          (bits[i.val]'(by have := i.isLt; omega))) .infinity
        = specAcc bits P k by
    have := h Specs.Secp256k1.scalarBits (le_refl _)
    convert this using 1
  intro k hk
  induction k with
  | zero => simp [specAcc, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, specAcc,
      dif_pos (by omega : k < Specs.Secp256k1.scalarBits)]
    have hk' : k ≤ Specs.Secp256k1.scalarBits := by omega
    rw [show Fin.foldl k (fun acc (i : Fin k) =>
        Specs.ShortWeierstrass.step Specs.Secp256k1.curve P acc
          (bits[i.castSucc.val]'(by have := i.isLt; omega))) .infinity =
      Fin.foldl k (fun acc (i : Fin k) =>
        Specs.ShortWeierstrass.step Specs.Secp256k1.curve P acc
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
  exact ⟨Or.inr rfl, DivOrZero.fe_valid_emuOfNat DivOrZero.P256_pos,
    DivOrZero.fe_valid_emuOfNat DivOrZero.P256_pos,
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

/-- The big-endian reindexing in the goal (`var {index := M + (31 - i)}`) is
the pointwise big-endian view of the evaluated mux output block. -/
lemma map_eval_ofFn_rev (env : Environment (F circomPrime)) (M : ℕ) :
    Vector.map (Expression.eval env)
      (Vector.ofFn fun i : Fin coordBytes =>
        (var { index := M + (31 - i.val) } : Expression (F circomPrime))) =
    Vector.ofFn (fun i : Fin coordBytes =>
      (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) M))[31 - i.val]'(by
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
          w[31 - i.val]'(by simp only [coordBytes]; omega)).toList.map
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
    simp only [show (31 : ℕ) - (32 - 1 - j) = j from by omega]
    rfl

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
  simp [Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]

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
    (input_bits : Vector (F circomPrime) Specs.Secp256k1.scalarBits)
    (input_px input_py : Emu (F circomPrime))
    (input_var_bits : Vector (Expression (F circomPrime)) Specs.Secp256k1.scalarBits)
    (h_bits : Vector.map (Expression.eval env) input_var_bits = input_bits)
    (hbits_bool : ∀ i : Fin Specs.Secp256k1.scalarBits, IsBool input_bits[i])
    (hpx_valid : Fe.Valid input_px) (hpy_valid : Fe.Valid input_py)
    (honcurve : Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
      { x := decodeFe input_px, y := decodeFe input_py })
    (k : ℕ) (hk'' : k < Specs.Secp256k1.scalarBits)
    (ih_bool : IsBool (Expression.eval env (accVar i₀ k).isInf))
    (ih_fx : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ k).x))
    (ih_fy : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ k).y))
    (ih_curve : Expression.eval env (accVar i₀ k).isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
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
            (varFromOffset FlaggedPoint (i₀ + k * 31959 + 31950)).x,
          y := Vector.map (Expression.eval env)
            (varFromOffset FlaggedPoint (i₀ + k * 31959 + 31950)).y,
          isInf := Expression.eval env
            (varFromOffset FlaggedPoint (i₀ + k * 31959 + 31950)).isInf }) :
    IsBool (Expression.eval env (accVar i₀ (k + 1)).isInf) ∧
    Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ (k + 1)).x) ∧
    Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ (k + 1)).y) ∧
    (Expression.eval env (accVar i₀ (k + 1)).isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
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
    (input_bits : Vector (F circomPrime) Specs.Secp256k1.scalarBits)
    (input_px input_py : Emu (F circomPrime))
    (input_var_bits : Vector (Expression (F circomPrime)) Specs.Secp256k1.scalarBits)
    (h_bits : Vector.map (Expression.eval env) input_var_bits = input_bits)
    (hbits_bool : ∀ i : Fin Specs.Secp256k1.scalarBits, IsBool input_bits[i])
    (hpx_valid : Fe.Valid input_px) (hpy_valid : Fe.Valid input_py)
    (honcurve : Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
      { x := decodeFe input_px, y := decodeFe input_py })
    (h_steps : ∀ i : Fin Specs.Secp256k1.scalarBits,
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
            (varFromOffset FlaggedPoint (i₀ + i.val * 31959 + 31950)).x,
          y := Vector.map (Expression.eval env)
            (varFromOffset FlaggedPoint (i₀ + i.val * 31959 + 31950)).y,
          isInf := Expression.eval env
            (varFromOffset FlaggedPoint (i₀ + i.val * 31959 + 31950)).isInf }) :
    ∀ k (hk : k ≤ Specs.Secp256k1.scalarBits),
      IsBool (Expression.eval env (accVar i₀ k).isInf) ∧
      Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ k).x) ∧
      Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ k).y) ∧
      (Expression.eval env (accVar i₀ k).isInf = 0 →
        Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
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
    have hk' : k ≤ Specs.Secp256k1.scalarBits := by omega
    have hk'' : k < Specs.Secp256k1.scalarBits := by omega
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
    (hbool : IsBool (Expression.eval env (accVar i₀ 256).isInf))
    (hfx : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ 256).x))
    (hfy : Fe.Valid (Vector.map (Expression.eval env) (accVar i₀ 256).y))
    (hxb_bytes : ∀ i : Fin coordBytes,
      ZMod.val (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504)))[i] < 256)
    (hxb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 8181504))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 256).x))
    (hyb_bytes : ∀ i : Fin coordBytes,
      ZMod.val (Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288)))[i] < 256)
    (hyb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 256).y))
    (hmx : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288 + 288)) =
      if Expression.eval env (accVar i₀ 256).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504)))
    (hmy : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288 + 288 + 32)) =
      if Expression.eval env (accVar i₀ 256).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288))) :
    Outputs.Valid
      { x := Vector.map (Expression.eval env)
          (Vector.ofFn fun i =>
            (var { index := i₀ + 8181504 + 288 + 288 + (31 - i.val) } :
              Expression (F circomPrime))),
        y := Vector.map (Expression.eval env)
          (Vector.ofFn fun i =>
            (var { index := i₀ + 8181504 + 288 + 288 + 32 + (31 - i.val) } :
              Expression (F circomPrime))),
        isInf := Expression.eval env (accVar i₀ 256).isInf } := by
  rw [map_eval_ofFn_rev env (i₀ + 8181504 + 288 + 288),
    map_eval_ofFn_rev env (i₀ + 8181504 + 288 + 288 + 32), hmx, hmy]
  simp only [Outputs.Valid]
  rcases hbool with hinf0 | hinf1
  · rw [hinf0, if_neg (zero_ne_one (α := F circomPrime)),
      if_neg (zero_ne_one (α := F circomPrime))]
    refine ⟨?_, ?_, Or.inl rfl, ?_, ?_,
      fun h => absurd h (zero_ne_one (α := F circomPrime))⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact hxb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact hyb_bytes ⟨31 - i.val, by simp only [coordBytes]; omega⟩
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
      exact DivOrZero.P256_pos
    · simp only [coordVal, fromLimbs_rev_ofFn, fromLimbs_eval_zeroBytes env zb hzb]
      exact DivOrZero.P256_pos
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]
    · intro i
      rw [Fin.getElem_fin, Vector.getElem_ofFn, eval_zeroBytes_getElem env zb hzb]

set_option maxRecDepth 8192 in
/-- The decoded output at the boundary satisfies the trusted total spec. -/
lemma output_spec
    (input_bits : Vector (F circomPrime) Specs.Secp256k1.scalarBits)
    (input_px input_py : Emu (F circomPrime))
    (zb : Var (fields coordBytes) (F circomPrime))
    (hbool : IsBool (Expression.eval env (accVar i₀ 256).isInf))
    (hdec256 : decodePoint
        { x := Vector.map (Expression.eval env) (accVar i₀ 256).x,
          y := Vector.map (Expression.eval env) (accVar i₀ 256).y,
          isInf := Expression.eval env (accVar i₀ 256).isInf } =
      specAcc (Vector.map ZMod.val input_bits)
        { x := decodeFe input_px, y := decodeFe input_py } 256)
    (hxb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 8181504))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 256).x))
    (hyb_val : Limbs.fromLimbs 8
        (List.map ZMod.val (Vector.map (Expression.eval env)
          (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288))).toList) =
      BigInt.value limbBits (Vector.map (Expression.eval env) (accVar i₀ 256).y))
    (hmx : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288 + 288)) =
      if Expression.eval env (accVar i₀ 256).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504)))
    (hmy : Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288 + 288 + 32)) =
      if Expression.eval env (accVar i₀ 256).isInf = 1
      then Vector.map (Expression.eval env) zb
      else Vector.map (Expression.eval env)
        (varFromOffset (fields coordBytes) (i₀ + 8181504 + 288))) :
    Specs.Secp256k1ScalarMul.Spec (Vector.map ZMod.val input_bits)
      { x := decodeFe input_px, y := decodeFe input_py }
      (decodeOutput
        { x := Vector.map (Expression.eval env)
            (Vector.ofFn fun i =>
              (var { index := i₀ + 8181504 + 288 + 288 + (31 - i.val) } :
                Expression (F circomPrime))),
          y := Vector.map (Expression.eval env)
            (Vector.ofFn fun i =>
              (var { index := i₀ + 8181504 + 288 + 288 + 32 + (31 - i.val) } :
                Expression (F circomPrime))),
          isInf := Expression.eval env (accVar i₀ 256).isInf }) := by
  rw [map_eval_ofFn_rev env (i₀ + 8181504 + 288 + 288),
    map_eval_ofFn_rev env (i₀ + 8181504 + 288 + 288 + 32)]
  unfold Specs.Secp256k1ScalarMul.Spec Specs.ShortWeierstrass.Spec
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
          Specs.Secp256k1.scalarBits =
        specAcc (Vector.map ZMod.val input_bits)
          { x := decodeFe input_px, y := decodeFe input_py } 256 from rfl,
      ← hdec256]
    simp only [coordVal, fromLimbs_rev_ofFn, hxb_val, hyb_val, decodeFe]
  · rw [hinf1] at hdec256 ⊢
    rw [if_pos rfl] at hdec256
    rw [if_pos rfl]
    rw [show specAcc (Vector.map ZMod.val input_bits)
          { x := decodeFe input_px, y := decodeFe input_py }
          Specs.Secp256k1.scalarBits =
        specAcc (Vector.map ZMod.val input_bits)
          { x := decodeFe input_px, y := decodeFe input_py } 256 from rfl]
    exact hdec256.symm

end OutputBoundary

end ScalarMul
end Solution.Secp256k1ScalarMulFixedBase
