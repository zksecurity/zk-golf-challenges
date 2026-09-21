import Solution.Secp256k1ScalarMul.MulMod
import Solution.Secp256k1ScalarMul.WitgenLimbs
import Challenge.Specs.Secp256k1
import Challenge.Instances.Secp256k1ScalarMul.Interface

/-!
# secp256k1 scalar multiplication — parameters, types, and decoding

Shared definitions for the secp256k1 variable-base scalar-multiplication
reference circuit: the emulated-field limb parameters, the constant limbs of
the secp256k1 prime, the flagged point type, and the decoding functions that
bridge circuit values to the trusted spec (`Challenge.Specs.Secp256k1`).

The secp256k1 base field (256-bit prime `p`) is emulated over the circuit
field (the ~254-bit circom/bn254 scalar prime) as `numLimbs = 4` little-endian
limbs of `limbBits = 64` bits — byte-aligned, so the byte-encoded output
boundary is a per-limb affine recomposition — reusing the big-integer gadget
family adapted
from the RSA solution (`Normalize`, `LessThan`, `Equal`, `EqViaCarries`,
`MulMod`).
-/

namespace Solution.Secp256k1ScalarMul

/-- The circuit field: the bn254/circom scalar prime, owned (with its
primality axiom) by the instance Interface. Reducible alias so every gadget
file can keep referring to it unqualified. -/
@[reducible] def circomPrime : ℕ :=
  Challenge.Instances.Secp256k1ScalarMul.Interface.circomPrime

instance : Fact (circomPrime > 2) := ⟨by decide⟩

/-- The emulated secp256k1 base-field prime (`2^256 - 2^32 - 977`). -/
@[reducible] def P256 : ℕ := Specs.Secp256k1.p

/-- Number of limbs of an emulated secp256k1 base-field element. -/
@[reducible] def numLimbs : ℕ := 4

/-- Limb bit-width (byte-aligned: one limb is exactly `bytesPerLimb` bytes). -/
@[reducible] def limbBits : ℕ := 64

/-- Bytes per limb (`limbBits / 8`). -/
@[reducible] def bytesPerLimb : ℕ := 8

/-- Number of bytes of a coordinate (`numLimbs * bytesPerLimb`). -/
@[reducible] def coordBytes : ℕ := 32

/-- An emulated secp256k1 base-field element: 4 little-endian 64-bit limbs
(covering exactly 256 bits; canonical values are `< P256 < 2^256`). -/
@[reducible] def Emu : TypeMap := BigInt numLimbs

/-- Big-integer parameters for 256-bit values over the circom prime: 4 limbs
of 64 bits, 69-bit carries. The largest field-size hypothesis (`hWp`) is
`≈ 2^133.1 < 2^253.6`. -/
def secpParams : BigIntParams circomPrime numLimbs where
  B := limbBits
  W := 69
  hB := by decide
  hW := by decide
  hB1 := by decide
  hWB := by decide
  hWp := by decide
  hp := by decide

/-! ## Constants as limbs -/

/-- Limb `k` of a natural number, little-endian base `2^limbBits`. -/
def limbOfNat (v k : ℕ) : ℕ := v / 2 ^ (limbBits * k) % 2 ^ limbBits

/-- A natural number `< 2^256` as a value-level `Emu`. -/
def emuOfNat (v : ℕ) : Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs => ((limbOfNat v k.val : ℕ) : F circomPrime)

/-- A natural number `< 2^256` as constant limb expressions. -/
def emuConst (v : ℕ) : Var Emu (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (((limbOfNat v k.val : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- The secp256k1 prime as constant limb expressions (the `modulus` argument
of every `MulMod`/`EqViaCarries` call). -/
def pConst : Var Emu (F circomPrime) := emuConst P256

/-- Constant `0` as limb expressions. -/
def zeroConst : Var Emu (F circomPrime) := emuConst 0

/-- Constant `1` as limb expressions. -/
def oneConst : Var Emu (F circomPrime) := emuConst 1

/-! ## Witness-side evaluation helpers -/

/-- Natural-number value of an `Emu` variable under a prover environment.
Used only inside witness generators. -/
def evalEmu (env : ProverEnvironment (F circomPrime))
    (x : Var Emu (F circomPrime)) : ℕ :=
  Limbs.fromLimbs limbBits
    ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

theorem evalEmu_eq_of_eval_eq {env env' : ProverEnvironment (F circomPrime)}
    {x : Var Emu (F circomPrime)}
    (h : eval env x = eval env' x) :
    evalEmu env x = evalEmu env' x := by
  have hmap :
      x.map (Expression.eval env.toEnvironment) =
        x.map (Expression.eval env'.toEnvironment) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    have h_i : (eval env x)[i] = (eval env' x)[i] := by
      simpa only using congrArg (fun y : Emu (F circomPrime) => y[i]) h
    rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
      ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at h_i
    exact h_i
  simp [evalEmu, hmap]

theorem emu_map_eval_eq_of_eval_eq {env env' : ProverEnvironment (F circomPrime)}
    {x : Var Emu (F circomPrime)}
    (h : eval env x = eval env' x) :
    x.map (Expression.eval env.toEnvironment) =
      x.map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  have h_i : (eval env x)[i] = (eval env' x)[i] := by
    simpa only using congrArg (fun y : Emu (F circomPrime) => y[i]) h
  rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
    ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at h_i
  exact h_i

theorem eval_mem_of_map_eval_eq {m : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    {x : Vector (Expression (F circomPrime)) m}
    (h : x.map (Expression.eval env.toEnvironment) =
      x.map (Expression.eval env'.toEnvironment)) :
    ∀ a ∈ x, Expression.eval env.toEnvironment a = Expression.eval env'.toEnvironment a := by
  intro a ha
  simp only [Vector.mem_iff_getElem] at ha
  rcases ha with ⟨i, hi, rfl⟩
  simpa only [Vector.getElem_map] using congrArg (fun y : Vector (F circomPrime) m => y[i]) h

/-! ## The digit layer for emulated field elements

Every emulated-arithmetic gadget (`AddMod`, `SubMod`, `AddModL`, `SubModL`, `MulModL`,
`DivOrZero`, `ToBytes`) works with the same two shapes: the base-`2^limbBits` **value**
of a limb vector, which is the argument of the ℕ-level formula the gadget computes, and
the limb **decomposition** of that formula's result. `emuDigits` and `emuOutF` are those
two, on the u64 digit library.

Reading an element in costs nothing: its four limbs are disjoint 64-bit windows of the
value, so a digit of the value is a bit-sum of single-limb bit reads and no carry
crosses a digit. Writing one out costs nothing either: limb `j` is the 64-bit window
`[64j, 64j+64)` of the digit list, assembled in the field. The bridges land on
`evalEmu` / `emuOfNat`, the vocabulary the existing functional proofs are stated in.

Subtraction needs no trick any more. The u64 sort has no subtraction, but the digit
layer's borrow chain (`WitgenBigNat.subP`) does, with one reduction modulo the register
width absorbing the borrow out (`WitgenNat.lval_subb_mod`); the old digit-wise ones'
complement, which existed only because a 256-bit value cannot be routed through the
field, is gone.
-/

namespace IREmu

open Witgen WitgenNat WitgenBigNat IRLimbs

/-- Digits of an emulated element: `limbBits · numLimbs = 256` bits. -/
@[reducible] def emuLen : ℕ := numChunks (limbBits * numLimbs)

/-- The width the limb decomposition covers: `2^(limbBits·numLimbs) = 2^256`. -/
@[reducible] def emuSpan : ℕ := 2 ^ (limbBits * numLimbs)

theorem emuSpan_le : emuSpan ≤ base ^ emuLen := two_pow_le_base_numChunks _

/-- The digits of an emulated element's value. Pure expressions: no steps. -/
def emuDigits (x : Var Emu (F circomPrime)) : List (U64Expr (F circomPrime)) :=
  digitsOf limbBits x emuLen

theorem evalsBig_emuDigits {S : Array (Step (F circomPrime))} (x : Var Emu (F circomPrime)) :
    EvalsBig S (emuDigits x) (fun env => ofNat (bigVal limbBits x env) emuLen) :=
  evalsBig_digitsOf (by decide) x emuLen

/-- On a normalized element the digit reader's value is `evalEmu`. -/
theorem bigVal_eq_evalEmu (x : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (h : BigInt.Normalized limbBits (x.map (Expression.eval env.toEnvironment))) :
    bigVal limbBits x env = evalEmu env x :=
  bigVal_eq_value limbBits x env h

/-- An emulated element's value fits the digit register. -/
theorem bigVal_lt_span (x : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : bigVal limbBits x env < emuSpan :=
  bigVal_lt x env

theorem lval_ofNat_emu {v : ℕ} (h : v < emuSpan) : lval (ofNat v emuLen) = v :=
  lval_ofNat_of_lt (lt_of_lt_of_le h emuSpan_le)

/-- `emuDigits` reads the element only through its evaluated limbs. -/
theorem bigVal_emu_congr (x : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (h : ∀ (j : ℕ) (hj : j < numLimbs),
      Expression.eval env.toEnvironment (x[j]'hj)
        = Expression.eval env'.toEnvironment (x[j]'hj)) :
    bigVal limbBits x env = bigVal limbBits x env' :=
  bigVal_congr limbBits x h

/-- `emuDigits` reads the element only through its evaluated limbs, in the `eval`
form the `computableWitnesses` hypotheses come in. -/
theorem bigVal_stable (x : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)} (h : eval env x = eval env' x) :
    bigVal limbBits x env = bigVal limbBits x env' := by
  refine bigVal_congr limbBits x fun j hj => ?_
  have hm := emu_map_eval_eq_of_eval_eq h
  have := congrArg (fun v : Emu (F circomPrime) => v[j]'hj) hm
  simpa only [Vector.getElem_map] using this

/-- The `numLimbs` limbs of a digit list, as a witness program's output vector. -/
def emuOutF (ds : List (U64Expr (F circomPrime))) : VExpr (F circomPrime) numLimbs :=
  limbsOut ds limbBits numLimbs

/-- Bridge for `emuOutF`: the witnessed vector is `emuOfNat` of the value the digits
denote, exactly as the old `emuIR` bridge read. -/
theorem evalsV_emuOutF {S : Array (Step (F circomPrime))}
    {ds : List (U64Expr (F circomPrime))} {dv}
    (h : EvalsBig S ds dv) :
    EvalsV S (emuOutF ds) (fun env => emuOfNat (lval (dv env))) :=
  evalsV_limbsOut h limbBits numLimbs

/-! ### Modular addition and subtraction, in the digit layer

All four emulated add/subtract gadgets reduce to the same two moves: build a
`workLen`-digit register holding `a + b` or `a + C − b` for a constant shift `C`, then
conditionally subtract the modulus once (`AddMod`, `SubMod`) or twice (`SubModL`,
whose operands are only normalized, so the difference can need two reductions).

`reduceStep` is that conditional subtraction: it subtracts `P256` and keeps the
difference unless the subtraction borrowed, in which case it keeps the original. Its
borrow *is* the comparison, so the gadgets' quotient/borrow witness comes out of the
same chain and needs no separate computation.

Every value below (`addN`, `shiftN`, `redN`, `redB`) is the register's own arithmetic
with its truncations, hence a total function of the operands' `bigVal`s: the
`computableWitnesses` bridges need no side condition, and the gadget's `Assumptions`
enter only in the readings (`addN_eq`, `shiftN_eq`, `redN_eq`, `redB_eq`).
-/

/-- Value of one reduction stage. -/
def redN (L X : ℕ) : ℕ :=
  if P256 % base ^ L ≤ X % base ^ L then X % base ^ L - P256 % base ^ L else X % base ^ L

/-- Borrow of one reduction stage: `1` exactly when no reduction happened. -/
def redB (L X : ℕ) : ℕ := if P256 % base ^ L ≤ X % base ^ L then 0 else 1

/-- One conditional reduction by the modulus: subtract `P256` when that keeps the
register non-negative, and report the borrow (`1` exactly when it did not). -/
def reduceStep (L : ℕ) (x : List (U64Expr (F circomPrime))) :
    M (F circomPrime) (List (U64Expr (F circomPrime)) × U64Expr (F circomPrime)) := do
  let d ← subP x (constDigits P256 L) (uc 0)
  let r ← selectP d.2 x d.1
  Pure.pure (r, d.2)

theorem computes_reduceStep {S : Array (Step (F circomPrime))} {L : ℕ}
    {x : List (U64Expr (F circomPrime))} {X : ProverEnvironment (F circomPrime) → ℕ}
    (hx : EvalsBig S x (fun env => ofNat (X env) L)) :
    Computes EvalsBigU S (reduceStep L x)
      (fun env => (ofNat (redN L (X env)) L, redB L (X env))) := by
  refine Computes.bind (computesBigU_subP _ _ (uc 0) hx (evalsBig_constDigits P256 L)
    (EvalsU.uc 0 (by norm_num)) (fun _ => by norm_num)) ?_
  intro S1 d hS1 hd
  have hd1 : EvalsBig S1 d.1
      (fun env => subb (ofNat (X env) L) (ofNat P256 L) 0) := hd.1
  have hd2 : EvalsU S1 d.2
      (fun env => subbOut (ofNat (X env) L) (ofNat P256 L) 0) := hd.2
  have hlen : x.length = d.1.length := by
    refine EvalsBig.length_expr (hx.mono hS1) hd1 fun env => ?_
    rw [length_ofNat, length_subb, length_ofNat]
  refine Computes.bind (computesBig_selectP x d.2 d.1 (hx.mono hS1) hd1 hd2 hlen) ?_
  intro S2 r hS2 hr
  refine Computes.pure ⟨hr.congr fun env => ?_, hd2.mono hS2 |>.congr fun env => ?_⟩
  · have hbd : Bounded (if subbOut (ofNat (X env) L) (ofNat P256 L) 0 = 0
        then subb (ofNat (X env) L) (ofNat P256 L) 0 else ofNat (X env) L) := by
      split
      · exact bounded_subb _ _ _ (bounded_ofNat _ _) (bounded_ofNat _ _) (by norm_num)
      · exact bounded_ofNat _ _
    refine eq_ofNat_of hbd ?_ ?_
    · rw [redN]
      by_cases hle : P256 % base ^ L ≤ X env % base ^ L
      · rw [if_pos (by
          rw [(subbOut_eq_zero_iff (bounded_ofNat _ _) (bounded_ofNat _ _)
            (by rw [length_ofNat, length_ofNat])).mpr (by rw [lval_ofNat, lval_ofNat]; exact hle)]),
          lval_subb_of_le (bounded_ofNat _ _) (bounded_ofNat _ _)
            (by rw [length_ofNat, length_ofNat])
            (by rw [lval_ofNat, lval_ofNat]; exact hle),
          lval_ofNat, lval_ofNat, if_pos hle]
      · rw [if_neg (by
          intro hz
          exact hle (by
            have := (subbOut_eq_zero_iff (bounded_ofNat (X env) L) (bounded_ofNat P256 L)
              (by rw [length_ofNat, length_ofNat])).mp hz
            rwa [lval_ofNat, lval_ofNat] at this)),
          lval_ofNat, if_neg hle]
    · split
      · rw [length_subb, length_ofNat]
      · rw [length_ofNat]
  · simp only [redB]
    by_cases hle : P256 % base ^ L ≤ X env % base ^ L
    · rw [if_pos hle]
      exact (subbOut_eq_zero_iff (bounded_ofNat _ _) (bounded_ofNat _ _)
        (by rw [length_ofNat, length_ofNat])).mpr (by rw [lval_ofNat, lval_ofNat]; exact hle)
    · rw [if_neg hle]
      have hb := subbOut_lt (ofNat (X env) L) (ofNat P256 L) 0 (by norm_num)
      rcases (show subbOut (ofNat (X env) L) (ofNat P256 L) 0 = 0
          ∨ subbOut (ofNat (X env) L) (ofNat P256 L) 0 = 1 by omega) with h | h
      · exfalso
        exact hle (by
          have := (subbOut_eq_zero_iff (bounded_ofNat (X env) L) (bounded_ofNat P256 L)
            (by rw [length_ofNat, length_ofNat])).mp h
          rwa [lval_ofNat, lval_ofNat] at this)
      · exact h

theorem redN_lt (L X : ℕ) : redN L X < base ^ L := by
  have h : X % base ^ L < base ^ L := Nat.mod_lt _ (Nat.pow_pos base_pos)
  rw [redN]
  split
  · exact lt_of_le_of_lt (Nat.sub_le _ _) h
  · exact h

theorem redB_lt_two (L X : ℕ) : redB L X < 2 := by rw [redB]; split <;> omega

/-- Digits of the working register: `2·P256` plus a 256-bit value still fits. -/
@[reducible] def workLen : ℕ := emuLen + 1

theorem span_lt_work : emuSpan < base ^ workLen := by decide

theorem modulus_lt_work : P256 < base ^ workLen := by decide

/-! ### The sum register -/

/-- `a + b` in a `workLen`-digit register. -/
def addSum (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (List (U64Expr (F circomPrime))) := do
  let s ← addP (emuDigits a) (emuDigits b) (uc 0)
  Pure.pure (resizeDigits s workLen)

/-- Value of `addSum`. -/
def addN (va vb : ℕ) : ℕ := va % base ^ emuLen + vb % base ^ emuLen

theorem computesBig_addSum {S : Array (Step (F circomPrime))} (a b : Var Emu (F circomPrime)) :
    ComputesBig S (addSum a b)
      (fun env => ofNat (addN (bigVal limbBits a env) (bigVal limbBits b env)) workLen) := by
  refine Computes.bind (computesBig_addP _ _ (uc 0) (evalsBig_emuDigits a) (evalsBig_emuDigits b)
    (EvalsU.uc 0 (by norm_num)) (fun _ => base_pos)) ?_
  intro S1 s hS1 hs
  exact Computes.pure ((evalsBig_resizeDigits hs workLen).congr fun env => by
    rw [lval_addc, lval_ofNat, lval_ofNat, Nat.add_zero, addN])

/-! ### The shifted-difference register -/

/-- `a + C − b` in a `workLen`-digit register, for a constant shift `C` large enough that
the subtraction never borrows. -/
def shiftSub (C : ℕ) (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (List (U64Expr (F circomPrime))) := do
  let e ← addP (emuDigits a) (constDigits C workLen) (uc 0)
  let f ← subP (resizeDigits e workLen) (emuDigits b) (uc 0)
  Pure.pure (resizeDigits f.1 workLen)

/-- Value of `shiftSub`. -/
def shiftN (C va vb : ℕ) : ℕ :=
  ((va % base ^ emuLen + C % base ^ workLen) % base ^ workLen + base ^ workLen
    - vb % base ^ emuLen) % base ^ workLen

theorem computesBig_shiftSub {S : Array (Step (F circomPrime))} (C : ℕ)
    (a b : Var Emu (F circomPrime)) :
    ComputesBig S (shiftSub C a b)
      (fun env => ofNat (shiftN C (bigVal limbBits a env) (bigVal limbBits b env)) workLen) := by
  refine Computes.bind (computesBig_addP _ _ (uc 0) (evalsBig_emuDigits a)
    (evalsBig_constDigits C workLen) (EvalsU.uc 0 (by norm_num)) (fun _ => base_pos)) ?_
  intro S1 e hS1 he
  have he' : EvalsBig S1 (resizeDigits e workLen)
      (fun env => ofNat ((bigVal limbBits a env % base ^ emuLen + C % base ^ workLen)
        % base ^ workLen) workLen) :=
    (evalsBig_resizeDigits he workLen).congr fun env => by
      rw [lval_addc, lval_ofNat, lval_ofNat, Nat.add_zero, ofNat_mod]
  refine Computes.bind (computesBigU_subP _ _ (uc 0) he'
    ((evalsBig_emuDigits b).mono hS1) (EvalsU.uc 0 (by norm_num)) (fun _ => by norm_num)) ?_
  intro S2 f hS2 hf
  have hf1 : EvalsBig S2 f.1 (fun env => subb
      (ofNat ((bigVal limbBits a env % base ^ emuLen + C % base ^ workLen) % base ^ workLen)
        workLen)
      (ofNat (bigVal limbBits b env) emuLen) 0) := hf.1
  exact Computes.pure ((evalsBig_resizeDigits hf1 workLen).congr fun env => by
    rw [lval_subb_mod (bounded_ofNat _ _) (bounded_ofNat _ _) (by simp), length_ofNat,
      lval_ofNat_of_lt (Nat.mod_lt _ (Nat.pow_pos base_pos)), lval_ofNat, shiftN])


/-! ### Reading the registers back

Each reading is `X % P` and `X / P` on a value the gadget's `Assumptions` keep below
`2·P256`, which is a case split rather than a division.
-/

private theorem mod_div_two_mul {P X : ℕ} (hP : 0 < P) (h : X < 2 * P) :
    X % P = (if P ≤ X then X - P else X) ∧ X / P = (if P ≤ X then 1 else 0) := by
  by_cases hle : P ≤ X
  · rw [if_pos hle, if_pos hle, Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_sub_div hP hle, Nat.div_eq_of_lt (by omega)]
    exact ⟨rfl, rfl⟩
  · rw [if_neg hle, if_neg hle, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    exact ⟨rfl, rfl⟩

theorem two_mul_modulus_lt_work : 2 * P256 < base ^ workLen := by decide

theorem redN_eq {X : ℕ} (h : X < 2 * P256) : redN workLen X = X % P256 := by
  have hw := two_mul_modulus_lt_work
  have hX : X < base ^ workLen := by omega
  rw [redN, Nat.mod_eq_of_lt modulus_lt_work, Nat.mod_eq_of_lt hX,
    (mod_div_two_mul (by decide : 0 < P256) h).1]

theorem redB_eq {X : ℕ} (h : X < 2 * P256) :
    (if redB workLen X = 0 then 1 else 0) = X / P256 := by
  have hw := two_mul_modulus_lt_work
  have hX : X < base ^ workLen := by omega
  rw [redB, Nat.mod_eq_of_lt modulus_lt_work, Nat.mod_eq_of_lt hX,
    (mod_div_two_mul (by decide : 0 < P256) h).2]
  split <;> simp

theorem addN_eq {va vb : ℕ} (hva : va < emuSpan) (hvb : vb < emuSpan) :
    addN va vb = va + vb := by
  have h := emuSpan_le
  rw [addN, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem shiftN_eq {C va vb : ℕ} (hva : va < emuSpan) (hvb : vb < emuSpan)
    (hC : va + C < base ^ workLen) (hle : vb ≤ va + C) : shiftN C va vb = va + C - vb := by
  have h := emuSpan_le
  rw [shiftN, Nat.mod_eq_of_lt (show va < base ^ emuLen by omega),
    Nat.mod_eq_of_lt (show vb < base ^ emuLen by omega),
    Nat.mod_eq_of_lt (show C < base ^ workLen by omega), Nat.mod_eq_of_lt hC,
    show va + C + base ^ workLen - vb = base ^ workLen + (va + C - vb) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem three_mul_modulus_lt_work : 3 * P256 < base ^ workLen := by decide

theorem redN_unfold {X : ℕ} (h : X < base ^ workLen) :
    redN workLen X = if P256 ≤ X then X - P256 else X := by
  rw [redN, Nat.mod_eq_of_lt modulus_lt_work, Nat.mod_eq_of_lt h]

theorem redB_unfold {X : ℕ} (h : X < base ^ workLen) :
    redB workLen X = if P256 ≤ X then 0 else 1 := by
  rw [redB, Nat.mod_eq_of_lt modulus_lt_work, Nat.mod_eq_of_lt h]

private theorem mod_div_three_mul {P X : ℕ} (hP : 0 < P) (h : X < 3 * P) :
    X % P = (if P ≤ X then (if P ≤ X - P then X - P - P else X - P) else X)
      ∧ X / P = (if P ≤ X then (if P ≤ X - P then 2 else 1) else 0) := by
  by_cases h1 : P ≤ X
  · by_cases h2 : P ≤ X - P
    · rw [if_pos h1, if_pos h1, if_pos h2, if_pos h2, Nat.mod_eq_sub_mod h1,
        Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega),
        Nat.div_eq_sub_div hP h1, Nat.div_eq_sub_div hP h2, Nat.div_eq_of_lt (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [if_pos h1, if_pos h1, if_neg h2, if_neg h2, Nat.mod_eq_sub_mod h1,
        Nat.mod_eq_of_lt (by omega), Nat.div_eq_sub_div hP h1, Nat.div_eq_of_lt (by omega)]
      exact ⟨rfl, rfl⟩
  · rw [if_neg h1, if_neg h1, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    exact ⟨rfl, rfl⟩

theorem redN2_eq {X : ℕ} (h : X < 3 * P256) :
    redN workLen (redN workLen X) = X % P256 := by
  have hw := three_mul_modulus_lt_work
  have hm := (mod_div_three_mul (by decide : 0 < P256) h).1
  have hX : X < base ^ workLen := by omega
  by_cases h1 : P256 ≤ X
  · have hX1 : X - P256 < base ^ workLen := by omega
    rw [redN_unfold hX, if_pos h1, redN_unfold hX1, hm, if_pos h1]
  · rw [redN_unfold hX, if_neg h1, redN_unfold hX, if_neg h1, hm, if_neg h1]

theorem redB2_eq {X : ℕ} (h : X < 3 * P256) :
    2 - (redB workLen X + redB workLen (redN workLen X)) = X / P256 := by
  have hw := three_mul_modulus_lt_work
  have hm := (mod_div_three_mul (by decide : 0 < P256) h).2
  have hX : X < base ^ workLen := by omega
  by_cases h1 : P256 ≤ X
  · have hX1 : X - P256 < base ^ workLen := by omega
    rw [redN_unfold hX, if_pos h1, redB_unfold hX, if_pos h1, redB_unfold hX1, hm, if_pos h1]
    by_cases h2 : P256 ≤ X - P256
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
  · rw [redN_unfold hX, if_neg h1, redB_unfold hX, if_neg h1, hm, if_neg h1]

/-! ### The four witness programs of the emulated add and subtract gadgets -/

/-- `r = (a + b) % P256`. -/
def addRProg (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (VExpr (F circomPrime) numLimbs) := do
  let s ← addSum a b
  let rd ← reduceStep workLen s
  Pure.pure (emuOutF rd.1)

/-- `q = (a + b) / P256`, the quotient bit. -/
def addQProg (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (FExpr (F circomPrime)) := do
  let s ← addSum a b
  let rd ← reduceStep workLen s
  Pure.pure (.ofU64 (.ite (.neq rd.2 (uc 0)) (uc 1) (uc 0)))

/-- `r = (a + b) % P256` for merely *normalized* operands, where the sum can exceed
`2·P256` and so needs two reduction stages. -/
def addLRProg (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (VExpr (F circomPrime) numLimbs) := do
  let s ← addSum a b
  let rd1 ← reduceStep workLen s
  let rd0 ← reduceStep workLen rd1.1
  Pure.pure (emuOutF rd0.1)

/-- `q = (a + b) / P256 ∈ {0,1,2}`: one per stage that *did* reduce. -/
def addLQProg (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (FExpr (F circomPrime)) := do
  let s ← addSum a b
  let rd1 ← reduceStep workLen s
  let rd0 ← reduceStep workLen rd1.1
  Pure.pure (.ofU64 (usub (uc 2) (.add rd1.2 rd0.2)))

/-- `r = a + q·P256 − b` with `q` the single borrow: the canonical-operand difference. -/
def subRProg (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (VExpr (F circomPrime) numLimbs) := do
  let s ← shiftSub P256 a b
  let rd ← reduceStep workLen s
  Pure.pure (emuOutF rd.1)

/-- The borrow digit `q = [a < b]`. -/
def subQProg (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (FExpr (F circomPrime)) := do
  let s ← shiftSub P256 a b
  let rd ← reduceStep workLen s
  Pure.pure (.ofU64 rd.2)

/-- `r = a + q·P256 − b` with two reduction stages: the normalized-operand difference,
where `q` may be `0`, `1` or `2`. -/
def subLRProg (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (VExpr (F circomPrime) numLimbs) := do
  let s ← shiftSub (2 * P256) a b
  let rd1 ← reduceStep workLen s
  let rd0 ← reduceStep workLen rd1.1
  Pure.pure (emuOutF rd0.1)

/-- The borrow digit `q = b₁ + b₀`: one per stage that did *not* reduce, since the
register starts at `a + 2·P256 − b` and each reduction removes one `P256`. -/
def subLQProg (a b : Var Emu (F circomPrime)) :
    M (F circomPrime) (FExpr (F circomPrime)) := do
  let s ← shiftSub (2 * P256) a b
  let rd1 ← reduceStep workLen s
  let rd0 ← reduceStep workLen rd1.1
  Pure.pure (.ofU64 (.add rd1.2 rd0.2))


/-! ### What the six programs compute -/

theorem computesV_addRProg (a b : Var Emu (F circomPrime)) :
    ComputesV #[] (addRProg a b)
      (fun env => emuOfNat
        (redN workLen (addN (bigVal limbBits a env) (bigVal limbBits b env)))) := by
  refine Computes.bind (computesBig_addSum a b) ?_
  intro S1 s hS1 hs
  refine Computes.bind (computes_reduceStep hs) ?_
  intro S2 rd hS2 hrd
  have h1 : EvalsBig S2 rd.1 (fun env =>
      ofNat (redN workLen (addN (bigVal limbBits a env) (bigVal limbBits b env))) workLen) := hrd.1
  exact Computes.pure ((evalsV_emuOutF h1).congr fun env => by
    rw [lval_ofNat_of_lt (redN_lt _ _)])

theorem computesF_addQProg (a b : Var Emu (F circomPrime)) :
    ComputesF #[] (addQProg a b)
      (fun env => FiniteField.fromNat
        (if redB workLen (addN (bigVal limbBits a env) (bigVal limbBits b env)) = 0
          then 1 else 0)) := by
  refine Computes.bind (computesBig_addSum a b) ?_
  intro S1 s hS1 hs
  refine Computes.bind (computes_reduceStep hs) ?_
  intro S2 rd hS2 hrd
  have h2 : EvalsU S2 rd.2 (fun env =>
      redB workLen (addN (bigVal limbBits a env) (bigVal limbBits b env))) := hrd.2
  exact Computes.pure (EvalsF.ofU64 (EvalsU.iteEq h2 (EvalsU.uc 0 (by norm_num))
    (EvalsU.uc 1 (by norm_num)) (EvalsU.uc 0 (by norm_num))))

theorem computesV_addLRProg (a b : Var Emu (F circomPrime)) :
    ComputesV #[] (addLRProg a b)
      (fun env => emuOfNat (redN workLen (redN workLen
        (addN (bigVal limbBits a env) (bigVal limbBits b env))))) := by
  refine Computes.bind (computesBig_addSum a b) ?_
  intro S1 s hS1 hs
  refine Computes.bind (computes_reduceStep hs) ?_
  intro S2 rd1 hS2 hrd1
  have h1 : EvalsBig S2 rd1.1 (fun env =>
      ofNat (redN workLen (addN (bigVal limbBits a env) (bigVal limbBits b env)))
        workLen) := hrd1.1
  refine Computes.bind (computes_reduceStep h1) ?_
  intro S3 rd0 hS3 hrd0
  have h0 : EvalsBig S3 rd0.1 (fun env =>
      ofNat (redN workLen (redN workLen
        (addN (bigVal limbBits a env) (bigVal limbBits b env)))) workLen) := hrd0.1
  exact Computes.pure ((evalsV_emuOutF h0).congr fun env => by
    rw [lval_ofNat_of_lt (redN_lt _ _)])

theorem computesF_addLQProg (a b : Var Emu (F circomPrime)) :
    ComputesF #[] (addLQProg a b)
      (fun env => FiniteField.fromNat
        (2 - (redB workLen (addN (bigVal limbBits a env) (bigVal limbBits b env))
          + redB workLen (redN workLen
            (addN (bigVal limbBits a env) (bigVal limbBits b env)))))) := by
  refine Computes.bind (computesBig_addSum a b) ?_
  intro S1 s hS1 hs
  refine Computes.bind (computes_reduceStep hs) ?_
  intro S2 rd1 hS2 hrd1
  have h1 : EvalsBig S2 rd1.1 (fun env =>
      ofNat (redN workLen (addN (bigVal limbBits a env) (bigVal limbBits b env)))
        workLen) := hrd1.1
  have h1b : EvalsU S2 rd1.2 (fun env =>
      redB workLen (addN (bigVal limbBits a env) (bigVal limbBits b env))) := hrd1.2
  refine Computes.bind (computes_reduceStep h1) ?_
  intro S3 rd0 hS3 hrd0
  have h0b : EvalsU S3 rd0.2 (fun env =>
      redB workLen (redN workLen
        (addN (bigVal limbBits a env) (bigVal limbBits b env)))) := hrd0.2
  refine Computes.pure (EvalsF.ofU64 (EvalsU.usub (EvalsU.uc 2 (by norm_num))
    (EvalsU.add (h1b.mono hS3) h0b (fun env => ?_)) (fun env => ?_)))
  · have := redB_lt_two workLen (addN (bigVal limbBits a env) (bigVal limbBits b env))
    have := redB_lt_two workLen (redN workLen
      (addN (bigVal limbBits a env) (bigVal limbBits b env)))
    have : (4 : ℕ) < 2 ^ 64 := by norm_num
    omega
  · have := redB_lt_two workLen (addN (bigVal limbBits a env) (bigVal limbBits b env))
    have := redB_lt_two workLen (redN workLen
      (addN (bigVal limbBits a env) (bigVal limbBits b env)))
    omega

theorem computesV_subRProg (a b : Var Emu (F circomPrime)) :
    ComputesV #[] (subRProg a b)
      (fun env => emuOfNat
        (redN workLen (shiftN P256 (bigVal limbBits a env) (bigVal limbBits b env)))) := by
  refine Computes.bind (computesBig_shiftSub P256 a b) ?_
  intro S1 s hS1 hs
  refine Computes.bind (computes_reduceStep hs) ?_
  intro S2 rd hS2 hrd
  have h1 : EvalsBig S2 rd.1 (fun env =>
      ofNat (redN workLen (shiftN P256 (bigVal limbBits a env) (bigVal limbBits b env)))
        workLen) := hrd.1
  exact Computes.pure ((evalsV_emuOutF h1).congr fun env => by
    rw [lval_ofNat_of_lt (redN_lt _ _)])

theorem computesF_subQProg (a b : Var Emu (F circomPrime)) :
    ComputesF #[] (subQProg a b)
      (fun env => FiniteField.fromNat
        (redB workLen (shiftN P256 (bigVal limbBits a env) (bigVal limbBits b env)))) := by
  refine Computes.bind (computesBig_shiftSub P256 a b) ?_
  intro S1 s hS1 hs
  refine Computes.bind (computes_reduceStep hs) ?_
  intro S2 rd hS2 hrd
  have h2 : EvalsU S2 rd.2 (fun env =>
      redB workLen (shiftN P256 (bigVal limbBits a env) (bigVal limbBits b env))) := hrd.2
  exact Computes.pure (EvalsF.ofU64 h2)

theorem computesV_subLRProg (a b : Var Emu (F circomPrime)) :
    ComputesV #[] (subLRProg a b)
      (fun env => emuOfNat (redN workLen (redN workLen
        (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env))))) := by
  refine Computes.bind (computesBig_shiftSub (2 * P256) a b) ?_
  intro S1 s hS1 hs
  refine Computes.bind (computes_reduceStep hs) ?_
  intro S2 rd1 hS2 hrd1
  have h1 : EvalsBig S2 rd1.1 (fun env =>
      ofNat (redN workLen (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env)))
        workLen) := hrd1.1
  refine Computes.bind (computes_reduceStep h1) ?_
  intro S3 rd0 hS3 hrd0
  have h0 : EvalsBig S3 rd0.1 (fun env =>
      ofNat (redN workLen (redN workLen
        (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env)))) workLen) := hrd0.1
  exact Computes.pure ((evalsV_emuOutF h0).congr fun env => by
    rw [lval_ofNat_of_lt (redN_lt _ _)])

theorem computesF_subLQProg (a b : Var Emu (F circomPrime)) :
    ComputesF #[] (subLQProg a b)
      (fun env => FiniteField.fromNat
        (redB workLen (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env))
          + redB workLen (redN workLen
            (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env))))) := by
  refine Computes.bind (computesBig_shiftSub (2 * P256) a b) ?_
  intro S1 s hS1 hs
  refine Computes.bind (computes_reduceStep hs) ?_
  intro S2 rd1 hS2 hrd1
  have h1 : EvalsBig S2 rd1.1 (fun env =>
      ofNat (redN workLen (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env)))
        workLen) := hrd1.1
  have h1b : EvalsU S2 rd1.2 (fun env =>
      redB workLen (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env))) := hrd1.2
  refine Computes.bind (computes_reduceStep h1) ?_
  intro S3 rd0 hS3 hrd0
  have h0b : EvalsU S3 rd0.2 (fun env =>
      redB workLen (redN workLen
        (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env)))) := hrd0.2
  refine Computes.pure (EvalsF.ofU64 (EvalsU.add (h1b.mono hS3) h0b (fun env => ?_)))
  have := redB_lt_two workLen (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env))
  have := redB_lt_two workLen (redN workLen
    (shiftN (2 * P256) (bigVal limbBits a env) (bigVal limbBits b env)))
  have : (4 : ℕ) < 2 ^ 64 := by norm_num
  omega


/-! ### Reading the add and subtract witnesses under the gadgets' assumptions -/

/-- The two operand values, on normalized limb vectors. -/
theorem bigVal_pair {a b : Var Emu (F circomPrime)} {env : ProverEnvironment (F circomPrime)}
    (hna : BigInt.Normalized limbBits (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized limbBits (b.map (Expression.eval env.toEnvironment))) :
    bigVal limbBits a env = evalEmu env a ∧ bigVal limbBits b env = evalEmu env b :=
  ⟨bigVal_eq_evalEmu a env hna, bigVal_eq_evalEmu b env hnb⟩

theorem eval_addRProg_of (a b : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (hna : BigInt.Normalized limbBits (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized limbBits (b.map (Expression.eval env.toEnvironment)))
    (hva : evalEmu env a < P256) (hvb : evalEmu env b < P256) :
    Witgen.VExpr.eval
        { env := env, locals := Witgen.evalSteps env (addRProg a b #[]).2.toList }
        (addRProg a b #[]).1
      = emuOfNat ((evalEmu env a + evalEmu env b) % P256) := by
  obtain ⟨ha, hb⟩ := bigVal_pair hna hnb
  rw [IRLimbs.eval_program (computesV_addRProg a b) env, ha, hb,
    addN_eq (by rw [← ha]; exact bigVal_lt_span a env) (by rw [← hb]; exact bigVal_lt_span b env),
    redN_eq (by omega)]

theorem eval_addQProg_of (a b : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (hna : BigInt.Normalized limbBits (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized limbBits (b.map (Expression.eval env.toEnvironment)))
    (hva : evalEmu env a < P256) (hvb : evalEmu env b < P256) :
    Witgen.FExpr.eval
        { env := env, locals := Witgen.evalSteps env (addQProg a b #[]).2.toList }
        (addQProg a b #[]).1
      = (((evalEmu env a + evalEmu env b) / P256 : ℕ) : F circomPrime) := by
  obtain ⟨ha, hb⟩ := bigVal_pair hna hnb
  rw [eval_programF (computesF_addQProg a b) env, ha, hb,
    addN_eq (by rw [← ha]; exact bigVal_lt_span a env) (by rw [← hb]; exact bigVal_lt_span b env),
    redB_eq (by omega), FiniteField.fromNat_F]

theorem eval_addLRProg_of (a b : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (hna : BigInt.Normalized limbBits (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized limbBits (b.map (Expression.eval env.toEnvironment))) :
    Witgen.VExpr.eval
        { env := env, locals := Witgen.evalSteps env (addLRProg a b #[]).2.toList }
        (addLRProg a b #[]).1
      = emuOfNat ((evalEmu env a + evalEmu env b) % P256) := by
  obtain ⟨ha, hb⟩ := bigVal_pair hna hnb
  have hsa : evalEmu env a < emuSpan := by rw [← ha]; exact bigVal_lt_span a env
  have hsb : evalEmu env b < emuSpan := by rw [← hb]; exact bigVal_lt_span b env
  have hlt : evalEmu env a + evalEmu env b < 3 * P256 := by
    have : 2 * emuSpan < 3 * P256 := by decide
    omega
  rw [IRLimbs.eval_program (computesV_addLRProg a b) env, ha, hb, addN_eq hsa hsb, redN2_eq hlt]

theorem eval_addLQProg_of (a b : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (hna : BigInt.Normalized limbBits (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized limbBits (b.map (Expression.eval env.toEnvironment))) :
    Witgen.FExpr.eval
        { env := env, locals := Witgen.evalSteps env (addLQProg a b #[]).2.toList }
        (addLQProg a b #[]).1
      = (((evalEmu env a + evalEmu env b) / P256 : ℕ) : F circomPrime) := by
  obtain ⟨ha, hb⟩ := bigVal_pair hna hnb
  have hsa : evalEmu env a < emuSpan := by rw [← ha]; exact bigVal_lt_span a env
  have hsb : evalEmu env b < emuSpan := by rw [← hb]; exact bigVal_lt_span b env
  have hlt : evalEmu env a + evalEmu env b < 3 * P256 := by
    have : 2 * emuSpan < 3 * P256 := by decide
    omega
  rw [eval_programF (computesF_addLQProg a b) env, ha, hb, addN_eq hsa hsb, redB2_eq hlt,
    FiniteField.fromNat_F]

theorem eval_subRProg_of (a b : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (hna : BigInt.Normalized limbBits (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized limbBits (b.map (Expression.eval env.toEnvironment)))
    (hva : evalEmu env a < P256) (hvb : evalEmu env b < P256) :
    Witgen.VExpr.eval
        { env := env, locals := Witgen.evalSteps env (subRProg a b #[]).2.toList }
        (subRProg a b #[]).1
      = emuOfNat ((evalEmu env a + P256 - evalEmu env b) % P256) := by
  obtain ⟨ha, hb⟩ := bigVal_pair hna hnb
  have hs : shiftN P256 (bigVal limbBits a env) (bigVal limbBits b env)
      = evalEmu env a + P256 - evalEmu env b := by
    rw [ha, hb]
    refine shiftN_eq (by rw [← ha]; exact bigVal_lt_span a env)
      (by rw [← hb]; exact bigVal_lt_span b env) ?_ (by omega)
    have := two_mul_modulus_lt_work
    omega
  rw [IRLimbs.eval_program (computesV_subRProg a b) env, hs, redN_eq (by omega)]

theorem eval_subQProg_of (a b : Var Emu (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (hna : BigInt.Normalized limbBits (a.map (Expression.eval env.toEnvironment)))
    (hnb : BigInt.Normalized limbBits (b.map (Expression.eval env.toEnvironment)))
    (hva : evalEmu env a < P256) (hvb : evalEmu env b < P256) :
    Witgen.FExpr.eval
        { env := env, locals := Witgen.evalSteps env (subQProg a b #[]).2.toList }
        (subQProg a b #[]).1
      = ((if evalEmu env a < evalEmu env b then 1 else 0 : ℕ) : F circomPrime) := by
  obtain ⟨ha, hb⟩ := bigVal_pair hna hnb
  have hs : shiftN P256 (bigVal limbBits a env) (bigVal limbBits b env)
      = evalEmu env a + P256 - evalEmu env b := by
    rw [ha, hb]
    refine shiftN_eq (by rw [← ha]; exact bigVal_lt_span a env)
      (by rw [← hb]; exact bigVal_lt_span b env) ?_ (by omega)
    have := two_mul_modulus_lt_work
    omega
  rw [eval_programF (computesF_subQProg a b) env, hs, redB, FiniteField.fromNat_F,
    Nat.mod_eq_of_lt modulus_lt_work,
    Nat.mod_eq_of_lt (show evalEmu env a + P256 - evalEmu env b < base ^ workLen by
      have := two_mul_modulus_lt_work; omega)]
  by_cases h : evalEmu env a < evalEmu env b
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg h]

/-! ### The witness-site bridges

Each site reads its program back through `IRLimbs.eval_program`; the `computableWitnesses`
obligation is the same statement with the environment varying, and follows from the
operands' limb values agreeing.
-/

theorem eval_toIR_addRProg_congr (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : bigVal limbBits a env = bigVal limbBits a env')
    (hb : bigVal limbBits b env = bigVal limbBits b env') :
    (addRProg a b).toIR.eval env = (addRProg a b).toIR.eval env' :=
  eval_toIR_congr (computesV_addRProg a b) (by rw [ha, hb])

theorem eval_toIR_addQProg_congr (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : bigVal limbBits a env = bigVal limbBits a env')
    (hb : bigVal limbBits b env = bigVal limbBits b env') :
    (Witgen.M.toIRLiteral (value := field) (addQProg a b)).eval env
      = (Witgen.M.toIRLiteral (value := field) (addQProg a b)).eval env' :=
  eval_toIRLiteralF_congr (computesF_addQProg a b) (by rw [ha, hb])

theorem eval_toIR_addLRProg_congr (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : bigVal limbBits a env = bigVal limbBits a env')
    (hb : bigVal limbBits b env = bigVal limbBits b env') :
    (addLRProg a b).toIR.eval env = (addLRProg a b).toIR.eval env' :=
  eval_toIR_congr (computesV_addLRProg a b) (by rw [ha, hb])

theorem eval_toIR_addLQProg_congr (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : bigVal limbBits a env = bigVal limbBits a env')
    (hb : bigVal limbBits b env = bigVal limbBits b env') :
    (Witgen.M.toIRLiteral (value := field) (addLQProg a b)).eval env
      = (Witgen.M.toIRLiteral (value := field) (addLQProg a b)).eval env' :=
  eval_toIRLiteralF_congr (computesF_addLQProg a b) (by rw [ha, hb])

theorem eval_toIR_subRProg_congr (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : bigVal limbBits a env = bigVal limbBits a env')
    (hb : bigVal limbBits b env = bigVal limbBits b env') :
    (subRProg a b).toIR.eval env = (subRProg a b).toIR.eval env' :=
  eval_toIR_congr (computesV_subRProg a b) (by rw [ha, hb])

theorem eval_toIR_subQProg_congr (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : bigVal limbBits a env = bigVal limbBits a env')
    (hb : bigVal limbBits b env = bigVal limbBits b env') :
    (Witgen.M.toIRLiteral (value := field) (subQProg a b)).eval env
      = (Witgen.M.toIRLiteral (value := field) (subQProg a b)).eval env' :=
  eval_toIRLiteralF_congr (computesF_subQProg a b) (by rw [ha, hb])

theorem eval_toIR_subLRProg_congr (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : bigVal limbBits a env = bigVal limbBits a env')
    (hb : bigVal limbBits b env = bigVal limbBits b env') :
    (subLRProg a b).toIR.eval env = (subLRProg a b).toIR.eval env' :=
  eval_toIR_congr (computesV_subLRProg a b) (by rw [ha, hb])

theorem eval_toIR_subLQProg_congr (a b : Var Emu (F circomPrime))
    {env env' : ProverEnvironment (F circomPrime)}
    (ha : bigVal limbBits a env = bigVal limbBits a env')
    (hb : bigVal limbBits b env = bigVal limbBits b env') :
    (Witgen.M.toIRLiteral (value := field) (subLQProg a b)).eval env
      = (Witgen.M.toIRLiteral (value := field) (subLQProg a b)).eval env' :=
  eval_toIRLiteralF_congr (computesF_subLQProg a b) (by rw [ha, hb])

/-! ### Sealing the programs

The six programs are sealed once their specifications are proved. A witness program
is *data*, and `circuit_norm` would happily evaluate one: `emuDigits` is a `map` over a
`List.range`, so `simp` can unfold the digit lists and then run `addP`/`subP`/`selectP`
over them, blowing the elaborator up on a term that no proof ever needs to see. Every
fact about them is already stated above; downstream files reason through those.
-/

attribute [irreducible]
  addRProg addQProg addLRProg addLQProg subRProg subQProg subLRProg subLQProg

end IREmu

/-! ## Decoding to the trusted spec -/

/-- Decode an emulated element to the secp256k1 base field of the trusted
spec. -/
def decodeFe (x : Emu (F circomPrime)) : Specs.Secp256k1.Fp :=
  ((x.value limbBits : ℕ) : Specs.Secp256k1.Fp)

/-- A well-formed emulated field element: normalized limbs and a canonical
(`< P256`) value. On canonical elements `decodeFe` is injective
(`BigInt.value_inj`), so spec-level equality is equivalent to limb-wise
equality. -/
def Fe.Valid (x : Emu (F circomPrime)) : Prop :=
  x.Normalized limbBits ∧ x.value limbBits < P256

/-! ## Flagged points -/

/-- A flagged secp256k1 point: affine coordinates as emulated field elements
plus a boolean is-infinity flag. The coordinates carry no meaning when the
flag is set. This is the in-circuit representation of
`Specs.ShortWeierstrass.GroupPoint`. -/
structure FlaggedPoint (F : Type) where
  x : Emu F
  y : Emu F
  isInf : F
deriving ProvableStruct

/-- Decode a flagged point to a spec-level group point. -/
def decodePoint (P : FlaggedPoint (F circomPrime)) :
    Specs.ShortWeierstrass.GroupPoint Specs.Secp256k1.Fp :=
  if P.isInf = 1 then .infinity
  else .affine { x := decodeFe P.x, y := decodeFe P.y }

/-- A well-formed flagged point: boolean flag, valid coordinates, and — when
finite — the decoded point lies on the curve. -/
def FlaggedPoint.Valid (P : FlaggedPoint (F circomPrime)) : Prop :=
  IsBool P.isInf ∧ Fe.Valid P.x ∧ Fe.Valid P.y ∧
    (P.isInf = 0 →
      Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve
        { x := decodeFe P.x, y := decodeFe P.y })

/-- The constant point at infinity (coordinates zero, flag set). -/
def infConst : Var FlaggedPoint (F circomPrime) :=
  { x := zeroConst, y := zeroConst,
    isInf := ((1 : F circomPrime) : Expression (F circomPrime)) }

/-- Per-field projection of an `eval`-agreement hypothesis on a `FlaggedPoint`.
The `Var FlaggedPoint` `match` no longer iota-reduces on a non-constructor term,
so the destructuring has to happen here, once. -/
lemma eval_flaggedPoint_parts {v : Var FlaggedPoint (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)}
    (h : eval env v = eval env' v) :
    eval env v.x = eval env' v.x ∧ eval env v.y = eval env' v.y ∧
      Expression.eval env.toEnvironment v.isInf = Expression.eval env'.toEnvironment v.isInf := by
  obtain ⟨x, y, isInf⟩ := v
  simp only [circuit_norm, FlaggedPoint.mk.injEq] at h ⊢
  exact h

end Solution.Secp256k1ScalarMul
