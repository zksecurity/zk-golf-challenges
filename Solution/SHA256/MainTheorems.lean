import Challenge.Instances.SHA256.Interface
import Solution.SHA256.PaddingTheorems
import Solution.SHA256.WitgenU64

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface
open Solution.SHA256.WitgenU64

/-!
# Helper lemmas for the top-level `Main` circuit

Gadget-private helpers (and the witness definitions) used by `main`, its
`soundness`/`completeness` proofs. These re-prove the private `SHA256Rounds`
helpers and bridge `paddedBlock` to `specBlock`. They are stated over the
concrete `circomPrime`. Shared lemmas live in `Theorems`/`PaddingTheorems`.
-/

instance hCircomPrimeLarge : Fact (circomPrime > 2^33) := ⟨by
  norm_num [circomPrime]⟩

def paddedBitsWitness (input : Var Input (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : SHA256PaddedBits (F circomPrime) :=
  paddedBitsValue ((eval env input.message).map ZMod.val) (Expression.eval env input.messageLen).val

/-!
## Witness generation through the witness IR

`main` witnesses two vectors of its own, the padded message bits and the one-hot
length flags, and generates both with deep-embedded witness programs. Each is a single
O(1)-size `.range` body: the 2560 padded bits share one loop body over the flat bit
index, and the 256 length flags share one equality test. The flag program is a
one-liner and lives inline in `main`; only the padded bits get a named program
(`paddedBitsIR`) here, with the `getElem_eval_*` bridges below connecting it to
`paddedBitsWitness`, the value every functional proof is stated over. Every truncated
subtraction goes through this solution's own `nsub` helper, whose side conditions only
have to hold in the `.ite` branch actually taken.
-/

section WitgenIR

/-! ### The ℕ view of the u64 sort, and truncated subtraction

The witness IR's integer sort is `UInt64`: every operation wraps modulo `2^64`. All the
padding arithmetic below is byte offsets and lengths under `2^16`, so the wrap never
fires and the honest value of a program is its `UInt64.toNat`. `nval` names that view,
so the bridges stay stated over `ℕ` exactly as they were.

The sort has no subtraction, but it wraps, so `a + (2^64 - 1) · b` *is* `a - b`
whenever `b ≤ a`. That is `nsub`: unlike a field round trip it needs no bound on the
minuend, only `b ≤ a` — and because `U64Expr.eval` of an `.ite` only evaluates the
branch taken, an `nsub` sitting in an untaken branch needs nothing at all. Witgen
helpers are solution-local (the analogue of a circom function), so both live in
`Solution/SHA256/WitgenU64.lean` rather than in the trusted challenge project. -/

/-! ### Subtraction-free closed form of the block count

`numBlocksForLen` is spelled with a truncated subtraction inside a `% 64`; the
equivalent `(len + 72) / 64` has none, which keeps `totalLenIR` free of `nsub`. -/

theorem numBlocksForLen_eq (len : ℕ) : numBlocksForLen len = (len + 72) / 64 := by
  unfold numBlocksForLen; omega

/-! ### The witness-IR programs -/

/-- The padded length in bytes, `numBlocksForLen len * 64`, spelled through the
subtraction-free block count `(len + 72) / 64`. -/
def totalLenIR (len : Witgen.U64Expr (F circomPrime)) : Witgen.U64Expr (F circomPrime) :=
  (len + 72) / 64 * 64

/-- `specPaddedByteConst` as a witness-IR ℕ expression: the three nested `if`s
translate branch for branch. `j < totalLen - 8` becomes `j + 8 < totalLen` (valid
because `totalLen ≥ 64`), and the only remaining subtraction, the length-field byte
offset `totalLen - 1 - j`, is an `nsub` whose side conditions hold in the branch that
takes it (`j < totalLen ≤ j + 8`). -/
def specPaddedByteConstIR (len j : Witgen.U64Expr (F circomPrime)) : Witgen.U64Expr (F circomPrime) :=
  .ite (j =? len) 128 <|
    .ite (j + 8 <? totalLenIR len) 0 <|
      .ite (j <? totalLenIR len)
        (((len * 8) >>> (8 * nsub (totalLenIR len) (j + 1))) % 256)
        0

/-- `specPaddedByte` as a witness-IR ℕ expression: the message read is a `listGet`
at the computed byte index, guarded by the same two conditions as the `dite`. -/
def specPaddedByteIR (msgVar : Var (fields inputBufferLen) (F circomPrime))
    (len j : Witgen.U64Expr (F circomPrime)) : Witgen.U64Expr (F circomPrime) :=
  .ite ((j <? len) &&& (j <? (256 : Witgen.U64Expr (F circomPrime))))
    msgVar[j].val
    (specPaddedByteConstIR len j)

/-- The padded byte index holding flat bit `i` (`nsub` for the big-endian
byte-in-word flip `3 - i % 32 / 8`, which is always in range). -/
def byteIdxIR (i : Witgen.U64Expr (F circomPrime)) : Witgen.U64Expr (F circomPrime) :=
  i / 512 * 64 + i % 512 / 32 * 4 + nsub 3 (i % 32 / 8)

/-! ### Eval bridges -/

theorem eval_totalLenIR (ctx : Witgen.Ctx (F circomPrime))
    (len : Witgen.U64Expr (F circomPrime)) (hlen : nval ctx len < 2 ^ 32) :
    nval ctx (totalLenIR len) = numBlocksForLen (nval ctx len) * 64 := by
  simp [totalLenIR, circuit_norm, numBlocksForLen_eq, UInt64.toNat_ofNat']

theorem eval_byteIdxIR (ctx : Witgen.Ctx (F circomPrime))
    (i : Witgen.U64Expr (F circomPrime)) (hi : nval ctx i < 2 ^ 32) :
    nval ctx (byteIdxIR i)
      = nval ctx i / 512 * 64 + nval ctx i % 512 / 32 * 4
          + (3 - nval ctx i % 32 / 8) := by
  simp only [byteIdxIR, circuit_norm, ofNat_def, nval_add, nval_mul, nval_div, nval_mod,
    nval_nsub_wrap, nval_const_ofNat, nval_const]
  omega

theorem totalLen_ge (len : ℕ) : 64 ≤ numBlocksForLen len * 64 := by
  have : 1 ≤ numBlocksForLen len := by rw [numBlocksForLen_eq]; omega
  omega

theorem eval_specPaddedByteConstIR (ctx : Witgen.Ctx (F circomPrime))
    (len j : Witgen.U64Expr (F circomPrime)) (hj : nval ctx j < 320)
    (hlen : nval ctx len < 2 ^ 32) :
    nval ctx (specPaddedByteConstIR len j)
      = specPaddedByteConst (nval ctx len) (nval ctx j) := by
  have hT := totalLen_ge (nval ctx len)
  have hTlt : numBlocksForLen (nval ctx len) * 64 < 2 ^ 33 := by
    rw [numBlocksForLen_eq]; omega
  have hTot : nval ctx (totalLenIR len) = numBlocksForLen (nval ctx len) * 64 :=
    eval_totalLenIR ctx len hlen
  unfold specPaddedByteConstIR specPaddedByteConst
  simp only [nval_norm, hTot]
  rw [show (nval ctx j + 8) % 18446744073709551616 = nval ctx j + 8 from by omega]
  -- branch 1: the `0x80` marker sits exactly at `j = len`
  by_cases h1 : nval ctx j = nval ctx len
  · simp only [h1, decide_true, ite_true, if_pos rfl]
  simp only [h1, decide_false, Bool.false_eq_true, ite_false, if_neg h1]
  -- branch 2: the zero run, `j + 8 < totalLen`
  by_cases h2 : nval ctx j + 8 < numBlocksForLen (nval ctx len) * 64
  · rw [if_pos (by omega : nval ctx j < numBlocksForLen (nval ctx len) * 64 - 8)]
    simp only [h2, decide_true, ite_true]
  rw [if_neg (by omega : ¬ nval ctx j < numBlocksForLen (nval ctx len) * 64 - 8)]
  simp only [h2, decide_false, Bool.false_eq_true, ite_false]
  -- branch 3: the 8-byte big-endian length field, the one place `nsub` is taken.
  -- `¬(j + 8 < totalLen)` bounds the shift by `8 · 7 = 56 < 64`, so it is not reduced.
  by_cases h3 : nval ctx j < numBlocksForLen (nval ctx len) * 64
  · rw [if_pos h3]
    simp only [h3, decide_true, ite_true]
    rw [show (nval ctx len * 8) % 18446744073709551616 = nval ctx len * 8 from by omega,
      show 8 * ((numBlocksForLen (nval ctx len) * 64
                + 18446744073709551615 * ((nval ctx j + 1) % 18446744073709551616))
              % 18446744073709551616) % 18446744073709551616 % 64
          = 8 * (numBlocksForLen (nval ctx len) * 64 - 1 - nval ctx j) from by omega,
      Nat.shiftRight_eq_div_pow]
  rw [if_neg h3]
  simp only [h3, decide_false, Bool.false_eq_true, ite_false]

theorem eval_specPaddedByteIR (msgVar : Var (fields inputBufferLen) (F circomPrime))
    (msg : Vector ℕ inputBufferLen) (ctx : Witgen.Ctx (F circomPrime))
    (hmsg : ∀ k (hk : k < inputBufferLen),
      msg[k] = ZMod.val (Expression.eval ctx.env.toEnvironment msgVar[k]))
    (hbyte : ∀ k (hk : k < inputBufferLen), msg[k] < 2 ^ 64)
    (len j : Witgen.U64Expr (F circomPrime)) (hj : nval ctx j < 320)
    (hlen : nval ctx len < 2 ^ 32) :
    nval ctx (specPaddedByteIR msgVar len j)
      = specPaddedByte msg (nval ctx len) (nval ctx j) := by
  unfold specPaddedByteIR specPaddedByte
  by_cases hc : nval ctx j < nval ctx len ∧ nval ctx j < inputBufferLen
  · rw [dif_pos hc]
    rw [show nval ctx
        (Witgen.U64Expr.ite ((j <? len) &&& (j <? (256 : Witgen.U64Expr (F circomPrime))))
          msgVar[j].val (specPaddedByteConstIR len j))
        = nval ctx msgVar[j].val from by
      simp only [nval_norm, hc.1, decide_true, Bool.true_and,
        show nval ctx j < 256 from by simpa [inputBufferLen] using hc.2, ite_true]]
    -- the message read is a `listGet` at an in-range index, and the byte it returns is
    -- below `2^64`, so the sort's truncation is the identity
    simp only [nval_norm, circuit_norm]
    rw [dif_pos hc.2, ← hmsg _ hc.2]
    exact Nat.mod_eq_of_lt (by simpa using hbyte _ hc.2)
  · rw [dif_neg hc]
    rw [show nval ctx
        (Witgen.U64Expr.ite ((j <? len) &&& (j <? (256 : Witgen.U64Expr (F circomPrime))))
          msgVar[j].val (specPaddedByteConstIR len j))
        = nval ctx (specPaddedByteConstIR len j) from by
      simp only [nval_norm]
      rw [if_neg (by simpa [inputBufferLen, not_and, not_lt] using hc)]]
    exact eval_specPaddedByteConstIR ctx len j hj hlen

/-! ### The top-level padded-bits witness program

The other top-level witness, the one-hot length flags, is a single `.range` body over
one equality test and is written inline in `main`. -/

/-- Witness program for the 2560 padded message bits: one `.range` body over the flat
bit index, reading bit `i % 8` of the expected padded byte at `byteIdxIR i`. -/
def paddedBitsIR (input : Var Input (F circomPrime)) :
    Witgen.VExpr (F circomPrime) paddedBitsLen :=
  .range paddedBitsLen fun i =>
    (((specPaddedByteIR input.message input.messageLen.val (byteIdxIR i)) >>> (i % 8)) % 2).toField

/-- `paddedBitsIR` computes exactly `paddedBitsValue` on the message bytes read out
of the symbolic message vector. The two bounds are what the u64 sort needs: the
message bytes and the length have to fit in the sort for its arithmetic to be the
honest arithmetic. Both hold for every input the circuit assumes. -/
theorem getElem_eval_paddedBitsIR (input : Var Input (F circomPrime))
    (msg : Vector ℕ inputBufferLen) (env : ProverEnvironment (F circomPrime))
    (hmsg : ∀ k (hk : k < inputBufferLen),
      msg[k] = ZMod.val (Expression.eval env.toEnvironment input.message[k]))
    (hbyte : ∀ k (hk : k < inputBufferLen), msg[k] < 2 ^ 64)
    (hlen : ZMod.val (Expression.eval env.toEnvironment input.messageLen) < 2 ^ 32)
    (i : ℕ) (hi : i < paddedBitsLen) :
    ((paddedBitsIR input).eval { env })[i]
      = (paddedBitsValue msg
          (ZMod.val (Expression.eval env.toEnvironment input.messageLen)))[i] := by
  simp only [paddedBitsLen, paddedBlocksLen] at hi
  rw [paddedBitsIR, Witgen.VExpr.range_def, Witgen.VExpr.getElem_eval_mapRange _ _ _ i hi,
    paddedBitsValue, Vector.getElem_ofFn]
  have hb : nval { env := env, locals := #[], idx := i }
      (byteIdxIR Witgen.U64Expr.idx)
      = i / 512 * 64 + i % 512 / 32 * 4 + (3 - i % 32 / 8) := by
    rw [eval_byteIdxIR _ _ (by simp only [nval_norm]; omega)]
    simp only [nval_norm]
    omega
  have hblt : nval { env := env, locals := #[], idx := i }
      (byteIdxIR Witgen.U64Expr.idx) < 320 := by rw [hb]; omega
  have hlen' : nval { env := env, locals := #[], idx := i } input.messageLen.val < 2 ^ 32 := by
    simp only [nval_norm, Witgen.FExpr.eval, FiniteField.val_F]
    omega
  rw [show Witgen.FExpr.eval { env := env, locals := #[], idx := i }
      ((((specPaddedByteIR input.message input.messageLen.val (byteIdxIR Witgen.U64Expr.idx))
        >>> (Witgen.U64Expr.idx % 8)) % 2).toField)
      = ((((nval { env := env, locals := #[], idx := i }
          (specPaddedByteIR input.message input.messageLen.val (byteIdxIR Witgen.U64Expr.idx)))
          >>> (i % 8)) % 2 : ℕ) : F circomPrime) from by
    simp only [circuit_norm, nval_norm]]
  rw [eval_specPaddedByteIR input.message msg _ hmsg hbyte _ _ hblt hlen', hb,
    -- the length read back through the sort is the length itself
    show nval { env := env, locals := #[], idx := i } input.messageLen.val
        = ZMod.val (Expression.eval env.toEnvironment input.messageLen) from by
      simp only [nval_norm, Witgen.FExpr.eval, FiniteField.val_F]
      omega,
    Nat.shiftRight_eq_div_pow]

/-- The value bridge at the level of `paddedBitsWitness`. The two bounds are the same
ones `getElem_eval_paddedBitsIR` needs: a byte and a length that fit in the u64 sort.
`completeness` gets both from the circuit's assumptions. -/
theorem getElem_eval_paddedBitsWitness (input : Var Input (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (hbyte : ∀ k (hk : k < inputBufferLen),
      ZMod.val (Expression.eval env.toEnvironment input.message[k]) < 2 ^ 64)
    (hlen : ZMod.val (Expression.eval env.toEnvironment input.messageLen) < 2 ^ 32)
    (i : ℕ) (hi : i < paddedBitsLen) :
    ((paddedBitsIR input).eval { env })[i] = (paddedBitsWitness input env)[i] := by
  rw [paddedBitsWitness]
  have hmsg : ∀ k (hk : k < inputBufferLen),
      ((eval env input.message).map ZMod.val)[k]
        = ZMod.val (Expression.eval env.toEnvironment input.message[k]) := by
    intro k hk
    rw [Vector.getElem_map,
      show eval env input.message
          = Vector.map (Expression.eval env.toEnvironment) input.message from
        CircuitType.eval_var_fields_prover .., Vector.getElem_map]
  refine getElem_eval_paddedBitsIR input _ env hmsg (fun k hk => ?_) hlen i hi
  rw [hmsg k hk]; exact hbyte k hk

/-- Vector-level value bridge, for `completeness`. -/
theorem eval_paddedBitsIR_eq (input : Var Input (F circomPrime))
    (env : ProverEnvironment (F circomPrime))
    (hbyte : ∀ k (hk : k < inputBufferLen),
      ZMod.val (Expression.eval env.toEnvironment input.message[k]) < 2 ^ 64)
    (hlen : ZMod.val (Expression.eval env.toEnvironment input.messageLen) < 2 ^ 32) :
    (paddedBitsIR input).eval { env } = paddedBitsWitness input env :=
  Vector.ext fun i hi => getElem_eval_paddedBitsWitness input env hbyte hlen i hi

/-! ### Congruence bridges, for the `computableWitness` obligation

The value bridges above are conditional: the u64 sort only agrees with the ℕ padding
spec when the bytes and the length fit in it. `computableWitnesses` has no assumptions
to draw such a bound from — and does not need one, because what it has to show is only
that the generator *reads nothing but the input*. These lemmas say exactly that, one
per program, and each is proved by normalising both sides with the same `nval_norm`
set and rewriting the two leaves. -/

/-- Reading a list of embedded circuit expressions at a computed index depends on the
environment only through those expressions. -/
theorem evalList_expr_congr (l : List (Expression (F circomPrime)))
    (ctx ctx' : Witgen.Ctx (F circomPrime))
    (h : ∀ x ∈ l, Expression.eval ctx.env.toEnvironment x
      = Expression.eval ctx'.env.toEnvironment x) (k : ℕ) :
    Witgen.FExpr.evalList ctx k (l.map Witgen.FExpr.expr)
      = Witgen.FExpr.evalList ctx' k (l.map Witgen.FExpr.expr) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    cases k with
    | zero => exact h a (by simp)
    | succ k => exact ih (fun x hx => h x (by simp [hx])) k

theorem nval_byteIdxIR_congr (ctx ctx' : Witgen.Ctx (F circomPrime))
    (i : Witgen.U64Expr (F circomPrime)) (hi : nval ctx i = nval ctx' i) :
    nval ctx (byteIdxIR i) = nval ctx' (byteIdxIR i) := by
  simp only [byteIdxIR, nval_norm, hi]

theorem nval_specPaddedByteConstIR_congr (ctx ctx' : Witgen.Ctx (F circomPrime))
    (len j : Witgen.U64Expr (F circomPrime))
    (hlen : nval ctx len = nval ctx' len) (hj : nval ctx j = nval ctx' j) :
    nval ctx (specPaddedByteConstIR len j)
      = nval ctx' (specPaddedByteConstIR len j) := by
  simp only [specPaddedByteConstIR, totalLenIR, nval_norm, hlen, hj]

theorem nval_specPaddedByteIR_congr (msgVar : Var (fields inputBufferLen) (F circomPrime))
    (ctx ctx' : Witgen.Ctx (F circomPrime)) (len j : Witgen.U64Expr (F circomPrime))
    (hmsg : ∀ x ∈ msgVar.toList, Expression.eval ctx.env.toEnvironment x
      = Expression.eval ctx'.env.toEnvironment x)
    (hlen : nval ctx len = nval ctx' len) (hj : nval ctx j = nval ctx' j) :
    nval ctx (specPaddedByteIR msgVar len j)
      = nval ctx' (specPaddedByteIR msgVar len j) := by
  have hread : Witgen.FExpr.eval ctx msgVar[j] = Witgen.FExpr.eval ctx' msgVar[j] := by
    show Witgen.FExpr.evalList ctx (nval ctx j) (msgVar.toList.map Witgen.FExpr.expr)
        = Witgen.FExpr.evalList ctx' (nval ctx' j) (msgVar.toList.map Witgen.FExpr.expr)
    rw [hj]
    exact evalList_expr_congr msgVar.toList ctx ctx' hmsg _
  simp only [specPaddedByteIR, nval_norm, hlen, hj, hread,
    nval_specPaddedByteConstIR_congr ctx ctx' len j hlen hj]

/-- The witness vector reads the environment only at the message cells and the length.
This is what `computableWitnesses` needs; it holds for every environment, with no bound
on either. -/
theorem eval_paddedBitsIR_congr (input : Var Input (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime))
    (hmsg : ∀ x ∈ input.message.toList, Expression.eval env.toEnvironment x
      = Expression.eval env'.toEnvironment x)
    (hlen : Expression.eval env.toEnvironment input.messageLen
      = Expression.eval env'.toEnvironment input.messageLen) :
    (paddedBitsIR input).eval { env := env }
      = (paddedBitsIR input).eval { env := env' } := by
  refine Vector.ext fun i hi => ?_
  rw [paddedBitsIR, Witgen.VExpr.range_def,
    Witgen.VExpr.getElem_eval_mapRange _ _ _ i hi,
    Witgen.VExpr.getElem_eval_mapRange _ _ _ i hi]
  have hlen' : nval { env := env, locals := #[], idx := i } input.messageLen.val
      = nval { env := env', locals := #[], idx := i } input.messageLen.val := by
    simp only [nval_norm, Witgen.FExpr.eval, hlen]
  have hj : nval { env := env, locals := #[], idx := i } (byteIdxIR Witgen.U64Expr.idx)
      = nval { env := env', locals := #[], idx := i } (byteIdxIR Witgen.U64Expr.idx) :=
    nval_byteIdxIR_congr _ _ _ (by simp only [nval_norm])
  simp only [circuit_norm, nval_norm,
    nval_specPaddedByteIR_congr input.message _ _ _ _ hmsg hlen' hj]

end WitgenIR

/-! ## Local helpers (re-proving private SHA256Rounds helpers) -/

/-- `constWord32 n` evaluated is always normalized. -/
lemma normalized_constWord32 (env : Environment (F circomPrime)) (n : ℕ) :
    Normalized (Vector.map (Expression.eval env) (constWord32 (p := circomPrime) n)) := by
  intro i
  have h : (n / 2^i.val % 2 : ℕ) = 0 ∨ (n / 2^i.val % 2 : ℕ) = 1 := by omega
  rcases h with h | h
  · left; simp [constWord32, Expression.eval, h]
  · right; simp [constWord32, Expression.eval, h]

lemma valueBits_constWord32 (env : Environment (F circomPrime)) (n : ℕ) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p := circomPrime) n)) = n % 2^32 := by
  simp only [valueBits, constWord32]
  have h2 : ∀ i : Fin 32, ((n / 2^i.val % 2 : ℕ) : F circomPrime).val = n / 2^i.val % 2 := by
    intro i
    have hp : 2^33 < circomPrime := hCircomPrimeLarge.out
    have hlt : (n / 2^i.val % 2 : ℕ) < circomPrime := by omega
    exact ZMod.val_natCast_of_lt hlt
  have heq : (∑ i : Fin 32, (Vector.map (Expression.eval env)
        (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F circomPrime))))[i].val * 2^i.val)
      = ∑ i : Fin 32, (n / 2^i.val % 2) * 2^i.val := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [show (Vector.map (Expression.eval env)
          (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F circomPrime))))[i] =
        ((n / 2^i.val % 2 : ℕ) : F circomPrime) from by
      simp [Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]]
    rw [h2 i]
  rw [heq]
  have key : ∀ (m : ℕ), ∑ i : Fin m, (n / 2^i.val % 2) * 2^i.val = n % 2^m := by
    intro m
    induction m with
    | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, pow_zero, Nat.mod_one]
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ih, Nat.mod_pow_succ]; ring
  exact key 32

lemma valueBits_constWord32_of_lt (env : Environment (F circomPrime)) {n : ℕ} (h : n < 2^32) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p := circomPrime) n)) = n := by
  rw [valueBits_constWord32, Nat.mod_eq_of_lt h]

lemma H0_lt (i : ℕ) (hi : i < 8) : Specs.SHA256.H0[i]'hi < 2^32 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    h|h|h|h|h|h|h|h <;> subst h <;> simp [Specs.SHA256.H0]

/-- The `i`-th word of the evaluated H0 const state is `Vector.map (Expression.eval env) (constWord32 H0[i])`. -/
lemma state0_getElem (env : Environment (F circomPrime)) (i : ℕ) (hi : i < 8) :
    (eval env (Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val])))[i]'hi =
      Vector.map (Expression.eval env)
        ((Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val]))[i]'hi) := by
  rw [show Vector.map (Expression.eval env)
        ((Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val]))[i]'hi) =
      eval env ((Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val]))[i]'hi)
      from (CircuitType.eval_var_fields env _).symm]
  exact (getElem_eval_vector (α := fields 32) env
    (Vector.ofFn fun j => constWord32 (p := circomPrime) (Specs.SHA256.H0[j.val])) i hi).symm

/-- `eval env state0` equals `Specs.SHA256.H0` (as values), where `state0` is the H0 const state. -/
lemma state0_value (env : Environment (F circomPrime)) :
    Vector.map valueBits
      (eval env (Vector.ofFn fun i => constWord32 (p := circomPrime) (Specs.SHA256.H0[i.val]))) = Specs.SHA256.H0 := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map, state0_getElem env i hi, Vector.getElem_ofFn]
  exact valueBits_constWord32_of_lt env (H0_lt i hi)

/-- Each word of `eval env state0` is normalized. -/
lemma state0_normalized (env : Environment (F circomPrime)) (i : ℕ) (hi : i < 8) :
    Normalized ((eval env (Vector.ofFn fun i => constWord32 (p := circomPrime) (Specs.SHA256.H0[i.val])))[i]'hi) := by
  rw [state0_getElem env i hi, Vector.getElem_ofFn]
  exact normalized_constWord32 env _

/-! ## Padded-block bridging (paddedBlock ↦ specBlock) -/

/-- The byte index for block `b`, word `w`, byte-in-word `k`. -/
lemma paddedBytes_idx_lt {b w k : ℕ} (hb : b < 5) (hw : w < 16) (hk : k < 4) :
    b * 64 + 4 * w + k < paddedBytesLen := by
  simp only [paddedBytesLen, paddedBlocksLen]; omega

lemma getElem_index_eq {α : Type*} {n : ℕ} (v : Vector α n) (i j : ℕ)
    (hi : i < n) (hj : j < n) (h : i = j) : v[i]'hi = v[j]'hj := by
  subst h; rfl

/-- Word `w` of block `b` of `paddedBlock` is the same word vector as `paddedWord` at byte `b*64+4w+k`,
for any `k < 4`. -/
lemma paddedBlock_word_eq (padded : Var SHA256PaddedBits (F circomPrime))
    (b : Fin paddedBlocksLen) (w : Fin 16) {k : ℕ} (hk : k < 4) :
    (paddedBlock padded b)[w] =
      paddedWord padded ⟨b.val * 64 + 4 * w.val + k, paddedBytes_idx_lt b.isLt w.isLt hk⟩ := by
  rw [paddedBlock, Fin.getElem_fin, Vector.getElem_ofFn]
  apply Vector.ext
  intro bit hbit
  rw [Vector.getElem_ofFn, paddedBit, paddedWord, Vector.getElem_ofFn]
  apply getElem_index_eq
  have hw : w.val < 16 := w.isLt
  have h1 : (b.val * 64 + 4 * w.val + k) / 64 = b.val := by omega
  have h2 : (b.val * 64 + 4 * w.val + k) % 64 = 4 * w.val + k := by omega
  have h3 : (4 * w.val + k) / 4 = w.val := by omega
  rw [h1, h2, h3]; ring

/-- Byte `k` of word `w` of block `b` of the evaluated padded bits is the spec padded byte,
given CheckPad's per-byte spec equation. -/
lemma wordByteVal_block (env : Environment (F circomPrime))
    (padded : Var SHA256PaddedBits (F circomPrime)) (msg : Vector ℕ inputBufferLen) (ℓ : ℕ)
    (h_bytes : ∀ j : Fin paddedBytesLen,
      paddedByteVal (Vector.map (Expression.eval env) padded) j = specPaddedByte msg ℓ j.val)
    (b : Fin paddedBlocksLen) (w : Fin 16) (k : Fin 4) :
    wordByteVal (Vector.map (Expression.eval env) ((paddedBlock padded b)[w])) k
      = specPaddedByte msg ℓ (b.val * 64 + 4 * w.val + k.val) := by
  have hjlt : b.val * 64 + 4 * w.val + k.val < paddedBytesLen :=
    paddedBytes_idx_lt b.isLt w.isLt k.isLt
  rw [paddedBlock_word_eq padded b w k.isLt]
  have hk4 : (b.val * 64 + 4 * w.val + k.val) % 4 = k.val := by have := k.isLt; omega
  have hbyte := wordByteVal_paddedWord env padded
    ⟨b.val * 64 + 4 * w.val + k.val, hjlt⟩
  rw [h_bytes ⟨b.val * 64 + 4 * w.val + k.val, hjlt⟩] at hbyte
  convert hbyte using 2
  exact Fin.ext hk4.symm

/-- The evaluated `paddedBlock b` matches `specBlock`. -/
lemma paddedBlock_value (env : Environment (F circomPrime))
    (padded : Var SHA256PaddedBits (F circomPrime)) (msg : Vector ℕ inputBufferLen) (ℓ : ℕ)
    (h_bytes : ∀ j : Fin paddedBytesLen,
      paddedByteVal (Vector.map (Expression.eval env) padded) j = specPaddedByte msg ℓ j.val)
    (b : Fin paddedBlocksLen) :
    Vector.map valueBits (eval env (paddedBlock padded b)) = specBlock msg ℓ b.val := by
  apply Vector.ext
  intro w hw
  rw [Vector.getElem_map,
    ← getElem_eval_vector (α := fields 32) env (paddedBlock padded b) w hw,
    CircuitType.eval_var_fields]
  rw [valueBits_eq_bytesToWord32BE]
  rw [specBlock, Specs.SHA256.bytesToBlock, Vector.getElem_mapFinRange]
  have e0 := wordByteVal_block env padded msg ℓ h_bytes b ⟨w, hw⟩ 0
  have e1 := wordByteVal_block env padded msg ℓ h_bytes b ⟨w, hw⟩ 1
  have e2 := wordByteVal_block env padded msg ℓ h_bytes b ⟨w, hw⟩ 2
  have e3 := wordByteVal_block env padded msg ℓ h_bytes b ⟨w, hw⟩ 3
  simp only [Fin.isValue, Fin.getElem_fin] at e0 e1 e2 e3
  rw [show ((paddedBlock padded b)[w]'hw) = (paddedBlock padded b)[(⟨w, hw⟩ : Fin 16)] from rfl] at *
  rw [e0, e1, e2, e3, Vector.getElem_ofFn, Vector.getElem_ofFn, Vector.getElem_ofFn,
    Vector.getElem_ofFn]
  congr 1

/-- Each word of an evaluated `paddedBlock` is normalized, given booleanity of the padded bits. -/
lemma paddedBlock_normalized (env : Environment (F circomPrime))
    (padded : Var SHA256PaddedBits (F circomPrime))
    (h_bool : ∀ i : Fin paddedBitsLen, IsBool (Vector.map (Expression.eval env) padded)[i])
    (b : Fin paddedBlocksLen) (w : ℕ) (hw : w < 16) :
    Normalized (eval env ((paddedBlock padded b)[w]'hw)) := by
  intro bit
  rw [CircuitType.eval_var_fields]
  -- (paddedBlock padded b)[w][bit] = padded[b*512 + w*32 + bit]
  have hidx : b.val * 16 * 32 + w * 32 + bit.val < paddedBitsLen := by
    have hb : b.val < 5 := b.isLt
    have := bit.isLt
    simp only [paddedBitsLen, paddedBlocksLen]; omega
  have hget : (Vector.map (Expression.eval env) ((paddedBlock padded b)[w]'hw))[bit] =
      (Vector.map (Expression.eval env) padded)[b.val * 16 * 32 + w * 32 + bit.val]'hidx := by
    rw [paddedBlock, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_ofFn,
      paddedBit, Vector.getElem_map]
  rw [hget]
  have := h_bool ⟨b.val * 16 * 32 + w * 32 + bit.val, hidx⟩
  simp only [IsBool] at this
  exact this

lemma paddedBlock_varFromOffset_eval_eq_of_agreesBelow
    {env env' : ProverEnvironment (F circomPrime)} {offset k : ℕ}
    (h_agree : env.AgreesBelow k env') (hbound : offset + paddedBitsLen ≤ k)
    (b : Fin paddedBlocksLen) :
    eval env.toEnvironment
        (paddedBlock (varFromOffset (F := F circomPrime) (fields paddedBitsLen) offset) b) =
      eval env'.toEnvironment
        (paddedBlock (varFromOffset (F := F circomPrime) (fields paddedBitsLen) offset) b) := by
  apply Vector.ext
  intro w hw
  rw [← getElem_eval_vector (α := fields 32) env.toEnvironment
      (paddedBlock (varFromOffset (F := F circomPrime) (fields paddedBitsLen) offset) b) w hw,
    ← getElem_eval_vector (α := fields 32) env'.toEnvironment
      (paddedBlock (varFromOffset (F := F circomPrime) (fields paddedBitsLen) offset) b) w hw]
  apply Vector.ext
  intro bit hbit
  rw [← ProvableType.getElem_eval_fields env.toEnvironment
      ((paddedBlock (varFromOffset (F := F circomPrime) (fields paddedBitsLen) offset) b)[w]'hw) bit hbit,
    ← ProvableType.getElem_eval_fields env'.toEnvironment
      ((paddedBlock (varFromOffset (F := F circomPrime) (fields paddedBitsLen) offset) b)[w]'hw) bit hbit]
  have hidx : b.val * 16 * 32 + w * 32 + bit < paddedBitsLen := by
    have hb : b.val < 5 := b.isLt
    have hw' : w < 16 := hw
    have hbit' : bit < 32 := hbit
    simp only [paddedBitsLen, paddedBlocksLen]
    omega
  have hbit_eq :
      (((paddedBlock (varFromOffset (F := F circomPrime) (fields paddedBitsLen) offset) b)[w]'hw)[bit]'hbit) =
        (varFromOffset (F := F circomPrime) (fields paddedBitsLen) offset :
          fields paddedBitsLen (Expression (F circomPrime))).get
          ⟨b.val * 16 * 32 + w * 32 + bit, hidx⟩ := by
    unfold paddedBlock paddedBit
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
    rfl
  rw [hbit_eq, ProvableType.varFromOffset_fields]
  have hget :
      (Vector.mapRange paddedBitsLen (fun i =>
          (var { index := offset + i } : Expression (F circomPrime)))
        ).get ⟨b.val * 16 * 32 + w * 32 + bit, hidx⟩ =
        (var { index := offset + (b.val * 16 * 32 + w * 32 + bit) } :
          Expression (F circomPrime)) := by
    exact
      (Vector.getElem_mapRange
        (create := fun i => (var { index := offset + i } : Expression (F circomPrime)))
        (b.val * 16 * 32 + w * 32 + bit) hidx)
  rw [hget]
  change env.get (offset + (b.val * 16 * 32 + w * 32 + bit)) =
    env'.get (offset + (b.val * 16 * 32 + w * 32 + bit))
  exact h_agree _ (by omega)

/-- Final digest-selection step: if each candidate state's value equals the chain state,
the selected digest word matches the SHA-256 spec output. -/
lemma digest_final
    (states : Vector (SHA256State (F circomPrime)) paddedBlocksLen)
    (msg : Vector ℕ inputBufferLen) (ℓ : ℕ) (hℓ : ℓ ≤ inputBufferLen)
    (hsv : ∀ k : Fin paddedBlocksLen, Vector.map valueBits states[k] = chainState msg ℓ (k.val + 1))
    (w : Fin 8) (hw : w.val < 8) :
    valueBits ((stateForLen states ℓ)[w.val]'hw) =
      (Specs.SHA256.sha256 (Specs.SHA256.truncate msg ℓ hℓ))[w.val]'hw := by
  have hpos := numBlocksForLen_pos ℓ
  have hle := numBlocksForLen_le hℓ
  simp only [paddedBlocksLen] at hle
  rw [stateForLen_eq states ℓ hℓ]
  rw [sha256_eq_chainState msg ℓ hℓ]
  -- numBlocksForLen ℓ - 1 corresponds to index k with k+1 = numBlocksForLen ℓ
  set nb := numBlocksForLen ℓ with hnb
  have hk : nb - 1 < paddedBlocksLen := by simp only [paddedBlocksLen]; omega
  have := hsv ⟨nb - 1, hk⟩
  have hkv : (⟨nb - 1, hk⟩ : Fin paddedBlocksLen).val + 1 = nb := by simp only; omega
  rw [hkv] at this
  rw [← this, Vector.getElem_map]
  congr 2

/-- The output of a `subcircuit` call is the child circuit's own output.
Definitional, but 4.32's `simp` no longer unfolds `subcircuit` on its own, so the
top-level `computableWitness` proof rewrites with this instead. -/
theorem subcircuit_output_eq {β α : TypeMap} [ProvableType β] [ProvableType α]
    (c : FormalCircuit (F circomPrime) β α) (b : Var β (F circomPrime)) (n : ℕ) :
    (subcircuit c b).output n = c.output b n := rfl

end Solution.SHA256
