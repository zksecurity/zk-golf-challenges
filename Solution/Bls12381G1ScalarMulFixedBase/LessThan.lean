import Solution.Bls12381G1ScalarMulFixedBase.Normalize
import Solution.Bls12381G1ScalarMulFixedBase.Equal
import Solution.Bls12381G1ScalarMulFixedBase.WitgenLimbs
import Challenge.Utils.ComputableWitnessLemmas

/-!
# RSA big-integer comparison (gadget G2)

This file defines `LessThan` (gadget **G2**): a `FormalAssertion` over a
pair of *normalized* big integers `(lhs, rhs)` asserting `lhs.value B < rhs.value B`.

## Strategy (borrow / carry chain)

We witness a `BigInt m` value `d` that should equal `rhs − 1 − lhs`, range-check it
to be normalized, and then certify the big-integer identity

```
lhs + d + 1 = rhs
```

limb-wise with a per-limb carry recurrence and a forced-zero top carry. Together
with `d` being normalized this yields `lhs ≤ rhs − 1 < rhs`, i.e.
`lhs.value B < rhs.value B`.

The "`+ 1`" is folded into the constant term of limb `0` so that every per-limb
constraint stays a degree-≤1 (linear) `assertZero`.

Soundness and completeness are fully proved.
-/

namespace Solution.Bls12381G1ScalarMulFixedBase
open Solution.Bls12381G1ScalarMulFixedBase.Limbs

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-! ## G2 — `LessThan` -/

namespace LessThan

/-- Inputs of `LessThan`: `lhs` and `rhs`, asserting `lhs.value < rhs.value`. -/
structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

/-- Natural-number value of a witnessed limb vector under a prover environment,
little-endian base `2^B`. Used only inside witness generators. -/
private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Solution.Bls12381G1ScalarMulFixedBase.Limbs.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

/-! ## Witness programs

Both witnesses are big-integer computations, so both live in the digit layer.

* `d = b − 1 − a`: the u64 sort has no subtraction, so the borrow chain of `subP` does
  the work and one reduction modulo the register width absorbs the borrow out. No
  digit-wise complement, and no field round trip.
* the carry out of limb `k` of `a + d + 1` is a window of the prefix sum through `k`;
  the program accumulates that prefix in one register (`IRLimbs.prefixP`, with the `+1`
  riding in as the addition's carry-in, so it is free) and reads the carry out with
  `shiftDigits`.

`dN` and `cN` are the registers' own arithmetic, truncations included, hence total
functions of the operands' limb values: the `computableWitnesses` bridges need no side
condition. The conditional readings (`getElem_eval_dWitness_of`,
`getElem_eval_cWitness`) take the normalization the gadget's `Assumptions` already
provide.
-/

section Generator
open Witgen WitgenNat WitgenBigNat IRLimbs

/-- Digits of the register `d = b − 1 − a` is computed in. -/
def subLen (m B : ℕ) : ℕ := numChunks (B * m + 1)

/-- The register arithmetic of `b − 1 − a`, truncations included. -/
def dN (L va vb : ℕ) : ℕ :=
  (vb % base ^ L + base ^ L - (va % base ^ L + 1 % base ^ L) % base ^ L) % base ^ L

/-- Witness program for the `m` limbs of `d = b − 1 − a`. The u64 sort has no
subtraction, so the borrow chain of `subP` does the work and one reduction modulo the
register width absorbs the borrow out. -/
def dProg (B L : ℕ) (a b : Var (BigInt m) (F p)) : M (F p) (VExpr (F p) m) := do
  let s ← addP (digitsOf B a L) (constDigits 1 L) (uc 0)
  let d ← subP (digitsOf B b L) (resizeDigits s L) (uc 0)
  Pure.pure (limbsOut d.1 B m)

omit [NeZero m] in
theorem computesV_dProg {B : ℕ} (hB : 0 < B) (L : ℕ) (a b : Var (BigInt m) (F p)) :
    ComputesV #[] (dProg B L a b)
      (fun env => Vector.ofFn fun j : Fin m =>
        ((dN L (bigVal B a env) (bigVal B b env) / 2 ^ (B * j.val) % 2 ^ B : ℕ) : F p)) := by
  refine Computes.bind (computesBig_addP _ _ (uc 0) (evalsBig_digitsOf hB a L)
    (evalsBig_constDigits 1 L) (EvalsU.uc 0 (by norm_num)) (fun _ => base_pos)) ?_
  intro S1 s hS1 hs
  have hsr : EvalsBig S1 (resizeDigits s L)
      (fun env => ofNat ((bigVal B a env % base ^ L + 1 % base ^ L) % base ^ L) L) :=
    (evalsBig_resizeDigits hs L).congr fun env => by
      rw [lval_addc, lval_ofNat, lval_ofNat, Nat.add_zero, ofNat_mod]
  refine Computes.bind (computesBigU_subP _ _ (uc 0) ((evalsBig_digitsOf hB b L).mono hS1) hsr
    (EvalsU.uc 0 (by norm_num)) (fun _ => by norm_num)) ?_
  intro S2 d hS2 hd
  have hd1 : EvalsBig S2 d.1 (fun env => subb (ofNat (bigVal B b env) L)
      (ofNat ((bigVal B a env % base ^ L + 1 % base ^ L) % base ^ L) L) 0) := hd.1
  refine Computes.pure ((evalsV_limbsOut hd1 B m).congr fun env => ?_)
  refine Vector.ext fun j hj => ?_
  simp only [Vector.getElem_ofFn]
  rw [lval_subb_mod (bounded_ofNat _ _) (bounded_ofNat _ _) (by simp), length_ofNat,
    lval_ofNat, lval_ofNat_of_lt (Nat.mod_lt _ (Nat.pow_pos base_pos)), dN]

omit [NeZero m] in
/-- Unconditional bridge for `dProg`, over the register's own arithmetic. -/
theorem getElem_eval_dProg {B : ℕ} (hB : 0 < B) (L : ℕ) (a b : Var (BigInt m) (F p))
    (env : ProverEnvironment (F p)) (k : ℕ) (hk : k < m) :
    (Witgen.VExpr.eval
        { env := env, locals := Witgen.evalSteps env (dProg B L a b #[]).2.toList }
        (dProg B L a b #[]).1)[k]
      = ((dN L (bigVal B a env) (bigVal B b env) / 2 ^ (B * k) % 2 ^ B : ℕ) : F p) := by
  rw [IRLimbs.eval_program (computesV_dProg hB L a b) env]
  simp only [Vector.getElem_ofFn]

omit [NeZero m] in
/-- `dProg` reads the operands only through their evaluated limbs. -/
theorem eval_toIR_dProg_congr {B : ℕ} (hB : 0 < B) (L : ℕ) (a b : Var (BigInt m) (F p))
    {env env' : ProverEnvironment (F p)}
    (ha : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (a[j]'hj)
      = Expression.eval env'.toEnvironment (a[j]'hj))
    (hb : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (b[j]'hj)
      = Expression.eval env'.toEnvironment (b[j]'hj)) :
    (dProg B L a b).toIR.eval env = (dProg B L a b).toIR.eval env' := by
  rw [IRLimbs.toIR_eq, Witgen.WitgenIR.eval]
  show Witgen.VExpr.eval { env := env, locals := _ } _
    = Witgen.VExpr.eval { env := env', locals := _ } _
  rw [IRLimbs.eval_program (computesV_dProg hB L a b) env,
    IRLimbs.eval_program (computesV_dProg hB L a b) env',
    bigVal_congr B a ha, bigVal_congr B b hb]

omit [NeZero m] in
/-- The register arithmetic is the intended difference once the operands are in range. -/
theorem dN_eq {L va vb : ℕ} (hlt : va < vb) (hvb : vb < base ^ L) :
    dN L va vb = vb - 1 - va := by
  have hb1 : 1 < base ^ L := by omega
  have hone : (1 : ℕ) % base ^ L = 1 := Nat.mod_eq_of_lt hb1
  rw [dN, hone, Nat.mod_eq_of_lt (by omega : va < base ^ L),
    Nat.mod_eq_of_lt (by omega : vb < base ^ L),
    Nat.mod_eq_of_lt (by omega : va + 1 < base ^ L),
    show vb + base ^ L - (va + 1) = base ^ L + (vb - 1 - va) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-! ## The carry chain of `a + d + 1` -/

/-- The register arithmetic of one carry bit, truncations included. -/
def cN (B nbits PL CL CB : ℕ) (vA vD : ℕ → ℕ) (k : ℕ) : ℕ :=
  (prefN B nbits PL vA (k + 1) + prefN B nbits PL vD (k + 1) + 1) % base ^ PL
    / 2 ^ (B * (k + 1)) % base ^ CL % 2 ^ CB

/-- The carry bits out of limbs `k, k+1, …, k+n-1` of `a + d + 1`. The `+1` rides in as
the carry-in of the prefix addition, so it costs nothing. -/
def cL (B nbits PL CL CB : ℕ) (a d : List (Expression (F p))) :
    ℕ → ℕ → M (F p) (List (FExpr (F p)))
  | 0, _ => Pure.pure []
  | n + 1, k => do
      let aA ← prefixP B nbits PL a (k + 1)
      let aD ← prefixP B nbits PL d (k + 1)
      let t ← addP aA aD (uc 1)
      let rest ← cL B nbits PL CL CB a d n (k + 1)
      Pure.pure (limbF (shiftDigits (resizeDigits t PL) (B * (k + 1)) CL) 0 CB :: rest)

omit [NeZero m] in
theorem computesFL_cL (B nbits PL CL CB : ℕ) (a d : List (Expression (F p))) :
    ∀ (n k : ℕ) {S : Array (Step (F p))},
      ComputesFL S (cL B nbits PL CL CB a d n k)
        (fun env j => if j < n then
          ((cN B nbits PL CL CB (coeffVals a env) (coeffVals d env) (k + j) : ℕ) : F p) else 0) := by
  intro n
  induction n with
  | zero => intro k S; exact Computes.pure (EvalsFL.nil (by simp))
  | succ n ih =>
    intro k S
    refine Computes.bind (computesBig_prefixP B nbits PL a (k + 1)) ?_
    intro S1 aA _ haA
    refine Computes.bind (computesBig_prefixP B nbits PL d (k + 1)) ?_
    intro S2 aD hS2 haD
    refine Computes.bind (computesBig_addP _ _ (uc 1) (haA.mono hS2) haD
      (EvalsU.uc 1 (by norm_num)) (fun _ => by rw [base_eq]; norm_num)) ?_
    intro S3 t hS3 ht
    have hw : EvalsBig S3 (shiftDigits (resizeDigits t PL) (B * (k + 1)) CL)
        (fun env => ofNat ((prefN B nbits PL (coeffVals a env) (k + 1)
            + prefN B nbits PL (coeffVals d env) (k + 1) + 1) % base ^ PL
          / 2 ^ (B * (k + 1))) CL) :=
      (evalsBig_shiftDigits (evalsBig_resizeDigits ht PL) (B * (k + 1)) CL).congr fun env => by
        rw [lval_ofNat, lval_addc, lval_ofNat_of_lt (prefN_lt B nbits PL _ (k + 1)),
          lval_ofNat_of_lt (prefN_lt B nbits PL _ (k + 1))]
    refine Computes.bind (ih (k + 1)) ?_
    intro S4 rest hS4 hrest
    refine Computes.pure (EvalsFL.cons ?_ (hrest.congr fun env j => ?_))
    · refine (evalsF_limbF (hw.mono hS4) 0 CB).congr fun env => ?_
      rw [if_pos (by omega), pow_zero, Nat.div_one, cN, lval_ofNat]
    · by_cases hj : j < n
      · rw [if_pos hj, if_pos (by omega), show k + 1 + j = k + (j + 1) by omega]
      · rw [if_neg hj, if_neg (by omega)]

/-- The whole carry vector as a witness program. -/
def cProg (B nbits PL CL CB n : ℕ) (a d : List (Expression (F p))) :
    M (F p) (VExpr (F p) n) := do
  let outs ← cL B nbits PL CL CB a d n 0
  Pure.pure (.lit (Vector.ofFn fun k : Fin n => outs.getD k.val (.const 0)))

omit [NeZero m] in
theorem computesV_cProg (B nbits PL CL CB n : ℕ) (a d : List (Expression (F p))) :
    ComputesV #[] (cProg B nbits PL CL CB n a d)
      (fun env => Vector.ofFn fun k : Fin n =>
        ((cN B nbits PL CL CB (coeffVals a env) (coeffVals d env) k.val : ℕ) : F p)) := by
  refine Computes.bind (computesFL_cL B nbits PL CL CB a d n 0) ?_
  intro S outs _ houts
  refine Computes.pure ((EvalsV.ofFL houts).congr fun env => ?_)
  refine Vector.ext fun k hk => ?_
  simp only [Vector.getElem_ofFn, if_pos hk, Nat.zero_add]

omit [NeZero m] in
/-- The register arithmetic is the intended running carry once the limbs are in range. -/
theorem cN_eq (B nbits PL CL CB n : ℕ) (vA vD : ℕ → ℕ)
    (hA : ∀ j, j < n → vA j < 2 ^ nbits) (hD : ∀ j, j < n → vD j < 2 ^ nbits)
    (hPL : 2 ^ (nbits + B * n + n + 1) ≤ base ^ PL)
    (hCL : 1 < base ^ CL) (hCB : 1 < 2 ^ CB)
    (k : ℕ) (hk : k + 1 ≤ n)
    (hle : (1 + ∑ j ∈ Finset.range (k + 1), (vA j + vD j) * 2 ^ (B * j))
      / 2 ^ (B * (k + 1)) ≤ 1) :
    cN B nbits PL CL CB vA vD k
      = (1 + ∑ j ∈ Finset.range (k + 1), (vA j + vD j) * 2 ^ (B * j)) / 2 ^ (B * (k + 1)) := by
  have hPL' : 2 ^ (nbits + B * n + n) ≤ base ^ PL :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hPL
  have hA' := sum_coeff_lt B nbits n vA hA (k + 1) hk
  have hD' := sum_coeff_lt B nbits n vD hD (k + 1) hk
  have hdouble : (2 : ℕ) * 2 ^ (nbits + B * n + n) = 2 ^ (nbits + B * n + n + 1) := by
    rw [← pow_succ']
  have hsplit : (∑ j ∈ Finset.range (k + 1), (vA j + vD j) * 2 ^ (B * j))
      = (∑ j ∈ Finset.range (k + 1), vA j * 2 ^ (B * j))
        + ∑ j ∈ Finset.range (k + 1), vD j * 2 ^ (B * j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hkey : (∑ j ∈ Finset.range (k + 1), vA j * 2 ^ (B * j)
        + ∑ j ∈ Finset.range (k + 1), vD j * 2 ^ (B * j) + 1) % base ^ PL
      = 1 + ∑ j ∈ Finset.range (k + 1), (vA j + vD j) * 2 ^ (B * j) := by
    rw [hsplit, Nat.mod_eq_of_lt (by omega)]
    omega
  have hQ : (1 + ∑ j ∈ Finset.range (k + 1), (vA j + vD j) * 2 ^ (B * j))
      / 2 ^ (B * (k + 1)) < base ^ CL := by omega
  have hQ2 : (1 + ∑ j ∈ Finset.range (k + 1), (vA j + vD j) * 2 ^ (B * j))
      / 2 ^ (B * (k + 1)) < 2 ^ CB := by omega
  rw [cN, prefN_eq B nbits PL n vA hA hPL' _ hk, prefN_eq B nbits PL n vD hD hPL' _ hk,
    hkey, Nat.mod_eq_of_lt hQ, Nat.mod_eq_of_lt hQ2]


omit [NeZero m] in
theorem getElem_eval_cProg (B nbits PL CL CB n : ℕ) (a d : List (Expression (F p)))
    (env : ProverEnvironment (F p)) (k : ℕ) (hk : k < n) :
    (Witgen.VExpr.eval
        { env := env,
          locals := Witgen.evalSteps env (cProg B nbits PL CL CB n a d #[]).2.toList }
        (cProg B nbits PL CL CB n a d #[]).1)[k]
      = ((cN B nbits PL CL CB (coeffVals a env) (coeffVals d env) k : ℕ) : F p) := by
  rw [IRLimbs.eval_program (computesV_cProg B nbits PL CL CB n a d) env]
  simp only [Vector.getElem_ofFn]

omit [NeZero m] in
/-- `cProg` reads the operands only through their evaluated limbs. -/
theorem eval_toIR_cProg_congr (B nbits PL CL CB n : ℕ) (a d : List (Expression (F p)))
    {env env' : ProverEnvironment (F p)}
    (ha : coeffVals a env = coeffVals a env') (hd : coeffVals d env = coeffVals d env') :
    (cProg B nbits PL CL CB n a d).toIR.eval env
      = (cProg B nbits PL CL CB n a d).toIR.eval env' := by
  rw [IRLimbs.toIR_eq, Witgen.WitgenIR.eval]
  show Witgen.VExpr.eval { env := env, locals := _ } _
    = Witgen.VExpr.eval { env := env', locals := _ } _
  rw [IRLimbs.eval_program (computesV_cProg B nbits PL CL CB n a d) env,
    IRLimbs.eval_program (computesV_cProg B nbits PL CL CB n a d) env', ha, hd]

/-! ## The two witness programs of `main` -/

/-- The `d` witness program. -/
def dWitness (P : BigIntParams p m) (a b : Var (BigInt m) (F p)) : M (F p) (VExpr (F p) m) :=
  dProg P.B (subLen m P.B) a b

/-- Digits of the carry-chain prefix register. -/
def cPrefLen (m B : ℕ) : ℕ := numChunks (B + B * m + m + 1)

/-- The carry witness program. -/
def cWitness (P : BigIntParams p m) (a d : Var (BigInt m) (F p)) : M (F p) (VExpr (F p) m) :=
  cProg P.B P.B (cPrefLen m P.B) 1 2 m a.toList d.toList

omit [NeZero m] in
/-- Bridge for `dWitness` in the branch that matters: on normalized limbs with
`a.value < b.value`, the witnessed limb is a limb of `b.value − 1 − a.value`. -/
theorem getElem_eval_dWitness_of (P : BigIntParams p m) (a b : Var (BigInt m) (F p))
    (env : ProverEnvironment (F p))
    (hanorm : ∀ j : Fin m, (Expression.eval env.toEnvironment (a[j.val]'j.isLt)).val < 2 ^ P.B)
    (hbnorm : ∀ j : Fin m, (Expression.eval env.toEnvironment (b[j.val]'j.isLt)).val < 2 ^ P.B)
    (hlt : evalValue P.B env a < evalValue P.B env b)
    (k : ℕ) (hk : k < m) :
    (Witgen.VExpr.eval
        { env := env, locals := Witgen.evalSteps env (dWitness P a b #[]).2.toList }
        (dWitness P a b #[]).1)[k]
      = (((evalValue P.B env b - 1 - evalValue P.B env a) / 2 ^ (P.B * k) % 2 ^ P.B : ℕ)
          : F p) := by
  have hna : BigInt.Normalized P.B (a.map (Expression.eval env.toEnvironment)) := fun j => by
    simpa using hanorm j
  have hnb : BigInt.Normalized P.B (b.map (Expression.eval env.toEnvironment)) := fun j => by
    simpa using hbnorm j
  have hva : bigVal P.B a env = evalValue P.B env a := bigVal_eq_value P.B a env hna
  have hvb : bigVal P.B b env = evalValue P.B env b := bigVal_eq_value P.B b env hnb
  have hblt : evalValue P.B env b < base ^ subLen m P.B := by
    have h1 : evalValue P.B env b < 2 ^ (P.B * m) := BigInt.value_lt hnb
    have h2 : (2 : ℕ) ^ (P.B * m + 1) ≤ base ^ subLen m P.B :=
      by rw [subLen]; exact two_pow_le_base_numChunks _
    have h3 : (2 : ℕ) ^ (P.B * m) ≤ 2 ^ (P.B * m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold dWitness
  rw [getElem_eval_dProg (by have := P.hB1; omega) _ a b env k hk, hva, hvb,
    dN_eq hlt hblt]

omit [NeZero m] in
/-- Bridge for `cWitness`: on normalized `a` and `d` whose carry really is a bit, the
witnessed cell is the running carry of `a + d + 1` out of limb `k`. -/
theorem getElem_eval_cWitness (P : BigIntParams p m) (a d : Var (BigInt m) (F p))
    (env : ProverEnvironment (F p)) (k : ℕ) (hk : k < m)
    (hA : ∀ (j : ℕ) (hj : j < m),
      (Expression.eval env.toEnvironment (a[j]'hj)).val < 2 ^ P.B)
    (hD : ∀ (j : ℕ) (hj : j < m),
      (Expression.eval env.toEnvironment (d[j]'hj)).val < 2 ^ P.B)
    (hle : (1 + ∑ j ∈ Finset.range (k + 1),
        ((if h : j < m then (Expression.eval env.toEnvironment (a[j]'h)).val else 0)
          + (if h : j < m then (Expression.eval env.toEnvironment (d[j]'h)).val else 0))
        * 2 ^ (P.B * j)) / 2 ^ (P.B * (k + 1)) ≤ 1) :
    (Witgen.VExpr.eval
        { env := env, locals := Witgen.evalSteps env (cWitness P a d #[]).2.toList }
        (cWitness P a d #[]).1)[k]
      = (((1 + ∑ j ∈ Finset.range (k + 1),
            ((if h : j < m then (Expression.eval env.toEnvironment (a[j]'h)).val else 0)
              + (if h : j < m then (Expression.eval env.toEnvironment (d[j]'h)).val else 0))
            * 2 ^ (P.B * j)) / 2 ^ (P.B * (k + 1)) : ℕ) : F p) := by
  have hcA : ∀ j, j < m → coeffVals a.toList env j < 2 ^ P.B := fun j hj => by
    rw [coeffVals_toList, dif_pos hj]; exact hA j hj
  have hcD : ∀ j, j < m → coeffVals d.toList env j < 2 ^ P.B := fun j hj => by
    rw [coeffVals_toList, dif_pos hj]; exact hD j hj
  have hsum : ∀ (x : Var (BigInt m) (F p)) (j : ℕ), coeffVals x.toList env j
      = if h : j < m then (Expression.eval env.toEnvironment (x[j]'h)).val else 0 :=
    fun x j => coeffVals_toList x env j
  unfold cWitness
  rw [getElem_eval_cProg _ _ _ _ _ _ _ _ env k hk,
    cN_eq P.B P.B (cPrefLen m P.B) 1 2 m _ _ hcA hcD
      (by rw [cPrefLen]; exact two_pow_le_base_numChunks _)
      (by rw [pow_one, base_eq]; norm_num) (by norm_num) k (by omega)
      (by simpa only [hsum] using hle)]
  simp only [hsum]


omit [NeZero m] in
/-- `dWitness` reads the operands only through their evaluated limbs. -/
theorem eval_toIR_dWitness_congr (P : BigIntParams p m) (a b : Var (BigInt m) (F p))
    {env env' : ProverEnvironment (F p)}
    (ha : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (a[j]'hj)
      = Expression.eval env'.toEnvironment (a[j]'hj))
    (hb : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (b[j]'hj)
      = Expression.eval env'.toEnvironment (b[j]'hj)) :
    (dWitness P a b).toIR.eval env = (dWitness P a b).toIR.eval env' :=
  eval_toIR_dProg_congr (by have := P.hB1; omega) _ a b ha hb

omit [NeZero m] in
/-- `cWitness` reads the operands only through their evaluated limbs. -/
theorem eval_toIR_cWitness_congr (P : BigIntParams p m) (a d : Var (BigInt m) (F p))
    {env env' : ProverEnvironment (F p)}
    (ha : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (a[j]'hj)
      = Expression.eval env'.toEnvironment (a[j]'hj))
    (hd : ∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (d[j]'hj)
      = Expression.eval env'.toEnvironment (d[j]'hj)) :
    (cWitness P a d).toIR.eval env = (cWitness P a d).toIR.eval env' := by
  have hcv : ∀ (x : Var (BigInt m) (F p)),
      (∀ (j : ℕ) (hj : j < m), Expression.eval env.toEnvironment (x[j]'hj)
        = Expression.eval env'.toEnvironment (x[j]'hj)) →
      coeffVals x.toList env = coeffVals x.toList env' := by
    intro x hx
    funext j
    rw [coeffVals_toList, coeffVals_toList]
    split
    · rename_i h; rw [hx j h]
    · rfl
  exact eval_toIR_cProg_congr _ _ _ _ _ _ _ _ (hcv a ha) (hcv d hd)


end Generator

/-- The `main` circuit of `LessThan`: assert two normalized big integers satisfy
`lhs.value B < rhs.value B`.

We witness `d = rhs − 1 − lhs` (its limbs), range-check `d` to be normalized,
witness one carry bit per limb, and assert the limb-wise identity
`lhs + d + 1 = rhs` with the top carry forced to `0`. -/
def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let a := input.lhs
  let b := input.rhs

  -- 1. witness the limbs of `d = b − 1 − a`
  let d ← witnessVectorProgram m (dWitness P a b)

  -- 2. range-check `d` to be normalized (subcircuit call)
  Normalize.circuit P d

  -- 3. witness one carry (borrow) bit per limb. The carry *out* of limb `k`
  -- for the base-`2^B` addition `a + d + 1` is the running carry, which can be
  -- read off as `⌊P_k / 2^(B·(k+1))⌋` where `P_k = 1 + Σ_{j≤k} (a[j]+d[j])·2^(B·j)`
  -- is the partial sum through limb `k`.
  let carry ← witnessVectorProgram m (cWitness P a d)

  -- boolean-constrain each carry bit
  Circuit.forEach carry (fun c => assertZero (c * (c - 1)))

  -- 4. per-limb recurrence `a[k] + d[k] + carry_in + [k=0] = b[k] + carry[k]·2^B`
  -- where `carry_in = carry[k-1]` (0 for `k = 0`), and the `+1` is folded into
  -- limb 0's constant term. We build the per-limb constraint expressions purely,
  -- then assert each is zero.
  let constraints : Vector (Expression (F p)) m := Vector.mapFinRange m fun k =>
    let carryIn : Expression (F p) :=
      if h : k.val = 0 then 0 else carry[k.val - 1]'(by omega)
    let one : Expression (F p) := if k.val = 0 then 1 else 0
    a[k.val] + d[k.val] + carryIn + one - b[k.val] - carry[k.val] * (2 ^ P.B : F p)
  Circuit.forEach constraints assertZero

  -- 5. force the top carry to zero
  if h : m = 0 then pure () else
    assertZero (carry[m - 1]'(by omega))

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P) where
  -- d : m witnesses; Normalize : m*B; carry bits : m
  localLength _ := m + m * P.B + m
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
      Gadgets.ToBits.rangeCheck]
    split <;> simp +arith [circuit_norm]

omit [NeZero m] in
/-- Per-field projection of an `eval`-agreement hypothesis on the `Inputs` struct.
The `Var Inputs` `match` no longer iota-reduces on a struct *variable*, so the
destructuring has to happen here, once. -/
lemma eval_inputs_getElem {input : Var (Inputs m) (F p)} {env env' : ProverEnvironment (F p)}
    (h : eval env input = eval env' input) :
    (∀ x, (hx : x < m) → Expression.eval env.toEnvironment (input.lhs[x]'hx)
        = Expression.eval env'.toEnvironment (input.lhs[x]'hx)) ∧
    (∀ x, (hx : x < m) → Expression.eval env.toEnvironment (input.rhs[x]'hx)
        = Expression.eval env'.toEnvironment (input.rhs[x]'hx)) := by
  obtain ⟨lhs, rhs⟩ := input
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq] at h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hx' := congrArg (fun v : Vector (F p) m => v[x]'hx) h.1
    simp only [Vector.getElem_map] at hx'
    exact hx'
  · have hx' := congrArg (fun v : Vector (F p) m => v[x]'hx) h.2
    simp only [Vector.getElem_map] at hx'
    exact hx'

omit [NeZero m] in
/-- Struct-level `eval` of the `lhs` field, projected at one index. Lean 4.33 keeps
the two forms apart in the goal, so the bridge has to be stated explicitly. -/
lemma getElem_eval_lhs {input : Var (Inputs m) (F p)} {env : Environment (F p)}
    (x : ℕ) (hx : x < m) :
    ((ProvableStruct.eval env input : Inputs m (F p)).lhs[x]'hx)
      = Expression.eval env (input.lhs[x]'hx) := by
  obtain ⟨lhs, rhs⟩ := input
  simp [circuit_norm, explicit_provable_type]

/-- Preconditions: both big integers are normalized. -/
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B

/-- Postcondition: `lhs.value B < rhs.value B`. -/
def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B < input.rhs.value B

/-- The `LessThan` formal assertion (gadget **G2**): two normalized big integers
satisfy `lhs.value B < rhs.value B`. -/
def circuit (P : BigIntParams p m) [Fact (p > 2)] :
    FormalAssertion (F p) (Inputs m) where
    main := main P
    requirementsChannelsLawful := by
      intro input offset
      simp only [main, circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
        Gadgets.ToBits.rangeCheck]
      split <;> simp +arith [circuit_norm]
    Assumptions := Assumptions P.B
    Spec := Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
        Gadgets.ToBits.rangeCheck] at h_holds ⊢
      obtain ⟨h_dnorm, h_cbool, h_lin, h_top⟩ := h_holds
      obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
      refine ⟨?_, by split <;> simp [circuit_norm]⟩
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- m = 0 is excluded by `[NeZero m]` (the gadget is only meaningful, and only
        -- sound, for at least one limb).
        exact absurd hm (NeZero.ne m)
      -- m ≥ 1: borrow/carry chain argument.
      -- Nat-indexed digit/carry functions.
      set An : ℕ → ℕ := fun k => if h : k < m then (input_lhs[k]'h).val else 0 with hAn
      set Dn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hDn
      set Bn : ℕ → ℕ := fun k => if h : k < m then (input_rhs[k]'h).val else 0 with hBn
      set Cn : ℕ → ℕ := fun k => (env.get (i₀ + m + m * B + k)).val with hCn
      -- digit bounds
      have hAn_lt : ∀ k, k < m → An k < 2 ^ B := by
        intro k hk; simp only [hAn, dif_pos hk]; exact ha_norm ⟨k, hk⟩
      have hBn_lt : ∀ k, k < m → Bn k < 2 ^ B := by
        intro k hk; simp only [hBn, dif_pos hk]; exact hb_norm ⟨k, hk⟩
      have hDn_lt : ∀ k, k < m → Dn k < 2 ^ B := by
        intro k hk
        have hspec := h_dnorm trivial ⟨k, hk⟩
        have heq : (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i => var { index := i₀ + i }))[(⟨k, hk⟩ : Fin m)]
            = env.get (i₀ + k) := by simp [circuit_norm]
        rw [heq] at hspec
        simpa [hDn] using hspec
      -- carry bits
      have hCn_le : ∀ k, k < m → Cn k ≤ 1 := by
        intro k hk
        have hb := h_cbool ⟨k, hk⟩
        have : IsBool (env.get (i₀ + m + m * B + k)) := by
          rw [IsBool.iff_mul_sub_one]; exact hb
        have := IsBool.val_lt_two this
        simp only [hCn]; omega
      -- 2^(B+1) < p
      have hPB1 : 2 ^ (B + 1) < p := by
        have h1 : 2 ^ (B + 1) ≤ 2 ^ (2 * B + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ (2 * B + 2) = 2 ^ (2 * B) * 4 := by rw [pow_add]; ring
        have h3 : 2 ^ (2 * B) * 4 ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
          have : 1 ≤ m + 1 := by omega
          nlinarith [Nat.two_pow_pos (2 * B)]
        omega
      -- per-limb nat equation: An k + Dn k + cin k + one k = Bn k + Cn k * 2^B
      have h_limb : ∀ k : ℕ, (hk : k < m) →
          An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)
            = Bn k + Cn k * 2 ^ B := by
        intro k hk
        have hlin := h_lin ⟨k, hk⟩
        -- evaluate the three "eval" subterms
        have ha_e : Expression.eval env input_var_lhs[(⟨k, hk⟩ : Fin m).val] = input_lhs[k]'hk := by
          rw [← h_input.1]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env input_var_rhs[(⟨k, hk⟩ : Fin m).val] = input_rhs[k]'hk := by
          rw [← h_input.2]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env
            (if h : (⟨k, hk⟩ : Fin m).val = 0 then 0
              else var { index := i₀ + m + m * B + ((⟨k, hk⟩ : Fin m).val - 1) })
            = if k = 0 then 0 else env.get (i₀ + m + m * B + (k - 1)) := by
          simp only []
          split <;> simp [circuit_norm]
        have hone_e : Expression.eval env (if (⟨k, hk⟩ : Fin m).val = 0 then 1 else 0)
            = if k = 0 then (1 : F p) else 0 := by
          simp only []; split <;> simp [circuit_norm]
        simp only [ha_e, hb_e, hcin_e, hone_e] at hlin
        -- bounds for the lift lemma
        have h3 : (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val ≤ 1 := by
          split
          · simp [ZMod.val_zero]
          · rename_i h
            have hkm : k - 1 < m := by omega
            have := hCn_le (k - 1) hkm
            simp only [hCn] at this; exact this
        have h4 : (if k = 0 then (1 : F p) else 0).val ≤ 1 := by
          split
          · simp [ZMod.val_one]
          · simp [ZMod.val_zero]
        have hpw : 2 ^ B + 2 ^ B = 2 ^ (B + 1) := by rw [pow_succ]; ring
        have hsum_lt : (input_lhs[k]'hk).val + (env.get (i₀ + k)).val
            + (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val
            + (if k = 0 then (1 : F p) else 0).val < p := by
          have h1 := hAn_lt k hk; have h2 := hDn_lt k hk
          simp only [hAn, hDn, dif_pos hk] at h1 h2
          omega
        have hrhs_lt : (input_rhs[k]'hk).val
            + (env.get (i₀ + m + m * B + k)).val * 2 ^ B < p := by
          have h1 := hBn_lt k hk; have h2 := hCn_le k hk
          simp only [hBn, hCn, dif_pos hk] at h1 h2
          nlinarith [Nat.two_pow_pos B]
        have hlin' : (input_lhs[k]'hk) + env.get (i₀ + k)
            + (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1)))
            + (if k = 0 then (1 : F p) else 0) - (input_rhs[k]'hk)
            - env.get (i₀ + m + m * B + k) * (2 ^ B : F p) = 0 := by
          exact hlin
        have hlift := per_limb_lift (B := B) (input_lhs[k]'hk) (env.get (i₀ + k))
          (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1)))
          (if k = 0 then (1 : F p) else 0) (input_rhs[k]'hk)
          (env.get (i₀ + m + m * B + k)) hB hsum_lt hrhs_lt hlin'
        -- rewrite the `.val`s of the carry/one terms
        have hcin_val : (if k = 0 then (0:F p) else env.get (i₀ + m + m * B + (k - 1))).val
            = if k = 0 then 0 else Cn (k - 1) := by
          split <;> simp [hCn]
        have hone_val : (if k = 0 then (1 : F p) else 0).val = if k = 0 then 1 else 0 := by
          split
          · simp [ZMod.val_one]
          · simp [ZMod.val_zero]
        rw [hcin_val, hone_val] at hlift
        simp only [hAn, hDn, hBn, hCn, dif_pos hk]
        omega
      -- top carry is zero
      have htop0 : Cn (m - 1) = 0 := by
        have hne : ¬ (m = 0) := by omega
        simp only [dif_neg hne, circuit_norm] at h_top
        simp only [hCn, h_top, ZMod.val_zero]
      -- value as range sums of the digit functions
      have hval_a : BigInt.value B input_lhs = ∑ k ∈ Finset.range m, An k * 2 ^ (B * k) := by
        rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => An k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
      have hval_b : BigInt.value B input_rhs = ∑ k ∈ Finset.range m, Bn k * 2 ^ (B * k) := by
        rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => Bn k * 2 ^ (B * k))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
      -- sum the per-limb equations over range m
      have hsum_eq : (∑ k ∈ Finset.range m,
            ((An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)) * 2 ^ (B * k)))
          = ∑ k ∈ Finset.range m, ((Bn k + Cn k * 2 ^ B) * 2 ^ (B * k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [h_limb k hk]
      -- distribute LHS
      have hLHS : (∑ k ∈ Finset.range m,
            (An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)) * 2 ^ (B * k))
          = (∑ k ∈ Finset.range m, An k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, Dn k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, (if k = 0 then 0 else Cn (k - 1)) * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, (if k = 0 then 1 else 0) * 2 ^ (B * k)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring
      have hRHS : (∑ k ∈ Finset.range m, (Bn k + Cn k * 2 ^ B) * 2 ^ (B * k))
          = (∑ k ∈ Finset.range m, Bn k * 2 ^ (B * k))
            + (∑ k ∈ Finset.range m, Cn k * 2 ^ (B * (k + 1))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_add, Nat.mul_one, pow_add]; ring
      -- the "one" sum equals 1 (only k=0 contributes)
      have hone_sum : (∑ k ∈ Finset.range m, (if k = 0 then 1 else 0) * 2 ^ (B * k)) = 1 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro k _ hk0; simp [hk0]
        · intro h; exact absurd (Finset.mem_range.mpr hm) h
      -- carry telescoping
      have htel := carry_telescope B Cn m
      rw [if_neg (by omega : ¬ (m = 0)), htop0, Nat.zero_mul, Nat.add_zero] at htel
      -- combine
      rw [hLHS, hRHS, hone_sum, htel] at hsum_eq
      -- now hsum_eq : value_a-sum + value_d-sum + carry-sum + 1 = value_b-sum + carry-sum
      rw [hval_a, hval_b]
      -- value_d-sum ≥ 0, cancel the carry sums
      have hd_nonneg : 0 ≤ ∑ k ∈ Finset.range m, Dn k * 2 ^ (B * k) := Nat.zero_le _
      omega
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start
      simp only [circuit_norm, Normalize.circuit, Normalize.elaborated, Normalize.main,
        Gadgets.ToBits.rangeCheck] at h_env ⊢
      obtain ⟨h_dwit, h_cwit, _, _⟩ := h_env
      obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
      -- nat-indexed digit functions
      set An : ℕ → ℕ := fun k => if h : k < m then (input_lhs[k]'h).val else 0 with hAn
      set Bn : ℕ → ℕ := fun k => if h : k < m then (input_rhs[k]'h).val else 0 with hBn
      -- evalValue equals the denotation of the inputs
      have heva : evalValue B env input_var_lhs = BigInt.value B input_lhs := by
        rw [evalValue, BigInt.value, ← h_input.1]
      have hevb : evalValue B env input_var_rhs = BigInt.value B input_rhs := by
        rw [evalValue, BigInt.value, ← h_input.2]
      -- side conditions of the `dIR` bridge: `lhs` is normalized and `lhs < rhs < 2^(B*m)`
      have hanorm : ∀ j : Fin m,
          (Expression.eval env.toEnvironment (input_var_lhs[j.val]'j.isLt)).val < 2 ^ B := by
        intro j
        rw [show Expression.eval env.toEnvironment (input_var_lhs[j.val]'j.isLt)
              = input_lhs[j.val]'j.isLt from by rw [← h_input.1]; simp [Vector.getElem_map]]
        exact ha_norm j
      have hlt' : evalValue B env input_var_lhs < evalValue B env input_var_rhs := by
        rw [heva, hevb]; exact h_spec
      have hbnorm : ∀ j : Fin m,
          (Expression.eval env.toEnvironment (input_var_rhs[j.val]'j.isLt)).val < 2 ^ B := by
        intro j
        rw [show Expression.eval env.toEnvironment (input_var_rhs[j.val]'j.isLt)
              = input_rhs[j.val]'j.isLt from by rw [← h_input.2]; simp [Vector.getElem_map]]
        exact hb_norm j
      -- the witnessed d-limb value at index i
      have hd_val : ∀ i : Fin m, (env.get (i₀ + i.val)).val
          = (evalValue B env input_var_rhs - 1 - evalValue B env input_var_lhs)
              / 2 ^ (B * i.val) % 2 ^ B := by
        intro i
        have hget := h_dwit i
        rw [getElem_eval_dWitness_of ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ _ _ env
            hanorm hbnorm hlt' i.val i.isLt] at hget
        rw [hget, ZMod.val_natCast_of_lt]
        exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB)
      -- abbreviations for the two denotations
      set va := BigInt.value B input_lhs with hva
      set vb := BigInt.value B input_rhs with hvb
      -- the witnessed d value (as a natural number, before per-limb split)
      set dtot : ℕ := vb - 1 - va with hdtot
      -- bounds: va, vb < 2^(B*m)
      have hva_lt : va < 2 ^ (B * m) := BigInt.value_lt ha_norm
      have hvb_lt : vb < 2 ^ (B * m) := BigInt.value_lt hb_norm
      -- d limb value
      have hd_val' : ∀ i : Fin m, (env.get (i₀ + i.val)).val = dtot / 2 ^ (B * i.val) % 2 ^ B := by
        intro i; rw [hd_val i, heva, hevb]
      -- nat-indexed d digits
      set Dn : ℕ → ℕ := fun k => if h : k < m then (env.get (i₀ + k)).val else 0 with hDn
      have hDn_eq : ∀ k, k < m → Dn k = dtot / 2 ^ (B * k) % 2 ^ B := by
        intro k hk; simp only [hDn, dif_pos hk]; exact hd_val' ⟨k, hk⟩
      have hDn_lt : ∀ k, k < m → Dn k < 2 ^ B := by
        intro k hk; rw [hDn_eq k hk]; exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_refl _)
      have hAn_lt : ∀ k, k < m → An k < 2 ^ B := fun k hk => by
        simp only [hAn, dif_pos hk]; exact ha_norm ⟨k, hk⟩
      have hBn_lt : ∀ k, k < m → Bn k < 2 ^ B := fun k hk => by
        simp only [hBn, dif_pos hk]; exact hb_norm ⟨k, hk⟩
      -- digit sum function and partial sums
      set gfun : ℕ → ℕ := fun k => An k + Dn k with hgfun
      have hgfun_le : ∀ j, gfun j ≤ 2 * (2 ^ B - 1) := by
        intro j
        rcases Nat.lt_or_ge j m with hj | hj
        · have := hAn_lt j hj; have := hDn_lt j hj; simp only [hgfun]; omega
        · simp only [hgfun, hAn, hDn, dif_neg (by omega : ¬ j < m)]; omega
      set P : ℕ → ℕ := fun k => 1 + ∑ j ∈ Finset.range (k + 1), gfun j * 2 ^ (B * j) with hP
      -- dtot < 2^(B*m), value of d, and the additive identity
      have hdtot_lt : dtot < 2 ^ (B * m) := by rw [hdtot]; omega
      have hadd : va + dtot + 1 = vb := by rw [hdtot]; omega
      -- value of witnessed d equals dtot
      have hvd : BigInt.value B (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange m fun i => var { index := i₀ + i })) = dtot := by
        rw [BigInt.value_eq_sum]
        have hstep : (∑ k : Fin m, ((Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun i => var { index := i₀ + i }))[k]).val * 2 ^ (B * k.val))
            = ∑ k ∈ Finset.range m, (dtot / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k) := by
          rw [← Fin.sum_univ_eq_sum_range (fun k => (dtot / 2 ^ (B * k) % 2 ^ B) * 2 ^ (B * k))]
          apply Finset.sum_congr rfl
          intro i _
          have : (Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
            simp [circuit_norm]
          rw [this, hd_val' i]
        rw [hstep, limb_decomp_mod, Nat.mod_eq_of_lt hdtot_lt]
      -- the witnessed `d` limbs are normalized: the carry bridge's side condition
      have hdnorm : ∀ (j : ℕ) (hj : j < m),
          (Expression.eval env.toEnvironment
            ((Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })[j]'hj)).val
            < 2 ^ B := by
        intro j hj
        rw [show Expression.eval env.toEnvironment
              ((Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })[j]'hj)
            = env.get (i₀ + j) from by simp [circuit_norm], hd_val' ⟨j, hj⟩]
        exact Nat.mod_lt _ (Nat.two_pow_pos B)
      -- the carry witness equals the partial-sum carry P k / 2^(B*(k+1))
      have hCn_eq : ∀ k : ℕ, k < m →
          (env.get (i₀ + m + m * B + k)).val = P k / 2 ^ (B * (k + 1)) := by
        intro k hk
        -- the raw witness expression equals P k / 2^(B*(k+1))
        have hraw : (1 + ∑ x ∈ Finset.range (k + 1),
            ((if h : x < m then (Expression.eval env.toEnvironment input_var_lhs[x]).val else 0) +
              (if h : x < m then (env.get (i₀ + x)).val else 0)) * 2 ^ (B * x)) / 2 ^ (B * (k + 1))
            = P k / 2 ^ (B * (k + 1)) := by
          congr 1
          simp only [hP]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          have hjm : j < m := by omega
          congr 1
          simp only [hgfun, hAn, hDn, dif_pos hjm]
          congr 1
          rw [← h_input.1]; simp [Vector.getElem_map]
        have hbit : P k / 2 ^ (B * (k + 1)) ≤ 1 := (ripple_carry B gfun hgfun_le k).2
        have hcw := h_cwit ⟨k, hk⟩
        rw [getElem_eval_cWitness ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ _ _ env k hk
            (fun j hj => hanorm ⟨j, hj⟩) hdnorm
            (by simp only [circuit_norm]; rw [hraw]; exact hbit)] at hcw
        simp only [circuit_norm] at hcw
        rw [hcw]
        rw [ZMod.val_natCast_of_lt, hraw]
        rw [hraw]
        have := hB; have := Nat.two_pow_pos B; omega
      -- m > 0 (else va = vb = 0, contradicting h_spec)
      have hm : 0 < m := by
        by_contra h
        have hm0 : m = 0 := by omega
        have h1 : va < 2 ^ (B * m) := hva_lt
        have h2 : vb < 2 ^ (B * m) := hvb_lt
        rw [hm0, Nat.mul_zero, pow_zero] at h1 h2
        omega
      -- An, Dn digit sums
      have hsum_an : (∑ j ∈ Finset.range m, An j * 2 ^ (B * j)) = va := by
        rw [hva, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => An j * 2 ^ (B * j))]
        apply Finset.sum_congr rfl
        intro i _; simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
      have hsum_dn : (∑ j ∈ Finset.range m, Dn j * 2 ^ (B * j)) = dtot := by
        rw [← hvd, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Dn j * 2 ^ (B * j))]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hDn, dif_pos i.isLt]
        congr 1
        have : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
          simp [circuit_norm]
        rw [this]
      -- P (m-1) = vb
      have hPlast : P (m - 1) = vb := by
        simp only [hP]
        rw [show m - 1 + 1 = m by omega]
        simp only [hgfun]
        rw [show (∑ j ∈ Finset.range m, (An j + Dn j) * 2 ^ (B * j))
            = (∑ j ∈ Finset.range m, An j * 2 ^ (B * j))
              + (∑ j ∈ Finset.range m, Dn j * 2 ^ (B * j)) by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring]
        rw [hsum_an, hsum_dn]; omega
      -- Bn k = the k-th extracted digit of vb
      have hBn_eq : ∀ k, k < m → Bn k = vb / 2 ^ (B * k) % 2 ^ B := by
        intro k hk
        have hvb_sum : vb = ∑ j ∈ Finset.range m, Bn j * 2 ^ (B * j) := by
          rw [hvb, BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Bn j * 2 ^ (B * j))]
          apply Finset.sum_congr rfl
          intro i _; simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
        rw [hvb_sum]
        exact (digit_extract B Bn (fun j => by
          rcases Nat.lt_or_ge j m with hj | hj
          · exact hBn_lt j hj
          · simp only [hBn, dif_neg (by omega : ¬ j < m)]; exact Nat.two_pow_pos B) m k hk).symm
      -- carry field value is a bit (0 or 1)
      have hCn_bit : ∀ k : ℕ, k < m → IsBool (env.get (i₀ + m + m * B + k)) := by
        intro k hk
        have hle : (env.get (i₀ + m + m * B + k)).val ≤ 1 := by
          rw [hCn_eq k hk]; exact (ripple_carry B gfun hgfun_le k).2
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · left; exact (ZMod.val_eq_zero _).mp h0
        · right
          have : env.get (i₀ + m + m * B + k) = ((1 : ℕ) : F p) := by
            rw [← h1, ZMod.natCast_zmod_val]
          simpa using this
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- 1. d is normalized (Normalize subcircuit obligation)
        refine ⟨trivial, ?_⟩
        intro i
        have : (Vector.map (Expression.eval env.toEnvironment)
            (Vector.mapRange m fun j => var { index := i₀ + j }))[i] = env.get (i₀ + i.val) := by
          simp [circuit_norm]
        rw [this]
        have := hDn_lt i.val i.isLt
        simp only [hDn, dif_pos i.isLt] at this
        exact this
      · -- 2. carry booleans
        intro i
        have hbit := hCn_bit i.val i.isLt
        exact (IsBool.iff_mul_sub_one).mp hbit
      · -- 3. per-limb field equation
        set Cn : ℕ → ℕ := fun k => (env.get (i₀ + m + m * B + k)).val with hCn
        have hCnP : ∀ k, k < m → Cn k = P k / 2 ^ (B * (k + 1)) := fun k hk => hCn_eq k hk
        -- the ℕ-level per-limb recurrence
        have hnat : ∀ k, k < m →
            An k + Dn k + (if k = 0 then 0 else Cn (k - 1)) + (if k = 0 then 1 else 0)
              = Bn k + Cn k * 2 ^ B := by
          intro k hk
          have hre : gfun k + (if k = 0 then 1 else P (k - 1) / 2 ^ (B * k))
              = (P k / 2 ^ (B * k)) % 2 ^ B + (P k / 2 ^ (B * (k + 1))) * 2 ^ B := ripple_eq B gfun k
          -- limb_stable: (P k / 2^(B*k)) % 2^B = (P (m-1) / 2^(B*k)) % 2^B = vb/2^(B*k)%2^B = Bn k
          have hlimb : (P k / 2 ^ (B * k)) % 2 ^ B = Bn k := by
            have h1 : P (m - 1) / 2 ^ (B * k) % 2 ^ B = P k / 2 ^ (B * k) % 2 ^ B :=
              limb_stable B gfun k (m - 1) (by omega)
            rw [hBn_eq k hk, ← hPlast, ← h1]
          -- carry-out and carry-in in terms of Cn
          have hco : P k / 2 ^ (B * (k + 1)) = Cn k := (hCnP k hk).symm
          rw [hlimb, hco] at hre
          simp only [hgfun] at hre
          -- handle the carry-in
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            simp only [↓reduceIte] at hre ⊢
            omega
          · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)]
            have hcin : P (k - 1) / 2 ^ (B * k) = Cn (k - 1) := by
              rw [hCnP (k - 1) (by omega), show k - 1 + 1 = k from by omega]
            rw [if_neg (by omega : ¬ k = 0), hcin] at hre
            omega
        -- cast each per-limb ℕ equation to F p
        intro i
        have hk := i.isLt
        have hnatk := hnat i.val hk
        -- evaluate the symbolic subterms
        have ha_e : Expression.eval env.toEnvironment input_var_lhs[i.val] = input_lhs[i.val]'hk := by
          rw [← h_input.1]; simp [Vector.getElem_map]
        have hb_e : Expression.eval env.toEnvironment input_var_rhs[i.val] = input_rhs[i.val]'hk := by
          rw [← h_input.2]; simp [Vector.getElem_map]
        have hcin_e : Expression.eval env.toEnvironment
            (if h : i.val = 0 then 0 else var { index := i₀ + m + m * B + (i.val - 1) })
            = if i.val = 0 then 0 else env.get (i₀ + m + m * B + (i.val - 1)) := by
          split <;> simp [circuit_norm]
        have hone_e : Expression.eval env.toEnvironment (if i.val = 0 then 1 else 0)
            = if i.val = 0 then (1 : F p) else 0 := by split <;> simp [circuit_norm]
        rw [ha_e, hb_e, hcin_e, hone_e]
        -- val-cast facts
        have hAk : ((An i.val : ℕ) : F p) = (input_lhs[i.val]'hk) := by
          simp only [hAn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hDk : ((Dn i.val : ℕ) : F p) = env.get (i₀ + i.val) := by
          simp only [hDn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hBk : ((Bn i.val : ℕ) : F p) = (input_rhs[i.val]'hk) := by
          simp only [hBn, dif_pos hk]; rw [ZMod.natCast_zmod_val]
        have hCk : ((Cn i.val : ℕ) : F p) = env.get (i₀ + m + m * B + i.val) := by
          simp only [hCn]; rw [ZMod.natCast_zmod_val]
        -- turn the goal into a cast of the ℕ equation
        have hcast_eq : (input_lhs[i.val]'hk) + env.get (i₀ + i.val)
            + (if i.val = 0 then (0:F p) else env.get (i₀ + m + m * B + (i.val - 1)))
            + (if i.val = 0 then (1 : F p) else 0)
            = (input_rhs[i.val]'hk) + env.get (i₀ + m + m * B + i.val) * (2 ^ B : F p) := by
          have hcast := congrArg (Nat.cast : ℕ → F p) hnatk
          push_cast at hcast
          rw [hAk, hDk, hBk, hCk] at hcast
          -- rewrite the conditional casts
          rw [show ((if i.val = 0 then (0:F p) else env.get (i₀ + m + m * B + (i.val - 1))))
                = ((if i.val = 0 then (0:ℕ) else Cn (i.val - 1) : ℕ) : F p) by
              split
              · simp
              · simp only [hCn]; rw [ZMod.natCast_zmod_val],
            show ((if i.val = 0 then (1:F p) else 0))
                = ((if i.val = 0 then (1:ℕ) else 0 : ℕ) : F p) by split <;> simp]
          push_cast
          convert hcast using 2
        rw [hcast_eq]; ring
      · -- 4. top carry is zero
        have hne : ¬ (m = 0) := by omega
        simp only [dif_neg hne, circuit_norm]
        -- need env.get (i₀+m+m*B+(m-1)) = 0
        have hval0 : (env.get (i₀ + m + m * B + (m - 1))).val = 0 := by
          rw [hCn_eq (m - 1) (by omega)]
          have : P (m - 1) / 2 ^ (B * (m - 1 + 1)) = vb / 2 ^ (B * m) := by
            rw [hPlast, show m - 1 + 1 = m from by omega]
          rw [this, Nat.div_eq_of_lt hvb_lt]
        exact (ZMod.val_eq_zero _).mp hval0

open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses (P : BigIntParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    IRLimbs.witnessVectorProgram_eq_witnessIR,
    Circuit.witnessIR_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    implies_true]
  refine ⟨?_, ?_, ?_, trivial, trivial, ?_⟩
  · -- witness `d`: the generator reads the input only
    intro _ h_input
    have h_in : eval env input = eval env' input := by
      simpa only [circuit_norm] using h_input
    obtain ⟨hlhs_j, hrhs_j⟩ := eval_inputs_getElem h_in
    exact eval_toIR_dWitness_congr P _ _ hlhs_j hrhs_j
  · -- Normalize subcircuit: input `d` is a previously-witnessed limb block
    refine FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (Normalize.circuit P) input _ _ ?_
      (Normalize.computableWitnesses P) env env'
    intro k e1 e2 hle h_agree _
    have hk : offset + m ≤ k := by
      simp only [circuit_norm] at hle
      omega
    have hmem := eval_mem_varFromOffset_fields_of_agreesBelow h_agree hk
    simp only [circuit_norm]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_map]
    exact hmem _ (Vector.getElem_mem hj)
  · -- witness the carry chain: generator reads the input `a` and the below-offset `d`
    intro h_agree h_input
    simp only [circuit_norm] at h_agree
    have hlhs_j := (eval_inputs_getElem h_input).1
    refine eval_toIR_cWitness_congr P _ _ hlhs_j fun j hj => ?_
    simp only [circuit_norm]
    exact h_agree (offset + j) (by omega)
  · -- top-carry assertion (or `pure ()` when `m = 0`)
    split <;> simp only [circuit_norm]

theorem computableWitness (P : BigIntParams p m) [Fact (p > 2)] : ∀ n input,
    ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F p) => eval env input) →
    Circuit.ComputableWitnesses (main P input) n := by
  exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies
    (computableWitnesses P)

/-! ## Sealing the witness programs

The programs are *data*, and big data: `circuit_norm` and any `rfl` that reaches a
circuit's `localLength` would otherwise start evaluating them, since the digit lists
are `map`s over `List.range` and the digit programs are ordinary recursions over
those. Downstream files reason through the bridges above instead.
-/

attribute [irreducible] dWitness cWitness

end LessThan

end

end Solution.Bls12381G1ScalarMulFixedBase

