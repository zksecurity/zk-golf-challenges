import Solution.Bls12381G1ScalarMul.Theorems
import Solution.Bls12381G1ScalarMul.WitgenBigNat
import Challenge.Utils.WitgenIR

/-!
# The gadgets' side of the digit library

`WitgenBigNat` knows about digit lists and limb windows; this file connects that
vocabulary to the one the circuits are written in (`BigInt.value`, `BigInt.Normalized`,
`Var (fields n)`), so that a gadget's witness program can be stated over its own inputs
and its bridge lemma read back in the gadget's own terms.

Three things live here:

* `bigVal`, the ℕ a limb vector denotes *as the digit reader sees it* (each limb
  truncated to `B` bits), with `bigVal_eq_value` turning it into `BigInt.value` on the
  normalized limbs every gadget's `Assumptions` provide;
* `digitsOf` / `evalsBig_digitsOf`, the step-free reader for a limb vector, and
  `limbsOut`'s specialization to the gadget's output shape;
* `toIR_eq`, the projection lemma every `witnessVectorProgram` bridge starts from. It is
  stated for a *variable* program so `rfl` closes it by structure eta, without ever
  forcing a long chain at `whnf` (see `DivOrZero`, where the chain is 256 squarings).
-/

namespace Solution.Bls12381G1ScalarMul
namespace IRLimbs

open Solution.Bls12381G1ScalarMul.Limbs
open Witgen WitgenNat WitgenBigNat

variable {p : ℕ} [Fact p.Prime]

/-! ## The value a limb vector denotes -/

/-- The ℕ a limb vector denotes, each limb truncated to `B` bits. Unconditional, which
is what lets every bridge below be stated without a normalization hypothesis. -/
def bigVal (B : ℕ) {n : ℕ} (x : Var (fields n) (F p)) (env : ProverEnvironment (F p)) : ℕ :=
  limbsVal B (limbVals x.toList env)

theorem limbVals_toList {n : ℕ} (x : Var (fields n) (F p)) (env : ProverEnvironment (F p)) :
    limbVals x.toList env = (x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val := by
  rw [limbVals, Vector.toList_map, List.map_map]
  rfl

/-- On normalized limbs the truncating reader is the circuit's own `BigInt.value`. -/
theorem bigVal_eq_value {n : ℕ} (B : ℕ) (x : Var (fields n) (F p))
    (env : ProverEnvironment (F p))
    (h : BigInt.Normalized B (x.map (Expression.eval env.toEnvironment))) :
    bigVal B x env = BigInt.value B (x.map (Expression.eval env.toEnvironment)) := by
  rw [bigVal, limbVals_toList, BigInt.value, Limbs.fromLimbs]
  refine limbsVal_eq_foldr B _ fun w hw => ?_
  rw [List.mem_map] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  rw [Vector.mem_toList_iff, Vector.mem_iff_getElem] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  exact h ⟨i, hi⟩

/-- `bigVal` reads the limb vector only through the evaluation of its limbs. -/
theorem bigVal_congr {n : ℕ} (B : ℕ) (x : Var (fields n) (F p))
    {env env' : ProverEnvironment (F p)}
    (h : ∀ (j : ℕ) (hj : j < n),
      Expression.eval env.toEnvironment x[j] = Expression.eval env'.toEnvironment x[j]) :
    bigVal B x env = bigVal B x env' := by
  have : limbVals x.toList env = limbVals x.toList env' := by
    rw [limbVals, limbVals]
    refine List.ext_getElem (by simp) fun j hj hj' => ?_
    simp only [List.getElem_map, Vector.getElem_toList]
    rw [h j (by simpa using hj')]
  rw [bigVal, bigVal, this]

/-! ## Reading a limb vector into digits -/

/-- The `len` low digits of the value a limb vector denotes. No steps. -/
def digitsOf (B : ℕ) {n : ℕ} (x : Var (fields n) (F p)) (len : ℕ) : List (U64Expr (F p)) :=
  limbsDigits B x.toList len

@[simp] theorem length_digitsOf (B : ℕ) {n : ℕ} (x : Var (fields n) (F p)) (len : ℕ) :
    (digitsOf B x len).length = len := length_limbsDigits _ _ _

theorem evalsBig_digitsOf {S : Array (Step (F p))} {B : ℕ} (hB : 0 < B) {n : ℕ}
    (x : Var (fields n) (F p)) (len : ℕ) :
    EvalsBig S (digitsOf B x len) (fun env => ofNat (bigVal B x env) len) :=
  evalsBig_limbsDigits hB _ len

/-- The reader is exact once the register is wide enough for the value. -/
theorem lval_digitsOf_eq {B : ℕ} {n : ℕ} (x : Var (fields n) (F p))
    {len : ℕ} (env : ProverEnvironment (F p)) (h : bigVal B x env < base ^ len) :
    lval (ofNat (bigVal B x env) len) = bigVal B x env := lval_ofNat_of_lt h

/-- `n` limbs of `B` bits, with a fixed-length register: every gadget's output. -/
theorem bigVal_lt {B : ℕ} {n : ℕ} (x : Var (fields n) (F p)) (env : ProverEnvironment (F p)) :
    bigVal B x env < 2 ^ (B * n) := by
  have h := limbsVal_lt B (limbVals x.toList env)
  rwa [limbVals, List.length_map, Vector.length_toList] at h

/-! ## Running prefix sums of a coefficient sequence

Two gadgets (`EqViaCarries`, `LessThan`) witness a *running carry*: a quotient of the
partial value through the loop index. The partial value is a prefix sum, so the program
accumulates it in one fixed-width register, re-reading the register at each index with
the free `shiftDigits` window.

`prefN` is the register's own arithmetic, truncations and all, so it is a total function
of the coefficient values. That is what makes the `computableWitnesses` bridge trivial:
two environments agreeing on the input limbs give the same `prefN`, whether or not the
coefficients are in range. `prefN_eq` is the reading under the gadget's `Assumptions`,
where the register is wide enough and nothing is truncated.
-/

/-! ## Prefix sums of a coefficient sequence -/

/-- The accumulator's value after `k` steps: the mirror of `prefixP`, with every
truncation the register performs spelled out, so it is a total function of the
coefficient values. -/
def prefN (B nbits PL : ℕ) (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (prefN B nbits PL v k + v k % 2 ^ nbits * 2 ^ (B * k)) % base ^ PL

theorem prefN_lt (B nbits PL : ℕ) (v : ℕ → ℕ) (k : ℕ) : prefN B nbits PL v k < base ^ PL := by
  cases k with
  | zero => exact Nat.pow_pos base_pos
  | succ k => exact Nat.mod_lt _ (Nat.pow_pos base_pos)

/-- The running prefix sum `Σ_{j<k} (v j mod 2^nbits) · 2^(B·j)`, accumulated into a
`PL`-digit register. -/
def prefixP (B nbits PL : ℕ) (x : List (Expression (F p))) :
    ℕ → M (F p) (List (U64Expr (F p)))
  | 0 => Pure.pure (constDigits 0 PL)
  | k + 1 => do
      let acc ← prefixP B nbits PL x k
      let s ← addP acc (readBitsAt (x.getD k (Expression.const 0)) (B * k) nbits) (uc 0)
      Pure.pure (resizeDigits s PL)

/-- The coefficient values a prefix program reads. -/
def coeffVals (x : List (Expression (F p))) (env : ProverEnvironment (F p)) (j : ℕ) : ℕ :=
  (Expression.eval env.toEnvironment (x.getD j (Expression.const 0))).val

theorem coeffVals_toList {n : ℕ} (x : Var (fields n) (F p)) (env : ProverEnvironment (F p))
    (j : ℕ) :
    coeffVals x.toList env j
      = if h : j < n then (Expression.eval env.toEnvironment (x[j]'h)).val else 0 := by
  rw [coeffVals]
  split
  · rename_i h
    rw [getD_of_lt _ (by simpa using h)]
    simp only [Vector.getElem_toList]
  · rename_i h
    rw [getD_of_ge _ (by simpa using Nat.le_of_not_lt h)]
    simp [Expression.eval]

theorem computesBig_prefixP (B nbits PL : ℕ) (x : List (Expression (F p))) :
    ∀ (k : ℕ) {S : Array (Step (F p))},
      ComputesBig S (prefixP B nbits PL x k)
        (fun env => ofNat (prefN B nbits PL (coeffVals x env) k) PL) := by
  intro k
  induction k with
  | zero =>
    intro S
    exact Computes.pure ((evalsBig_constDigits 0 PL).congr fun env => rfl)
  | succ k ih =>
    intro S
    refine Computes.bind ih ?_
    intro S1 acc _ hacc
    have hterm : EvalsBig S1 (readBitsAt (x.getD k (Expression.const 0)) (B * k) nbits)
        (fun env => ofNat (coeffVals x env k % 2 ^ nbits * 2 ^ (B * k))
          (numChunks (B * k + nbits))) := by
      refine (evalsBig_readBitsAt_F _ _ _).congr fun env => ?_
      rfl
    refine Computes.bind (computesBig_addP acc _ (uc 0) hacc hterm
      (EvalsU.uc 0 (by norm_num)) (fun _ => base_pos)) ?_
    intro S2 s _ hs
    refine Computes.pure ((evalsBig_resizeDigits hs PL).congr fun env => ?_)
    have hlen : (coeffVals x env k % 2 ^ nbits * 2 ^ (B * k))
        < base ^ numChunks (B * k + nbits) := by
      have h1 : coeffVals x env k % 2 ^ nbits < 2 ^ nbits := Nat.mod_lt _ (Nat.two_pow_pos _)
      have h2 : coeffVals x env k % 2 ^ nbits * 2 ^ (B * k) < 2 ^ nbits * 2 ^ (B * k) :=
        Nat.mul_lt_mul_of_lt_of_le h1 (le_refl _) (Nat.two_pow_pos _)
      have h3 : (2 : ℕ) ^ nbits * 2 ^ (B * k) = 2 ^ (B * k + nbits) := by
        rw [← pow_add]; congr 1; omega
      have h4 : (2 : ℕ) ^ (B * k + nbits) ≤ base ^ numChunks (B * k + nbits) := by
        rw [base_pow]
        exact Nat.pow_le_pow_right (by norm_num) (le_numChunks _)
      omega
    rw [lval_addc, lval_ofNat_of_lt (prefN_lt B nbits PL _ k), lval_ofNat_of_lt hlen,
      Nat.add_zero, prefN, ofNat_mod]

/-! ## Reading the mirror back as the intended carry -/

/-- A prefix sum of `nbits`-wide coefficients, bounded. -/
theorem sum_coeff_lt (B nbits n : ℕ) (v : ℕ → ℕ) (hv : ∀ j, j < n → v j < 2 ^ nbits)
    (k : ℕ) (hk : k ≤ n) :
    (∑ j ∈ Finset.range k, v j * 2 ^ (B * j)) < 2 ^ (nbits + B * n + n) := by
  have hstep : ∀ j ∈ Finset.range k, v j * 2 ^ (B * j) ≤ (2 ^ nbits - 1) * 2 ^ (B * n) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : v j ≤ 2 ^ nbits - 1 := by have := hv j (by omega); omega
    exact Nat.mul_le_mul h1 (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left B (by omega)))
  calc (∑ j ∈ Finset.range k, v j * 2 ^ (B * j))
      ≤ ∑ _j ∈ Finset.range k, (2 ^ nbits - 1) * 2 ^ (B * n) := Finset.sum_le_sum hstep
    _ = k * ((2 ^ nbits - 1) * 2 ^ (B * n)) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ n * ((2 ^ nbits - 1) * 2 ^ (B * n)) := Nat.mul_le_mul_right _ hk
    _ < 2 ^ n * (2 ^ nbits * 2 ^ (B * n)) :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.lt_two_pow_self)
          (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (by positivity)
    _ = 2 ^ (nbits + B * n + n) := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- With the coefficients in range and the register wide enough, the mirror is the plain
prefix sum. -/
theorem prefN_eq (B nbits PL n : ℕ) (v : ℕ → ℕ) (hv : ∀ j, j < n → v j < 2 ^ nbits)
    (hPL : 2 ^ (nbits + B * n + n) ≤ base ^ PL) :
    ∀ k, k ≤ n → prefN B nbits PL v k = ∑ j ∈ Finset.range k, v j * 2 ^ (B * j) := by
  intro k
  induction k with
  | zero => intro _; simp [prefN]
  | succ k ih =>
    intro hk
    have hvk : v k < 2 ^ nbits := hv k (by omega)
    rw [prefN, ih (by omega), Nat.mod_eq_of_lt hvk, ← Finset.sum_range_succ]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (sum_coeff_lt B nbits n v hv (k + 1) hk) hPL)

/-- The register arithmetic behind one carry: an offset sum, a wrapping subtraction and
one final window, on operands the offset dominates. -/
theorem carry_mod_eq {OFF QP QS CL CB : ℕ} (hP : QP ≤ OFF) (hS : QS ≤ OFF)
    (hCB : 2 * OFF < 2 ^ CB) (hCL : 2 ^ CB ≤ base ^ CL) :
    ((OFF % base ^ CL + QP % base ^ CL) % base ^ CL + base ^ CL - QS % base ^ CL)
        % base ^ CL % 2 ^ CB
      = OFF + QP - QS := by
  have hOFFlt : OFF < base ^ CL := by omega
  have hQPlt : QP < base ^ CL := by omega
  have hQSlt : QS < base ^ CL := by omega
  have hsum : OFF + QP < base ^ CL := by omega
  have hres : OFF + QP - QS < base ^ CL := by omega
  have hres2 : OFF + QP - QS < 2 ^ CB := by omega
  rw [Nat.mod_eq_of_lt hOFFlt, Nat.mod_eq_of_lt hQPlt, Nat.mod_eq_of_lt hQSlt,
    Nat.mod_eq_of_lt hsum,
    show OFF + QP + base ^ CL - QS = base ^ CL + (OFF + QP - QS) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt hres, Nat.mod_eq_of_lt hres2]

/-! ## The `witnessVectorProgram` bridge -/

omit [Fact p.Prime] in
/-- `Witgen.M.toIR` spelled out with projections. Stated for a *variable* program so
that `rfl` closes it by structure eta, without ever running the program at `whnf` —
which is exactly the shape `circuit_norm` leaves the `witnessVectorProgram`
obligations in. -/
theorem toIR_eq {n : ℕ} (prog : Witgen.M (F p) (Witgen.VExpr (F p) n)) :
    prog.toIR = Witgen.WitgenIR.ir (prog #[]).2.toList (prog #[]).1 := rfl

/-- `witnessVectorProgram` is a `witnessIR` site, spelled out so that the
`computableWitnesses` rewrite finds it. -/
theorem witnessVectorProgram_eq_witnessIR {n : ℕ}
    (prog : Witgen.M (F p) (Witgen.VExpr (F p) n)) :
    witnessVectorProgram n prog = witnessIR (fields n) prog.toIR := rfl

/-- The value a `witnessVectorProgram` site witnesses, from the program's
`ComputesV` fact. -/
theorem eval_program {n : ℕ} {prog : Witgen.M (F p) (Witgen.VExpr (F p) n)}
    {val : ProverEnvironment (F p) → Vector (F p) n}
    (h : ComputesV #[] prog val) (env : ProverEnvironment (F p)) :
    Witgen.VExpr.eval { env := env, locals := Witgen.evalSteps env (prog #[]).2.toList }
        (prog #[]).1
      = val env := by
  have h' := ComputesV.toIR h env
  rwa [toIR_eq, Witgen.WitgenIR.eval] at h'

/-- Congruence for a vector `witnessVectorProgram` site, in the `toIR` spelling the
`computableWitnesses` obligation uses: the program reads the environment only through
the value it was specified to compute. -/
theorem eval_toIR_congr {n : ℕ} {prog : Witgen.M (F p) (Witgen.VExpr (F p) n)} {val}
    (h : ComputesV #[] prog val) {env env' : ProverEnvironment (F p)}
    (hv : val env = val env') :
    prog.toIR.eval env = prog.toIR.eval env' := by
  rw [toIR_eq, Witgen.WitgenIR.eval]
  show Witgen.VExpr.eval { env := env, locals := _ } _
    = Witgen.VExpr.eval { env := env', locals := _ } _
  rw [eval_program h env, eval_program h env', hv]

/-- `Witgen.M.toIR` is an `.ir` program by construction, for any program. Stated for a
*variable* program so the proof never reduces a concrete one. -/
theorem isIR_toIR {n : ℕ} (prog : Witgen.M (F p) (Witgen.VExpr (F p) n)) :
    Challenge.WitgenIR.IsIR prog.toIR := trivial

/-- `isIR_toIR` through a named abbreviation of the IR. Takes the defining equation
rather than unfolding, so the check stays first-order: unifying `IsIR ?x` against a
concrete program's `toIR` would otherwise send the elaborator into the program. -/
theorem isIR_of_eq_toIR {n : ℕ} {ir : Witgen.WitgenIR (F p) n}
    {prog : Witgen.M (F p) (Witgen.VExpr (F p) n)} (h : ir = prog.toIR) :
    Challenge.WitgenIR.IsIR ir := h ▸ isIR_toIR prog

/-- `ComputesV.toIR` through a named abbreviation of the IR. -/
theorem eval_ir_of_eq_toIR {n : ℕ} {ir : Witgen.WitgenIR (F p) n}
    {prog : Witgen.M (F p) (Witgen.VExpr (F p) n)} {val} (h : ir = prog.toIR)
    (hp : ComputesV #[] prog val) (env : ProverEnvironment (F p)) :
    ir.eval env = val env := by rw [h]; exact ComputesV.toIR hp env

/-! ## Scalar witness sites

A gadget whose scalar witness (a quotient bit, a borrow) needs shared `let`-steps is a
`witnessProgram` at the `field` provable type, which is the same single-cell operation
`witnessField` was, with an IR program in place of a bare expression.
-/

theorem eval_programF {prog : Witgen.M (F p) (Witgen.FExpr (F p))} {val}
    (h : ComputesF #[] prog val) (env : ProverEnvironment (F p)) :
    Witgen.FExpr.eval
        { env := env, locals := Witgen.evalSteps env (prog #[]).2.toList } (prog #[]).1
      = val env := h.2.eval env

theorem eval_toIRLiteralF {prog : Witgen.M (F p) (Witgen.FExpr (F p))} {val}
    (h : ComputesF #[] prog val) (env : ProverEnvironment (F p)) :
    (Witgen.M.toIRLiteral (value := field) prog).eval env = #v[val env] := by
  rw [Witgen.M.eval_toIRLiteral]
  simp only [Witgen.M.eval, circuit_norm]
  rw [eval_programF h env]
  rfl

/-- Congruence for a scalar `witnessProgram` site, in the `toIRLiteral` spelling the
`computableWitnesses` obligation uses. -/
theorem eval_toIRLiteralF_congr {prog : Witgen.M (F p) (Witgen.FExpr (F p))} {val}
    (h : ComputesF #[] prog val) {env env' : ProverEnvironment (F p)}
    (hv : val env = val env') :
    (Witgen.M.toIRLiteral (value := field) prog).eval env
      = (Witgen.M.toIRLiteral (value := field) prog).eval env' := by
  rw [eval_toIRLiteralF h env, eval_toIRLiteralF h env', hv]

/-- A scalar `witnessProgram` is a `witnessIR` site, spelled out so that the
`computableWitnesses` rewrite finds it. -/
theorem witnessProgramF_eq_witnessIR (prog : Witgen.M (F p) (Witgen.FExpr (F p))) :
    witnessProgram (F := F p) (value := field) (var := Expression) prog
      = witnessIR field prog.toIRLiteral := rfl

end IRLimbs
end Solution.Bls12381G1ScalarMul
