import Challenge.Instances.SHA256.Interface
import Solution.SHA256.And32
import Solution.SHA256.SHA256Rounds
import Solution.SHA256.CompressBlock
import Solution.SHA256.CheckPad
import Solution.SHA256.SelectDigest
import Solution.SHA256.PaddingTheorems
import Challenge.Utils.CostR1CS

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface
open Challenge.CostR1CS

namespace Cost

instance hCircomPrimeLarge : Fact (circomPrime > 2^33) := ⟨by
  norm_num [circomPrime]⟩

/-- Each `fields 32` row of a `varFromOffset` over a `ProvableVector (fields 32) n`
is itself a `varFromOffset`, hence affine. -/
theorem affineW_varFromOffset_pvec {n : ℕ} (off j : ℕ) (hj : j < n) :
    AffineW ((varFromOffset (ProvableVector (fields 32) n) off :
      Var (ProvableVector (fields 32) n) (F circomPrime))[j]'hj) := by
  rw [varFromOffset_vector, Vector.getElem_mapRange]
  exact affineW_varFromOffset _ _

def and32Cost : Count := ⟨32, 32⟩
def xor32Cost : Count := ⟨32, 32⟩
def add32Cost : Count := ⟨33, 34⟩
def ch32Cost : Count := ⟨32, 32⟩
def maj32Cost : Count := ⟨64, 64⟩
def sigmaCost : Count := ⟨64, 64⟩

def scheduleStepCost : Count := ⟨227, 230⟩

def messageScheduleCost : Count :=
  ⟨48 * (sigmaCost.allocations + sigmaCost.allocations + 3 * add32Cost.allocations),
   48 * (sigmaCost.constraints + sigmaCost.constraints + 3 * add32Cost.constraints)⟩

def sha256RoundCost : Count :=
  ⟨2 * sigmaCost.allocations + ch32Cost.allocations + maj32Cost.allocations +
      7 * add32Cost.allocations,
   2 * sigmaCost.constraints + ch32Cost.constraints + maj32Cost.constraints +
      7 * add32Cost.constraints⟩

def sha256RoundsCost : Count :=
  ⟨64 * sha256RoundCost.allocations, 64 * sha256RoundCost.constraints⟩

def compressBlockCost : Count :=
  ⟨messageScheduleCost.allocations + sha256RoundsCost.allocations + 8 * add32Cost.allocations,
   messageScheduleCost.constraints + sha256RoundsCost.constraints + 8 * add32Cost.constraints⟩

/-! ## Per-gadget offset-independent costs (`CostIs`)

Each `costIs_*` lemma computes the exact `operationCount` of a gadget at *every*
offset, by structural recursion over the gadget's own `do`-block. Higher-level
gadgets reuse the lower ones through `CostIs.subcircuit`. The final `*Cost_proof`
theorems instantiate these at offset `0`. No `native_decide`, no `decide`. -/

theorem costIs_and32 (a b : Var (fields 32) (F circomPrime)) :
    CostIs (And32.and32 a b) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_xor32 (a b : Var (fields 32) (F circomPrime)) :
    CostIs (Xor32.xor32 a b) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_ch32 (e f g : Var (fields 32) (F circomPrime)) :
    CostIs (Ch32.ch32 e f g) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_add32 (a b : Var (fields 32) (F circomPrime)) :
    CostIs (Add32.add32 a b) ⟨33, 34⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.witnessField _) fun _ =>
      CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
        CostIs.bind (CostIs.assertZero _) fun _ =>
          CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_maj32 (a b c : Var (fields 32) (F circomPrime)) :
    CostIs (Maj32.maj32 a b c) ⟨64, 64⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun z =>
      CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
        CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_sub_xor32 (b : Var Xor32.Inputs (F circomPrime)) :
    CostIs (subcircuit Xor32.circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (costIs_xor32 _ _)

theorem costIs_lowerSigma0 (x : Var (fields 32) (F circomPrime)) :
    CostIs (LowerSigma0.lowerSigma0 x) ⟨64, 64⟩ :=
  CostIs.bind (costIs_sub_xor32 _) fun _ => costIs_sub_xor32 _

theorem costIs_lowerSigma1 (x : Var (fields 32) (F circomPrime)) :
    CostIs (LowerSigma1.lowerSigma1 x) ⟨64, 64⟩ :=
  CostIs.bind (costIs_sub_xor32 _) fun _ => costIs_sub_xor32 _

theorem costIs_upperSigma0 (x : Var (fields 32) (F circomPrime)) :
    CostIs (UpperSigma0.upperSigma0 x) ⟨64, 64⟩ :=
  CostIs.bind (costIs_sub_xor32 _) fun _ => costIs_sub_xor32 _

theorem costIs_upperSigma1 (x : Var (fields 32) (F circomPrime)) :
    CostIs (UpperSigma1.upperSigma1 x) ⟨64, 64⟩ :=
  CostIs.bind (costIs_sub_xor32 _) fun _ => costIs_sub_xor32 _

/-- Per-gadget subcircuit-cost wrappers. Each isolates the (single) `circuit.main`
unfolding into its own elaboration, so composite chains never accumulate the
defeq work of many subcircuit invocations into one heartbeat budget. -/
theorem costIs_sub_add32 (b : Var Add32.Inputs (F circomPrime)) :
    CostIs (subcircuit Add32.circuit b) add32Cost :=
  CostIs.subcircuit (costIs_add32 _ _)

theorem costIs_sub_ch32 (b : Var Ch32.Inputs (F circomPrime)) :
    CostIs (subcircuit Ch32.circuit b) ch32Cost :=
  CostIs.subcircuit (costIs_ch32 _ _ _)

theorem costIs_sub_maj32 (b : Var Maj32.Inputs (F circomPrime)) :
    CostIs (subcircuit Maj32.circuit b) maj32Cost :=
  CostIs.subcircuit (costIs_maj32 _ _ _)

theorem costIs_sub_upperSigma0 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit UpperSigma0.circuit b) sigmaCost :=
  CostIs.subcircuit (costIs_upperSigma0 _)

theorem costIs_sub_upperSigma1 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit UpperSigma1.circuit b) sigmaCost :=
  CostIs.subcircuit (costIs_upperSigma1 _)

theorem costIs_sub_lowerSigma0 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit LowerSigma0.circuit b) sigmaCost :=
  CostIs.subcircuit (costIs_lowerSigma0 _)

theorem costIs_sub_lowerSigma1 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit LowerSigma1.circuit b) sigmaCost :=
  CostIs.subcircuit (costIs_lowerSigma1 _)

theorem costIs_sha256Round (state : Vector (Var (fields 32) (F circomPrime)) 8)
    (k w : Var (fields 32) (F circomPrime)) :
    CostIs (SHA256Round.sha256Round state k w) sha256RoundCost :=
  CostIs.bind (costIs_sub_upperSigma1 _) fun _ =>
  CostIs.bind (costIs_sub_ch32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_upperSigma0 _) fun _ =>
  CostIs.bind (costIs_sub_maj32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ => CostIs.pure _

theorem costIs_scheduleStep (input : Var ScheduleStep.Inputs (F circomPrime)) :
    CostIs (ScheduleStep.main input) scheduleStepCost :=
  CostIs.bind (costIs_sub_lowerSigma1 _) fun _ =>
  CostIs.bind (costIs_sub_lowerSigma0 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  costIs_sub_add32 _

theorem costIs_sub_scheduleStep (b : Var ScheduleStep.Inputs (F circomPrime)) :
    CostIs (subcircuit ScheduleStep.circuit b) scheduleStepCost :=
  CostIs.subcircuit (costIs_scheduleStep _)

theorem costIs_messageSchedule (block : SHA256Block (Expression (F circomPrime))) :
    CostIs (MessageSchedule.main block) messageScheduleCost :=
  CostIs.foldlRange (constant := MessageSchedule.constantLength) (fun _ _ n =>
    (CostIs.bind (costIs_sub_scheduleStep _) fun _ => CostIs.pure _) n)

theorem costIs_sub_sha256Round (b : Var SHA256Round.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Round.circuit b) sha256RoundCost :=
  CostIs.subcircuit (costIs_sha256Round _ _ _)

theorem costIs_sha256Rounds (input : Var SHA256Rounds.Inputs (F circomPrime)) :
    CostIs (SHA256Rounds.main input) sha256RoundsCost :=
  CostIs.foldlRange (fun _ _ n => costIs_sub_sha256Round _ n)

theorem costIs_sub_messageSchedule (b : Var SHA256Block (F circomPrime)) :
    CostIs (subcircuit MessageSchedule.circuit b) messageScheduleCost :=
  CostIs.subcircuit (costIs_messageSchedule _)

theorem costIs_sub_sha256Rounds (b : Var SHA256Rounds.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds.circuit b) sha256RoundsCost :=
  CostIs.subcircuit (costIs_sha256Rounds _)

theorem costIs_compressBlock (input : Var CompressBlock.Inputs (F circomPrime)) :
    CostIs (CompressBlock.main input) compressBlockCost :=
  CostIs.bind (costIs_sub_messageSchedule _) fun _ =>
  CostIs.bind (costIs_sub_sha256Rounds _) fun _ =>
    CostIs.mapFinRange fun _ _ => costIs_sub_add32 _ _

theorem and32Cost_proof :
    circuitCount (And32.main (varFromOffset And32.Inputs 0 : Var And32.Inputs (F circomPrime))) =
      and32Cost :=
  costIs_and32 _ _ 0

theorem xor32Cost_proof :
    circuitCount (Xor32.main (varFromOffset Xor32.Inputs 0 : Var Xor32.Inputs (F circomPrime))) =
      xor32Cost :=
  costIs_xor32 _ _ 0

theorem add32Cost_proof :
    circuitCount (Add32.main (varFromOffset Add32.Inputs 0 : Var Add32.Inputs (F circomPrime))) =
      add32Cost :=
  costIs_add32 _ _ 0

theorem ch32Cost_proof :
    circuitCount (Ch32.main (varFromOffset Ch32.Inputs 0 : Var Ch32.Inputs (F circomPrime))) =
      ch32Cost :=
  costIs_ch32 _ _ _ 0

theorem maj32Cost_proof :
    circuitCount (Maj32.main (varFromOffset Maj32.Inputs 0 : Var Maj32.Inputs (F circomPrime))) =
      maj32Cost :=
  costIs_maj32 _ _ _ 0

theorem lowerSigma0Cost_proof :
    circuitCount (LowerSigma0.main (varFromOffset (fields 32) 0 : Var (fields 32) (F circomPrime))) =
      sigmaCost :=
  costIs_lowerSigma0 _ 0

theorem lowerSigma1Cost_proof :
    circuitCount (LowerSigma1.main (varFromOffset (fields 32) 0 : Var (fields 32) (F circomPrime))) =
      sigmaCost :=
  costIs_lowerSigma1 _ 0

theorem upperSigma0Cost_proof :
    circuitCount (UpperSigma0.main (varFromOffset (fields 32) 0 : Var (fields 32) (F circomPrime))) =
      sigmaCost :=
  costIs_upperSigma0 _ 0

theorem upperSigma1Cost_proof :
    circuitCount (UpperSigma1.main (varFromOffset (fields 32) 0 : Var (fields 32) (F circomPrime))) =
      sigmaCost :=
  costIs_upperSigma1 _ 0

theorem messageScheduleCost_proof :
    circuitCount (MessageSchedule.main
      (varFromOffset SHA256Block 0 : Var SHA256Block (F circomPrime))) =
      messageScheduleCost :=
  costIs_messageSchedule _ 0

theorem sha256RoundCost_proof :
    circuitCount (SHA256Round.main
      (varFromOffset SHA256Round.Inputs 0 : Var SHA256Round.Inputs (F circomPrime))) =
      sha256RoundCost :=
  costIs_sha256Round _ _ _ 0

theorem sha256RoundsCost_proof :
    circuitCount (SHA256Rounds.main
      (varFromOffset SHA256Rounds.Inputs 0 : Var SHA256Rounds.Inputs (F circomPrime))) =
      sha256RoundsCost :=
  costIs_sha256Rounds _ 0

theorem compressBlockCost_proof :
    circuitCount (CompressBlock.main
      (varFromOffset CompressBlock.Inputs 0 : Var CompressBlock.Inputs (F circomPrime))) =
      compressBlockCost :=
  costIs_compressBlock _ 0

/-! ## Per-gadget R1CS certificates (`IsR1CSCirc`)

`r1cs_*` lemmas certify, structurally, that every asserted expression of a gadget
is a single R1CS row, given that the gadget's input vectors are affine (`AffineW`,
i.e. each entry has structural degree ≤ 1 — true for all variable/constant atoms).
The witnessed outputs are `varFromOffset` vectors, hence affine, so the property
propagates through composition. No `native_decide`. -/

-- The trusted R1CS predicates are now `Prop`-valued `def`s (matching on
-- `r1csProducts` / the operation list). Left reducible, the unifier tries to
-- *evaluate* them on the asserted expressions when matching the single-row
-- lemmas / `assertZero` / `forEach` against a goal, which loops on neutral
-- subterms like `a[i]`. We only ever *apply* these certificates (never compute
-- the predicates), so keep them opaque for the R1CS proofs below.
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem affineW_rotr32 {x : Var (fields 32) (F circomPrime)} {k : Fin 32} (hx : AffineW x) :
    AffineW (rotr32 k x) := by
  intro i hi
  show Affine ((x.rotate k.val)[i])
  rw [Vector.getElem_rotate hi]
  exact hx _ _

theorem affineW_shr32 {x : Var (fields 32) (F circomPrime)} {k : Fin 32} (hx : AffineW x) :
    AffineW (shr32 k x) := by
  intro i hi
  show Affine ((shr32 k x)[i])
  rw [shr32, Vector.getElem_ofFn]
  split
  · exact hx _ _
  · exact Affine.zero

theorem affine_fieldFromBitsExpr {m : ℕ} (v : Var (fields m) (F circomPrime)) (h : AffineW v) :
    Affine (Utils.Bits.fieldFromBitsExpr v) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

/-- The output of `xor32` is its witness vector, hence affine. Stated via `circuit_norm`
so the offset reasoning stays cheap (avoids whnf-reducing the whole bind). -/
theorem affineW_xor32_output (a b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((Xor32.xor32 a b).output n) := by
  have h : (Xor32.xor32 a b).output n = varFromOffset (fields 32) n := by
    simp only [Xor32.xor32, circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem r1cs_and32 (a b : Var (fields 32) (F circomPrime)) (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (And32.and32 a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_sub_mul (affineW_witnessVector_output 32 _ n j.val j.isLt)
            (ha j.val j.isLt) (hb j.val j.isLt)) m)
      (fun _ => IsR1CSCirc.pure _)

theorem and32_isR1CS : isR1CS (F := F circomPrime) And32.main :=
  isR1CS_of_IsR1CSCirc (r1cs_and32 _ _ (affineW_varFromOffset _ _) (affineW_varFromOffset _ _))

theorem r1cs_xor32 (a b : Var (fields 32) (F circomPrime)) (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (Xor32.xor32 a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_add_mul
            (Affine.sub (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt)
              (ha j.val j.isLt)) (hb j.val j.isLt))
            (Affine.fconst_mul _ (ha j.val j.isLt)) (hb j.val j.isLt)) m)
      (fun _ => IsR1CSCirc.pure _)

theorem xor32_isR1CS : isR1CS (F := F circomPrime) Xor32.main :=
  isR1CS_of_IsR1CSCirc (r1cs_xor32 _ _ (affineW_varFromOffset _ _) (affineW_varFromOffset _ _))

theorem r1cs_add32 (a b : Var (fields 32) (F circomPrime)) (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (Add32.add32 a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun n' =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 32 _ n j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt) (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul (affine_witnessField_output _ n')
        (Affine.sub (affine_witnessField_output _ n') (Affine.const 1))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_of_affine
        (Affine.sub (Affine.sub (Affine.add
          (affine_fieldFromBitsExpr a ha) (affine_fieldFromBitsExpr b hb))
          (affine_fieldFromBitsExpr _ (affineW_witnessVector_output 32 _ n)))
          (Affine.fconst_mul _ (affine_witnessField_output _ n')))))
    fun _ => IsR1CSCirc.pure _

theorem add32_isR1CS : isR1CS (F := F circomPrime) Add32.main :=
  isR1CS_of_IsR1CSCirc (r1cs_add32 _ _ (affineW_varFromOffset _ _) (affineW_varFromOffset _ _))

theorem r1cs_ch32 (e f g : Var (fields 32) (F circomPrime))
    (he : AffineW e) (hf : AffineW f) (hg : AffineW g) :
    IsR1CSCirc (Ch32.ch32 e f g) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_sub_mul
            (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt) (hg j.val j.isLt))
            (he j.val j.isLt)
            (Affine.sub (hf j.val j.isLt) (hg j.val j.isLt))) m)
      (fun _ => IsR1CSCirc.pure _)

theorem ch32_isR1CS : isR1CS (F := F circomPrime) Ch32.main :=
  isR1CS_of_IsR1CSCirc
    (r1cs_ch32 _ _ _ (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
      (affineW_varFromOffset _ _))

theorem r1cs_maj32 (a b c : Var (fields 32) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) :
    IsR1CSCirc (Maj32.maj32 a b c) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n' =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_sub_mul (affineW_witnessVector_output 32 _ n j.val j.isLt)
          (ha j.val j.isLt) (hb j.val j.isLt)) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_sub_mul
          (Affine.sub (affineW_witnessVector_output 32 _ n' j.val j.isLt)
            (affineW_witnessVector_output 32 _ n j.val j.isLt))
          (hc j.val j.isLt)
          (Affine.sub (Affine.add (ha j.val j.isLt) (hb j.val j.isLt))
            (Affine.fconst_mul _ (affineW_witnessVector_output 32 _ n j.val j.isLt)))) m)
    fun _ => IsR1CSCirc.pure _

theorem maj32_isR1CS : isR1CS (F := F circomPrime) Maj32.main :=
  isR1CS_of_IsR1CSCirc
    (r1cs_maj32 _ _ _ (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
      (affineW_varFromOffset _ _))

/-- Output of a `subcircuit Xor32.circuit` is its witness row, hence affine. -/
theorem affineW_subOut_xor32 (b : Var Xor32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Xor32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Xor32.circuit, Xor32.elaborated]; exact Affine.var _

theorem r1cs_sub_xor32 (b : Var Xor32.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) : IsR1CSCirc (subcircuit Xor32.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_xor32 _ _ ha hb)

theorem r1cs_lowerSigma0 (x : Var (fields 32) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (LowerSigma0.lowerSigma0 x) :=
  IsR1CSCirc.bind_out (r1cs_sub_xor32 _ (affineW_rotr32 hx) (affineW_rotr32 hx)) fun _ =>
    r1cs_sub_xor32 _ (affineW_subOut_xor32 _ _) (affineW_shr32 hx)

theorem lowerSigma0_isR1CS : isR1CS (F := F circomPrime) LowerSigma0.main :=
  isR1CS_of_IsR1CSCirc (r1cs_lowerSigma0 _ (affineW_varFromOffset _ _))

theorem r1cs_lowerSigma1 (x : Var (fields 32) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (LowerSigma1.lowerSigma1 x) :=
  IsR1CSCirc.bind_out (r1cs_sub_xor32 _ (affineW_rotr32 hx) (affineW_rotr32 hx)) fun _ =>
    r1cs_sub_xor32 _ (affineW_subOut_xor32 _ _) (affineW_shr32 hx)

theorem lowerSigma1_isR1CS : isR1CS (F := F circomPrime) LowerSigma1.main :=
  isR1CS_of_IsR1CSCirc (r1cs_lowerSigma1 _ (affineW_varFromOffset _ _))

theorem r1cs_upperSigma0 (x : Var (fields 32) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (UpperSigma0.upperSigma0 x) :=
  IsR1CSCirc.bind_out (r1cs_sub_xor32 _ (affineW_rotr32 hx) (affineW_rotr32 hx)) fun _ =>
    r1cs_sub_xor32 _ (affineW_subOut_xor32 _ _) (affineW_rotr32 hx)

theorem upperSigma0_isR1CS : isR1CS (F := F circomPrime) UpperSigma0.main :=
  isR1CS_of_IsR1CSCirc (r1cs_upperSigma0 _ (affineW_varFromOffset _ _))

theorem r1cs_upperSigma1 (x : Var (fields 32) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (UpperSigma1.upperSigma1 x) :=
  IsR1CSCirc.bind_out (r1cs_sub_xor32 _ (affineW_rotr32 hx) (affineW_rotr32 hx)) fun _ =>
    r1cs_sub_xor32 _ (affineW_subOut_xor32 _ _) (affineW_rotr32 hx)

theorem upperSigma1_isR1CS : isR1CS (F := F circomPrime) UpperSigma1.main :=
  isR1CS_of_IsR1CSCirc (r1cs_upperSigma1 _ (affineW_varFromOffset _ _))

/-! ### Affineness of constants, witness rows and subcircuit outputs -/

theorem affineW_constWord32 (m : ℕ) :
    AffineW (constWord32 m : Var (fields 32) (F circomPrime)) := by
  intro j hj; rw [constWord32, Vector.getElem_ofFn]; exact Affine.const _

theorem affineW_mapRange_var (f : ℕ → ℕ) :
    AffineW (Vector.mapRange 32 (fun i => Expression.var ⟨f i⟩) : Var (fields 32) (F circomPrime)) := by
  intro j hj; rw [Vector.getElem_mapRange]; exact Affine.var _

theorem affineW_subOut_add32 (b : Var Add32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Add32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Add32.circuit, Add32.elaborated]; exact Affine.var _

theorem affineW_subOut_ch32 (b : Var Ch32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Ch32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Ch32.circuit, Ch32.elaborated]; exact Affine.var _

theorem affineW_subOut_maj32 (b : Var Maj32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Maj32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Maj32.circuit, Maj32.elaborated]; exact Affine.var _

theorem affineW_subOut_upperSigma0 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit UpperSigma0.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, UpperSigma0.circuit, UpperSigma0.elaborated]
  exact Affine.var _

theorem affineW_subOut_upperSigma1 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit UpperSigma1.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, UpperSigma1.circuit, UpperSigma1.elaborated]
  exact Affine.var _

theorem affineW_subOut_lowerSigma0 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit LowerSigma0.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, LowerSigma0.circuit, LowerSigma0.elaborated]
  exact Affine.var _

theorem affineW_subOut_lowerSigma1 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit LowerSigma1.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, LowerSigma1.circuit, LowerSigma1.elaborated]
  exact Affine.var _

/-! ### Subcircuit R1CS wrappers (each isolates one `circuit.main` defeq) -/

theorem r1cs_sub_add32 (b : Var Add32.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) : IsR1CSCirc (subcircuit Add32.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_add32 _ _ ha hb)

theorem r1cs_sub_ch32 (b : Var Ch32.Inputs (F circomPrime))
    (he : AffineW b.e) (hf : AffineW b.f) (hg : AffineW b.g) :
    IsR1CSCirc (subcircuit Ch32.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_ch32 _ _ _ he hf hg)

theorem r1cs_sub_maj32 (b : Var Maj32.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) :
    IsR1CSCirc (subcircuit Maj32.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_maj32 _ _ _ ha hb hc)

theorem r1cs_sub_upperSigma0 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit UpperSigma0.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_upperSigma0 _ hb)

theorem r1cs_sub_upperSigma1 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit UpperSigma1.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_upperSigma1 _ hb)

theorem r1cs_sub_lowerSigma0 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit LowerSigma0.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_lowerSigma0 _ hb)

theorem r1cs_sub_lowerSigma1 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit LowerSigma1.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_lowerSigma1 _ hb)

theorem r1cs_sha256Round (state : Vector (Var (fields 32) (F circomPrime)) 8)
    (k w : Var (fields 32) (F circomPrime))
    (hstate : ∀ i (hi : i < 8), AffineW state[i]) (hk : AffineW k) (hw : AffineW w) :
    IsR1CSCirc (SHA256Round.sha256Round state k w) :=
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _ (hstate 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_ch32 _ (hstate 4 (by omega)) (hstate 5 (by omega)) (hstate 6 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (hstate 7 (by omega)) (affineW_subOut_upperSigma1 _ _)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_subOut_add32 _ _) (affineW_subOut_ch32 _ _)) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_add32 _ (affineW_subOut_add32 _ _) hk) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_add32 _ (affineW_subOut_add32 _ _) hw) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _ (hstate 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_maj32 _ (hstate 0 (by omega)) (hstate 1 (by omega)) (hstate 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_subOut_upperSigma0 _ _) (affineW_subOut_maj32 _ _)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_subOut_add32 _ _) (affineW_subOut_add32 _ _)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (hstate 3 (by omega)) (affineW_subOut_add32 _ _)) fun _ =>
  IsR1CSCirc.pure _

/-- The 8 output words of a `SHA256Round` are affine when the input state is.
Each word's `circuit_norm` reduction is a separate declaration so it gets its own
heartbeat budget (reducing all eight at once is too expensive). -/
theorem affineW_sha256Round_out_w0 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[0]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]
  exact affineW_mapRange_var _

theorem affineW_sha256Round_out_w4 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[4]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]
  exact affineW_mapRange_var _

theorem affineW_sha256Round_out_w1 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[0]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[1]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w2 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[1]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[2]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w3 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[2]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[3]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w5 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[4]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[5]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w6 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[5]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[6]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w7 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[6]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[7]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_output (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Round.circuit input).output n)[j]) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact affineW_sha256Round_out_w0 _ _
  · exact affineW_sha256Round_out_w1 _ _ (hstate 0 (by omega))
  · exact affineW_sha256Round_out_w2 _ _ (hstate 1 (by omega))
  · exact affineW_sha256Round_out_w3 _ _ (hstate 2 (by omega))
  · exact affineW_sha256Round_out_w4 _ _
  · exact affineW_sha256Round_out_w5 _ _ (hstate 4 (by omega))
  · exact affineW_sha256Round_out_w6 _ _ (hstate 5 (by omega))
  · exact affineW_sha256Round_out_w7 _ _ (hstate 6 (by omega))

theorem r1cs_sha256Rounds (input : Var SHA256Rounds.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW input.schedule[k]) :
    IsR1CSCirc (SHA256Rounds.main input) := by
  refine IsR1CSCirc.foldlRange_inv (fun s => ∀ j (hj : j < 8), AffineW s[j]) hstate ?_ ?_
  · intro s i hs
    exact IsR1CSCirc.subcircuit
      (r1cs_sha256Round _ _ _ hs (affineW_constWord32 _) (hsched _ i.isLt))
  · intro s i n hs
    exact affineW_sha256Round_output _ n hs

theorem affineW_rounds_input_state (j : ℕ) (hj : j < 8) :
    AffineW ((varFromOffset SHA256Rounds.Inputs 0 :
      Var SHA256Rounds.Inputs (F circomPrime)).state[j]) := by
  have heq : (varFromOffset SHA256Rounds.Inputs 0 :
      Var SHA256Rounds.Inputs (F circomPrime)).state = varFromOffset SHA256State 0 := by
    simp only [circuit_norm]
  rw [heq]; exact affineW_varFromOffset_pvec _ _ hj

theorem affineW_rounds_input_sched (k : ℕ) (hk : k < 64) :
    AffineW ((varFromOffset SHA256Rounds.Inputs 0 :
      Var SHA256Rounds.Inputs (F circomPrime)).schedule[k]) := by
  have heq : (varFromOffset SHA256Rounds.Inputs 0 :
      Var SHA256Rounds.Inputs (F circomPrime)).schedule = varFromOffset SHA256Schedule (8 * 32) := by
    simp only [circuit_norm]
  rw [heq]; exact affineW_varFromOffset_pvec _ _ hk

theorem sha256Rounds_isR1CS : isR1CS (F := F circomPrime) SHA256Rounds.main :=
  isR1CS_of_IsR1CSCirc
    (r1cs_sha256Rounds _ affineW_rounds_input_state affineW_rounds_input_sched)

theorem r1cs_scheduleStep (input : Var ScheduleStep.Inputs (F circomPrime))
    (h2 : AffineW input.wm2) (h7 : AffineW input.wm7)
    (h15 : AffineW input.wm15) (h16 : AffineW input.wm16) :
    IsR1CSCirc (ScheduleStep.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_lowerSigma1 _ h2) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_lowerSigma0 _ h15) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_subOut_lowerSigma1 _ _) h7) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_subOut_add32 _ _) (affineW_subOut_lowerSigma0 _ _)) fun _ =>
  r1cs_sub_add32 _ (affineW_subOut_add32 _ _) h16

theorem affineW_subOut_scheduleStep (b : Var ScheduleStep.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit ScheduleStep.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, ScheduleStep.circuit, ScheduleStep.elaborated]
  exact Affine.var _

theorem r1cs_sub_scheduleStep (b : Var ScheduleStep.Inputs (F circomPrime))
    (h2 : AffineW b.wm2) (h7 : AffineW b.wm7) (h15 : AffineW b.wm15) (h16 : AffineW b.wm16) :
    IsR1CSCirc (subcircuit ScheduleStep.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_scheduleStep b h2 h7 h15 h16)

theorem r1cs_messageSchedule (block : SHA256Block (Expression (F circomPrime)))
    (hblock : ∀ k (hk : k < 16), AffineW block[k]) : IsR1CSCirc (MessageSchedule.main block) := by
  refine IsR1CSCirc.foldlRange_inv (constant := MessageSchedule.constantLength)
    (fun w => ∀ k (hk : k < 64), AffineW w[k]) ?_ ?_ ?_
  · intro k hk
    show AffineW ((block ++ Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F circomPrime))))[k])
    rw [Vector.getElem_append]
    split
    · exact hblock _ _
    · rw [Vector.getElem_replicate]
      intro j hj
      rw [Vector.getElem_replicate]
      exact Affine.zero (F := F circomPrime)
  · intro w i hw
    exact IsR1CSCirc.bind_out
      (r1cs_sub_scheduleStep _ (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)))
      (fun _ => IsR1CSCirc.pure _)
  · intro w i n hw k hk
    simp only [circuit_norm, Vector.getElem_set]
    split
    · exact affineW_varFromOffset _ _
    · exact hw _ _

theorem messageSchedule_isR1CS : isR1CS (Input := SHA256Block) (F := F circomPrime) MessageSchedule.main :=
  isR1CS_of_IsR1CSCirc (r1cs_messageSchedule _ (fun _k hk => affineW_varFromOffset_pvec _ _ hk))

/-- Every word of `stateVar` is affine when the input state is (recursion over
rounds; each word is either a fresh witness row or a pass-through). -/
theorem affineW_stateVar (i₀ : ℕ) (s : Var SHA256State (F circomPrime))
    (hs : ∀ j (hj : j < 8), AffineW s[j]) :
    ∀ (m j : ℕ) (hj : j < 8), AffineW ((SHA256Rounds.stateVar i₀ s m)[j]) := by
  intro m
  induction m with
  | zero => intro j hj; exact hs j hj
  | succ p ih =>
      intro j hj
      rw [SHA256Rounds.stateVar]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact affineW_mapRange_var _
      · exact ih 0 (by omega)
      · exact ih 1 (by omega)
      · exact ih 2 (by omega)
      · exact affineW_mapRange_var _
      · exact ih 4 (by omega)
      · exact ih 5 (by omega)
      · exact ih 6 (by omega)

/-- Every word of `varSchedule` is affine when the input block is. -/
theorem affineW_varSchedule (i₀ : ℕ) (block : SHA256Block (Expression (F circomPrime)))
    (hblock : ∀ k (hk : k < 16), AffineW block[k]) :
    ∀ (m k : ℕ) (hk : k < 64), AffineW ((MessageSchedule.varSchedule i₀ block m)[k]) := by
  intro m
  induction m with
  | zero =>
      intro k hk
      rw [MessageSchedule.varSchedule]
      show AffineW ((block ++ Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F circomPrime))))[k])
      rw [Vector.getElem_append]
      split
      · exact hblock _ _
      · rw [Vector.getElem_replicate]
        intro j hj; rw [Vector.getElem_replicate]; exact Affine.zero (F := F circomPrime)
  | succ p ih =>
      intro k hk
      rw [MessageSchedule.varSchedule]
      split
      · rw [Vector.getElem_set]
        split
        · exact affineW_varFromOffset _ _
        · exact ih k hk
      · exact ih k hk

theorem affineW_subOut_messageSchedule (b : SHA256Block (Expression (F circomPrime))) (n : ℕ)
    (hb : ∀ k (hk : k < 16), AffineW b[k]) :
    ∀ k (hk : k < 64), AffineW (((subcircuit MessageSchedule.circuit b).output n)[k]) := by
  intro k hk
  have heq : (subcircuit MessageSchedule.circuit b).output n = MessageSchedule.varSchedule n b 48 := by
    simp only [circuit_norm, subcircuit, MessageSchedule.circuit, MessageSchedule.elaborated]
  rw [heq]; exact affineW_varSchedule n b hb 48 k hk

theorem affineW_subOut_sha256Rounds (b : Var SHA256Rounds.Inputs (F circomPrime)) (n : ℕ)
    (hb : ∀ j (hj : j < 8), AffineW b.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Rounds.circuit b).output n)[j]) := by
  intro j hj
  have heq : (subcircuit SHA256Rounds.circuit b).output n = SHA256Rounds.stateVar n b.state 64 := by
    simp only [circuit_norm, subcircuit, SHA256Rounds.circuit, SHA256Rounds.elaborated]
  rw [heq]; exact affineW_stateVar n b.state hb 64 j hj

theorem r1cs_sub_messageSchedule (b : SHA256Block (Expression (F circomPrime)))
    (hb : ∀ k (hk : k < 16), AffineW b[k]) : IsR1CSCirc (subcircuit MessageSchedule.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_messageSchedule _ hb)

theorem r1cs_sub_sha256Rounds (b : Var SHA256Rounds.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW b.schedule[k]) :
    IsR1CSCirc (subcircuit SHA256Rounds.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_sha256Rounds _ hstate hsched)

theorem r1cs_compressBlock (input : Var CompressBlock.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hblock : ∀ k (hk : k < 16), AffineW input.block[k]) :
    IsR1CSCirc (CompressBlock.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_messageSchedule _ hblock) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_sha256Rounds _ hstate (affineW_subOut_messageSchedule _ _ hblock)) fun _ =>
  IsR1CSCirc.mapFinRange fun i n =>
    r1cs_sub_add32 _ (hstate i.val i.isLt)
      (affineW_subOut_sha256Rounds _ _ hstate i.val i.isLt) n

theorem affineW_subOut_compressBlock (input : Var CompressBlock.Inputs (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit CompressBlock.circuit input).output n)[j]) := by
  intro j hj
  simp only [circuit_norm, subcircuit, CompressBlock.circuit, CompressBlock.elaborated]
  exact affineW_mapRange_var _

theorem compressBlock_isR1CS : isR1CS (F := F circomPrime) CompressBlock.main :=
  isR1CS_of_IsR1CSCirc
    (r1cs_compressBlock _
      (fun j hj => by
        have heq : (varFromOffset CompressBlock.Inputs 0 :
            Var CompressBlock.Inputs (F circomPrime)).state = varFromOffset SHA256State 0 := by
          simp only [circuit_norm]
        rw [heq]; exact affineW_varFromOffset_pvec _ _ hj)
      (fun k hk => by
        have heq : (varFromOffset CompressBlock.Inputs 0 :
            Var CompressBlock.Inputs (F circomPrime)).block = varFromOffset SHA256Block (8 * 32) := by
          simp only [circuit_norm]
        rw [heq]; exact affineW_varFromOffset_pvec _ _ hk))

/-! ## Structural cost / R1CS certificates for the padding gadgets and `main`

These mirror the cost lemmas above for the padding/digest gadgets, and add the
matching `IsR1CSCirc` certificates, all without `native_decide`/`decide`.

Two performance points make the deep `do`-blocks here elaborate cheaply:

* the `BitsBool` over `paddedBitsLen` bits is certified through a **size-generic**
  wrapper (`*_sub_bitsBool`) and only then instantiated, so the unifier never
  materialises the 2560-element flat operation list at a concrete size; and
* `byteFromWord`/`expectedPaddedByte`/`paddedWord`/`paddedBit`/`paddedBlock` are
  made `local irreducible` before the composite proofs, so unification against
  `CheckPad.main` stays syntactic instead of unfolding the 256-deep `Fin.foldl`
  expressions. The composite proofs supply `circuit`/`b` explicitly for the same
  reason (no inference from the now-opaque goal is required).
-/

/-! ### Affineness of `byteFromWord` and the single-row certificate for the
padding-byte constraint

`expectedPaddedByte` is written in factored form `constPart + message[j] · coefSum`,
so the asserted `byteFromWord word b - expectedPaddedByte …` is `L - (C + A·B)`
with `L, C, A, B` all affine — a single R1CS row. (The naive sum-of-products form
would be rank-2+ once `message` is a vector of input variables.) -/

/-- `L - (C + A*B)` with all of `L, C, A, B` affine is a single R1CS row. -/
theorem isR1CSRow_sub_add_mul {L C A B : Expression (F circomPrime)}
    (hL : Affine L) (hC : Affine C) (hA : Affine A) (hB : Affine B) :
    isR1CSRow (L - (C + A * B)) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (L + -(C + A * B)) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
            r1csProducts_of_affine hL, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (L + -(C + A * B)) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
            r1csProducts_of_affine hL, r1csProducts_of_affine hC, h]) (by omega)

theorem affine_byteFromWord (word : Var (fields 32) (F circomPrime)) (b : Fin 4)
    (hw : AffineW word) : Affine (byteFromWord word b) := by
  unfold byteFromWord
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc bit hacc
    exact Affine.add hacc (Affine.mul_deg0 (hw _ (by omega)) (degree_const _))

/-- The padding-byte constraint is a single R1CS row when the witnessed word and
the (now symbolic) message and length flags are affine. -/
theorem r1csRow_checkPaddedByte (word : Var (fields 32) (F circomPrime)) (b : Fin 4)
    (message lenFlags : Var (fields inputBufferLen) (F circomPrime)) (j : Fin paddedBytesLen)
    (hword : AffineW word) (hmsg : AffineW message) (hflags : AffineW lenFlags) :
    isR1CSRow (byteFromWord word b - expectedPaddedByte message lenFlags j) := by
  rw [expectedPaddedByte]
  refine isR1CSRow_sub_add_mul (affine_byteFromWord _ _ hword) ?_ ?_ ?_
  · -- constant part: ∑ lenFlags[len] · (padding const)
    apply affine_finFoldl'
    · exact Affine.zero
    · intro acc len hacc
      exact Affine.add hacc (Affine.mul_deg0 (hflags _ len.isLt) (degree_const _))
  · -- message term: message[j] (or 0 past the buffer), affine
    split
    · exact hmsg _ _
    · exact Affine.zero
  · -- coefficient mass: ∑_{len > j} lenFlags[len], affine
    apply affine_finFoldl'
    · exact Affine.zero
    · intro acc len hacc
      refine Affine.add hacc ?_
      split
      · exact hflags _ len.isLt
      · exact Affine.zero

/-! ### Affineness of `paddedWord` / `paddedBlock` slices of an affine bit-vector -/

theorem affineW_paddedWord (padded : Var SHA256PaddedBits (F circomPrime))
    (hp : AffineW padded) (j : Fin paddedBytesLen) : AffineW (paddedWord padded j) := by
  intro bit hbit
  rw [paddedWord, Vector.getElem_ofFn]
  exact hp _ _

theorem affineW_paddedBlock (padded : Var SHA256PaddedBits (F circomPrime))
    (hp : AffineW padded) (block : Fin paddedBlocksLen) :
    ∀ k (hk : k < 16), AffineW ((paddedBlock padded block)[k]'hk) := by
  intro k hk bit hbit
  rw [paddedBlock, Vector.getElem_ofFn, Vector.getElem_ofFn, paddedBit]
  exact hp _ _

/-! ### Per-gadget cost leaves for the padding gadgets -/

theorem costIs_checkLenFlags (b : Var CheckLenFlags.Inputs (F circomPrime)) :
    CostIs (CheckLenFlags.main b) ⟨0, 258⟩ :=
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ => CostIs.assertZero _

theorem costIs_bitsBool (n : ℕ) [NeZero n] (input : Var (fields n) (F circomPrime)) :
    CostIs (BitsBool.main n input) ⟨0, n⟩ := by
  have h : CostIs (BitsBool.main n input) ⟨n * 0, n * 1⟩ :=
    CostIs.forEach fun _ => CostIs.assertZero _
  rw [Nat.mul_zero, Nat.mul_one] at h
  exact h

theorem costIs_checkPaddedByte (j : Fin paddedBytesLen)
    (input : Var CheckPaddedByte.Inputs (F circomPrime)) :
    CostIs (CheckPaddedByte.main j input) ⟨0, 1⟩ :=
  CostIs.assertZero _

/-! ### R1CS certificates for the padding gadgets -/

theorem r1cs_checkLenFlags (b : Var CheckLenFlags.Inputs (F circomPrime))
    (hmsg : Affine b.messageLen) (hflags : AffineW b.lenFlags) :
    IsR1CSCirc (CheckLenFlags.main b) :=
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun i m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (hflags i.val i.isLt)
          (Affine.sub (hflags i.val i.isLt) (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_of_affine
        (Affine.sub
          (affine_finFoldl' (fun acc i => acc + b.lenFlags[i]) 0 Affine.zero
            (fun acc i h => Affine.add h (hflags i.val i.isLt)))
          (Affine.const 1))))
    fun _ =>
  IsR1CSCirc.assertZero
    (isR1CSRow_of_affine
      (Affine.sub hmsg
        (affine_finFoldl'
          (fun acc i => acc + b.lenFlags[i] * (((i.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
          0 Affine.zero
          (fun acc i h => Affine.add h (Affine.mul_deg0 (hflags i.val i.isLt) (degree_const _))))))

theorem r1cs_bitsBool (n : ℕ) [NeZero n] (input : Var (fields n) (F circomPrime))
    (hin : AffineW input) : IsR1CSCirc (BitsBool.main n input) :=
  IsR1CSCirc.forEach fun i m =>
    IsR1CSCirc.assertZero
      (isR1CSRow_mul (hin i.val i.isLt)
        (Affine.sub (hin i.val i.isLt) (Affine.const 1))) m

theorem r1cs_checkPaddedByte (j : Fin paddedBytesLen)
    (input : Var CheckPaddedByte.Inputs (F circomPrime))
    (hword : AffineW input.word) (hmsg : AffineW input.message) (hflags : AffineW input.lenFlags) :
    IsR1CSCirc (CheckPaddedByte.main j input) :=
  IsR1CSCirc.assertZero (r1csRow_checkPaddedByte _ _ _ _ j hword hmsg hflags)

/-! ### Size-generic subcircuit wrappers for `BitsBool`

Proving the `assertion` wrapper at *generic* `n` keeps the unifier from
materialising the concrete `n`-element operation list; instantiating afterwards
is pure substitution. -/

theorem costIs_sub_checkLenFlags (b : Var CheckLenFlags.Inputs (F circomPrime)) :
    CostIs (assertion CheckLenFlags.circuit b) ⟨0, 258⟩ :=
  CostIs.assertion (costIs_checkLenFlags b)

theorem r1cs_sub_checkLenFlags (b : Var CheckLenFlags.Inputs (F circomPrime))
    (hmsg : Affine b.messageLen) (hflags : AffineW b.lenFlags) :
    IsR1CSCirc (assertion CheckLenFlags.circuit b) :=
  IsR1CSCirc.assertion (r1cs_checkLenFlags b hmsg hflags)

theorem costIs_sub_bitsBool (n : ℕ) [NeZero n] (input : Var (fields n) (F circomPrime)) :
    CostIs (assertion (BitsBool.circuit n) input) ⟨0, n⟩ :=
  CostIs.assertion (costIs_bitsBool n input)

theorem r1cs_sub_bitsBool (n : ℕ) [NeZero n] (input : Var (fields n) (F circomPrime))
    (hp : AffineW input) : IsR1CSCirc (assertion (BitsBool.circuit n) input) :=
  IsR1CSCirc.assertion (r1cs_bitsBool n input hp)

-- Keep the deep `Fin.foldl`/`ofFn` expressions folded during the composite
-- proofs below: unification against `CheckPad.main` stays syntactic.
attribute [local irreducible] byteFromWord expectedPaddedByte paddedWord paddedBit paddedBlock

theorem costIs_checkPad (input : Var CheckPad.Inputs (F circomPrime)) :
    CostIs (CheckPad.main input) ⟨0, 3138⟩ :=
  CostIs.bind (costIs_sub_checkLenFlags _) fun _ =>
  CostIs.bind (costIs_sub_bitsBool paddedBitsLen _) fun _ =>
  CostIs.forEach (fun j m =>
    CostIs.assertion (circuit := CheckPaddedByte.circuit j)
      (b := ⟨input.messageLen, input.message, input.lenFlags, paddedWord input.padded j⟩)
      (costIs_checkPaddedByte j _) m)

theorem r1cs_checkPad (input : Var CheckPad.Inputs (F circomPrime))
    (hmsglen : Affine input.messageLen) (hmsg : AffineW input.message)
    (hflags : AffineW input.lenFlags) (hpadded : AffineW input.padded) :
    IsR1CSCirc (CheckPad.main input) :=
  IsR1CSCirc.bind (r1cs_sub_checkLenFlags _ hmsglen hflags) fun _ =>
  IsR1CSCirc.bind (r1cs_sub_bitsBool paddedBitsLen _ hpadded) fun _ =>
  IsR1CSCirc.forEach (fun j m =>
    IsR1CSCirc.assertion (circuit := CheckPaddedByte.circuit j)
      (b := ⟨input.messageLen, input.message, input.lenFlags, paddedWord input.padded j⟩)
      (r1cs_checkPaddedByte j _ (affineW_paddedWord _ hpadded j) hmsg hflags) m)

/-! ### Subcircuit wrappers for `CheckPad`, compress blocks, digest -/

theorem costIs_sub_checkPad (b : Var CheckPad.Inputs (F circomPrime)) :
    CostIs (assertion CheckPad.circuit b) ⟨0, 3138⟩ :=
  CostIs.assertion (costIs_checkPad b)

theorem r1cs_sub_checkPad (b : Var CheckPad.Inputs (F circomPrime))
    (hmsglen : Affine b.messageLen) (hmsg : AffineW b.message)
    (hflags : AffineW b.lenFlags) (hpadded : AffineW b.padded) :
    IsR1CSCirc (assertion CheckPad.circuit b) :=
  IsR1CSCirc.assertion (r1cs_checkPad b hmsglen hmsg hflags hpadded)

theorem costIs_sub_selectDigest (input : Var SelectDigest.Inputs (F circomPrime)) :
    CostIs (subcircuit SelectDigest.circuit input) Count.zero :=
  CostIs.subcircuit (fun _ => rfl)

/-- `SelectDigest.main` is a pure output (no operations), so it is trivially R1CS. -/
theorem r1cs_selectDigest (b : Var SelectDigest.Inputs (F circomPrime)) :
    IsR1CSCirc (subcircuit SelectDigest.circuit b) :=
  IsR1CSCirc.subcircuit (fun n => by
    rw [show (SelectDigest.circuit.main b).operations n = [] from rfl, Lemmas.operationsIsR1CS_nil]
    trivial)

theorem costIs_sub_compressBlock (b : Var CompressBlock.Inputs (F circomPrime)) :
    CostIs (subcircuit CompressBlock.circuit b) compressBlockCost :=
  CostIs.subcircuit (costIs_compressBlock _)

theorem r1cs_sub_compressBlock (b : Var CompressBlock.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hblock : ∀ k (hk : k < 16), AffineW b.block[k]) :
    IsR1CSCirc (subcircuit CompressBlock.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_compressBlock _ hstate hblock)

/-- The fixed initial state `H0` is a vector of constant words, hence affine. -/
theorem affineW_state0 (j : ℕ) (hj : j < 8) :
    AffineW ((Vector.ofFn fun i => constWord32 Specs.SHA256.H0[i] :
      Var SHA256State (F circomPrime))[j]'hj) := by
  rw [Vector.getElem_ofFn]
  exact affineW_constWord32 _

/-! ### Symbolic top-level input atoms

The challenge's `isR1CS main` allocates the inputs as *variables* at offset 0, so
the message bytes and length are affine (degree-1) atoms, not constants. -/

theorem affineW_input_message :
    AffineW ((varFromOffset Input 0 : Var Input (F circomPrime)).message) := by
  have heq : (varFromOffset Input 0 : Var Input (F circomPrime)).message
      = varFromOffset (fields inputBufferLen) 0 := by simp only [circuit_norm]
  rw [heq]; exact affineW_varFromOffset _ _

theorem affine_input_messageLen :
    Affine ((varFromOffset Input 0 : Var Input (F circomPrime)).messageLen) := by
  simp only [circuit_norm]
  exact Affine.var _

end Cost

end Solution.SHA256
