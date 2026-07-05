import Challenge.Instances.KeccakF1600.Interface
import Solution.KeccakF1600.Xor5Lane
import Solution.KeccakF1600.ChiLane
import Solution.KeccakF1600.KeccakRound
import Solution.KeccakF1600.MainTheorems
import Challenge.Utils.CostR1CS

namespace Solution.KeccakF1600

open Challenge.Instances.KeccakF1600.Interface
open Challenge.CostR1CS

namespace Cost

/-- All 25 lanes of a symbolic state are affine. -/
def StateAffine (s : Var KeccakBitState (F circomPrime)) : Prop :=
  ∀ j (hj : j < 25), AffineW (s[j]'hj)

/-- All 5 lanes of a symbolic row are affine. -/
def RowAffine (s : Var KeccakBitRow (F circomPrime)) : Prop :=
  ∀ j (hj : j < 5), AffineW (s[j]'hj)

theorem affineW_rotl {x : Var (fields 64) (F circomPrime)} (hx : AffineW x) (k : ℕ) :
    AffineW (rotl k x) := by
  intro i hi
  show Affine ((x.rotate (64 - k % 64))[i])
  rw [Vector.getElem_rotate]
  exact hx _ (Nat.mod_lt _ (by norm_num))

theorem affineW_notBits {x : Var (fields 64) (F circomPrime)} (hx : AffineW x) :
    AffineW (notBits x) := by
  intro i hi
  show Affine ((x.map fun ai => 1 - ai)[i])
  rw [Vector.getElem_map]
  exact Affine.sub (Affine.const 1) (hx i hi)

theorem affineW_xorConst {x : Var (fields 64) (F circomPrime)} (hx : AffineW x) (c : ℕ) :
    AffineW (xorConst c x) := by
  intro i hi
  show Affine ((Vector.ofFn fun (w : Fin 64) => if c.testBit w.val then 1 - x[w] else x[w])[i])
  rw [Vector.getElem_ofFn]
  split
  · exact Affine.sub (Affine.const 1) (hx i hi)
  · exact hx i hi

theorem stateAffine_rhoPiWire {s : Var KeccakBitState (F circomPrime)} (hs : StateAffine s) :
    StateAffine (rhoPiWire s) := by
  intro j hj
  rw [rhoPiWire_getElem s j hj]
  exact affineW_rotl (hs _ (piSource ⟨j, hj⟩).isLt) _

theorem stateAffine_toLanes {bits : Vector (Expression (F circomPrime)) 1600}
    (h : ∀ i (hi : i < 1600), Affine bits[i]) :
    StateAffine (toLanes bits) := by
  intro j hj i hi
  rw [toLanes_getElem bits j hj, Vector.getElem_ofFn]
  exact h _ (by omega)

theorem costIs_xorLane (a b : Var (fields 64) (F circomPrime)) :
    CostIs (XorLane.xorLane a b) ⟨64, 64⟩ :=
  CostIs.bind (CostIs.witnessVector 64 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_andLane (a b : Var (fields 64) (F circomPrime)) :
    CostIs (AndLane.andLane a b) ⟨64, 64⟩ :=
  CostIs.bind (CostIs.witnessVector 64 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_sub_xorLane (b : Var XorLane.Inputs (F circomPrime)) :
    CostIs (subcircuit XorLane.circuit b) ⟨64, 64⟩ :=
  CostIs.subcircuit (fun n => costIs_xorLane b.a b.b n)

theorem costIs_sub_andLane (b : Var AndLane.Inputs (F circomPrime)) :
    CostIs (subcircuit AndLane.circuit b) ⟨64, 64⟩ :=
  CostIs.subcircuit (fun n => costIs_andLane b.a b.b n)

theorem costIs_xor5Lane (input : Var Xor5Lane.Inputs (F circomPrime)) :
    CostIs (Xor5Lane.main input) ⟨256, 256⟩ :=
  CostIs.bind (costIs_sub_xorLane _) fun _ =>
  CostIs.bind (costIs_sub_xorLane _) fun _ =>
  CostIs.bind (costIs_sub_xorLane _) fun _ =>
  costIs_sub_xorLane _

theorem costIs_sub_xor5Lane (b : Var Xor5Lane.Inputs (F circomPrime)) :
    CostIs (subcircuit Xor5Lane.circuit b) ⟨256, 256⟩ :=
  CostIs.subcircuit (fun n => costIs_xor5Lane b n)

theorem costIs_chiLane (input : Var ChiLane.Inputs (F circomPrime)) :
    CostIs (ChiLane.main input) ⟨128, 128⟩ :=
  CostIs.bind (costIs_sub_andLane _) fun _ => costIs_sub_xorLane _

theorem costIs_sub_chiLane (b : Var ChiLane.Inputs (F circomPrime)) :
    CostIs (subcircuit ChiLane.circuit b) ⟨128, 128⟩ :=
  CostIs.subcircuit (fun n => costIs_chiLane b n)

theorem costIs_thetaC (state : Var KeccakBitState (F circomPrime)) :
    CostIs (ThetaC.main state) ⟨1280, 1280⟩ :=
  CostIs.mapFinRange fun _ n => (costIs_sub_xor5Lane _ : CostIs _ ⟨256, 256⟩) n

theorem costIs_thetaD (c : Var KeccakBitRow (F circomPrime)) :
    CostIs (ThetaD.main c) ⟨320, 320⟩ :=
  CostIs.mapFinRange fun _ n => (costIs_sub_xorLane _ : CostIs _ ⟨64, 64⟩) n

theorem costIs_thetaXor (b : Var ThetaXor.Inputs (F circomPrime)) :
    CostIs (ThetaXor.main b) ⟨1600, 1600⟩ := by
  obtain ⟨state, d⟩ := b
  unfold ThetaXor.main
  exact CostIs.mapFinRange fun i n => costIs_sub_xorLane _ n

theorem costIs_sub_thetaC (b : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit ThetaC.circuit b) ⟨1280, 1280⟩ :=
  CostIs.subcircuit (fun n => costIs_thetaC b n)

theorem costIs_sub_thetaD (b : Var KeccakBitRow (F circomPrime)) :
    CostIs (subcircuit ThetaD.circuit b) ⟨320, 320⟩ :=
  CostIs.subcircuit (fun n => costIs_thetaD b n)

theorem costIs_sub_thetaXor (b : Var ThetaXor.Inputs (F circomPrime)) :
    CostIs (subcircuit ThetaXor.circuit b) ⟨1600, 1600⟩ :=
  CostIs.subcircuit (fun n => costIs_thetaXor b n)

theorem costIs_theta (state : Var KeccakBitState (F circomPrime)) :
    CostIs (Theta.main state) ⟨3200, 3200⟩ :=
  CostIs.bind (costIs_sub_thetaC _) fun _ =>
  CostIs.bind (costIs_sub_thetaD _) fun _ =>
  costIs_sub_thetaXor _

theorem costIs_sub_theta (b : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit Theta.circuit b) ⟨3200, 3200⟩ :=
  CostIs.subcircuit (fun n => costIs_theta b n)

theorem costIs_chi (state : Var KeccakBitState (F circomPrime)) :
    CostIs (Chi.main state) ⟨3200, 3200⟩ :=
  CostIs.mapFinRange fun _ n => (costIs_sub_chiLane _ : CostIs _ ⟨128, 128⟩) n

theorem costIs_sub_chi (b : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit Chi.circuit b) ⟨3200, 3200⟩ :=
  CostIs.subcircuit (fun n => costIs_chi b n)

theorem costIs_round (c : ℕ) (state : Var KeccakBitState (F circomPrime)) :
    CostIs (KeccakRound.main c state) ⟨6400, 6400⟩ :=
  CostIs.bind (costIs_sub_theta _) fun _ =>
  CostIs.bind (costIs_sub_chi _) fun _ =>
  CostIs.pure _

theorem costIs_sub_round (c : ℕ) (hc : c < 2^64) (state : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit (KeccakRound.circuit c hc) state) ⟨6400, 6400⟩ :=
  CostIs.subcircuit (fun n => costIs_round c state n)

-- Keep the trusted R1CS predicates opaque while *applying* the per-gadget
-- certificates: otherwise the unifier evaluates `r1csProducts` on the 64-bit
-- asserted expressions and loops.
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem affineW_subOut_xorLane (b : Var XorLane.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit XorLane.circuit b).output n) := by
  rw [show (subcircuit XorLane.circuit b).output n = varFromOffset (fields 64) n from rfl]
  exact affineW_varFromOffset 64 n

theorem affineW_subOut_andLane (b : Var AndLane.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit AndLane.circuit b).output n) := by
  rw [show (subcircuit AndLane.circuit b).output n = varFromOffset (fields 64) n from rfl]
  exact affineW_varFromOffset 64 n

theorem affineW_subOut_xor5Lane (b : Var Xor5Lane.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Xor5Lane.circuit b).output n) := by
  rw [show (subcircuit Xor5Lane.circuit b).output n = varFromOffset (fields 64) (n + 192) from rfl]
  exact affineW_varFromOffset 64 (n + 192)

theorem affineW_subOut_chiLane (b : Var ChiLane.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit ChiLane.circuit b).output n) := by
  rw [show (subcircuit ChiLane.circuit b).output n = varFromOffset (fields 64) (n + 64) from rfl]
  exact affineW_varFromOffset 64 (n + 64)

theorem r1cs_xorLane (a b : Var (fields 64) (F circomPrime)) (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (XorLane.xorLane a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 64 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_add_mul
            (Affine.sub (Affine.sub (affineW_witnessVector_output 64 _ n j.val j.isLt)
              (ha j.val j.isLt)) (hb j.val j.isLt))
            (Affine.fconst_mul _ (ha j.val j.isLt)) (hb j.val j.isLt)) m)
      (fun _ => IsR1CSCirc.pure _)

theorem r1cs_andLane (a b : Var (fields 64) (F circomPrime)) (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (AndLane.andLane a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 64 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_sub_mul (affineW_witnessVector_output 64 _ n j.val j.isLt)
            (ha j.val j.isLt) (hb j.val j.isLt)) m)
      (fun _ => IsR1CSCirc.pure _)

theorem r1cs_sub_xorLane (b : Var XorLane.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) : IsR1CSCirc (subcircuit XorLane.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_xorLane _ _ ha hb)

theorem r1cs_sub_andLane (b : Var AndLane.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) : IsR1CSCirc (subcircuit AndLane.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_andLane _ _ ha hb)

theorem r1cs_xor5Lane (input : Var Xor5Lane.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hc : AffineW input.c)
    (hd : AffineW input.d) (he : AffineW input.e) :
    IsR1CSCirc (Xor5Lane.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_xorLane _ ha hb) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_xorLane _ (affineW_subOut_xorLane _ _) hc) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_xorLane _ (affineW_subOut_xorLane _ _) hd) fun _ =>
  r1cs_sub_xorLane _ (affineW_subOut_xorLane _ _) he

theorem r1cs_sub_xor5Lane (b : Var Xor5Lane.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) (hd : AffineW b.d)
    (he : AffineW b.e) : IsR1CSCirc (subcircuit Xor5Lane.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_xor5Lane _ ha hb hc hd he)

theorem r1cs_chiLane (input : Var ChiLane.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hc : AffineW input.c) :
    IsR1CSCirc (ChiLane.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_andLane _ (affineW_notBits hb) hc) fun _ =>
  r1cs_sub_xorLane _ ha (affineW_subOut_andLane _ _)

theorem r1cs_sub_chiLane (b : Var ChiLane.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) :
    IsR1CSCirc (subcircuit ChiLane.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_chiLane _ ha hb hc)

theorem rowAffine_subOut_thetaC (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    RowAffine ((subcircuit ThetaC.circuit b).output n) := by
  intro j hj i hi
  rw [show (subcircuit ThetaC.circuit b).output n = ThetaC.circuit.output b n from rfl]
  simp only [ThetaC.circuit, ThetaC.elaborated, circuit_norm]
  exact Affine.var _

theorem rowAffine_subOut_thetaD (b : Var KeccakBitRow (F circomPrime)) (n : ℕ) :
    RowAffine ((subcircuit ThetaD.circuit b).output n) := by
  intro j hj i hi
  rw [show (subcircuit ThetaD.circuit b).output n = ThetaD.circuit.output b n from rfl]
  simp only [ThetaD.circuit, ThetaD.elaborated, circuit_norm]
  exact Affine.var _

theorem stateAffine_subOut_theta (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    StateAffine ((subcircuit Theta.circuit b).output n) := by
  intro j hj i hi
  rw [show (subcircuit Theta.circuit b).output n = Theta.circuit.output b n from rfl]
  simp only [Theta.circuit, Theta.elaborated, circuit_norm]
  exact Affine.var _

theorem r1cs_thetaC (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (ThetaC.main state) :=
  IsR1CSCirc.mapFinRange fun x n =>
    (r1cs_sub_xor5Lane _ (hs _ (by omega)) (hs _ (by omega)) (hs _ (by omega))
      (hs _ (by omega)) (hs _ (by omega))) n

theorem r1cs_thetaD (c : Var KeccakBitRow (F circomPrime)) (hc : RowAffine c) :
    IsR1CSCirc (ThetaD.main c) :=
  IsR1CSCirc.mapFinRange fun x n =>
    (r1cs_sub_xorLane _ (hc _ (by omega)) (affineW_rotl (hc _ (by omega)) 1)) n

theorem r1cs_thetaXor (b : Var ThetaXor.Inputs (F circomPrime))
    (hs : StateAffine b.state) (hd : RowAffine b.d) :
    IsR1CSCirc (ThetaXor.main b) := by
  obtain ⟨state, d⟩ := b
  unfold ThetaXor.main
  exact IsR1CSCirc.mapFinRange fun i n =>
    (r1cs_sub_xorLane _ (hs _ i.isLt) (hd _ (by omega))) n

theorem r1cs_sub_thetaC (b : Var KeccakBitState (F circomPrime)) (hs : StateAffine b) :
    IsR1CSCirc (subcircuit ThetaC.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_thetaC b hs)

theorem r1cs_sub_thetaD (b : Var KeccakBitRow (F circomPrime)) (hc : RowAffine b) :
    IsR1CSCirc (subcircuit ThetaD.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_thetaD b hc)

theorem r1cs_sub_thetaXor (b : Var ThetaXor.Inputs (F circomPrime))
    (hs : StateAffine b.state) (hd : RowAffine b.d) :
    IsR1CSCirc (subcircuit ThetaXor.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_thetaXor b hs hd)

theorem r1cs_theta (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (Theta.main state) :=
  IsR1CSCirc.bind_out (r1cs_sub_thetaC state hs) fun n1 =>
  IsR1CSCirc.bind_out (r1cs_sub_thetaD _ (rowAffine_subOut_thetaC state n1)) fun n2 =>
  r1cs_sub_thetaXor _ hs (rowAffine_subOut_thetaD _ n2)

theorem r1cs_chi (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (Chi.main state) :=
  IsR1CSCirc.mapFinRange fun j n =>
    (r1cs_sub_chiLane _ (hs _ j.isLt) (hs _ (chiSource1 j).isLt) (hs _ (chiSource2 j).isLt)) n

theorem r1cs_sub_theta (b : Var KeccakBitState (F circomPrime)) (hs : StateAffine b) :
    IsR1CSCirc (subcircuit Theta.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_theta b hs)

theorem r1cs_sub_chi (b : Var KeccakBitState (F circomPrime)) (hs : StateAffine b) :
    IsR1CSCirc (subcircuit Chi.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_chi b hs)

/-- The χ subcircuit output is a fresh witness state, hence affine. -/
theorem stateAffine_subOut_chi (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    StateAffine ((subcircuit Chi.circuit b).output n) := by
  intro j hj i hi
  rw [show (subcircuit Chi.circuit b).output n = Chi.circuit.output b n from rfl]
  simp only [Chi.circuit, Chi.elaborated, circuit_norm]
  exact Affine.var _

/-- ι preserves affineness lane by lane (`xorConst` of an affine lane is affine). -/
theorem stateAffine_iotaWire (c : ℕ) {s : Var KeccakBitState (F circomPrime)}
    (hs : StateAffine s) : StateAffine (iotaWire c s) := by
  intro j hj
  rw [show (iotaWire c s)[j] = xorConst (if j = 0 then c else 0) s[j] from by
    rw [iotaWire, Vector.getElem_mapFinRange]]
  exact affineW_xorConst (hs j hj) _

/-- A round output (ι of the χ-output witness state) is affine. -/
theorem stateAffine_subOut_round (c : ℕ) (hc : c < 2^64)
    (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    StateAffine ((subcircuit (KeccakRound.circuit c hc) b).output n) := by
  rw [show (subcircuit (KeccakRound.circuit c hc) b).output n
      = (KeccakRound.circuit c hc).output b n from rfl]
  simp only [KeccakRound.circuit, KeccakRound.elaborated, circuit_norm]
  apply stateAffine_iotaWire
  intro j hj i hi
  rw [Vector.getElem_mapFinRange, Vector.getElem_mapRange]
  exact Affine.var _

/-- Flattening an affine lane state to 1600 bits keeps every bit affine. -/
theorem affine_fromLanes {s : Var KeccakBitState (F circomPrime)} (hs : StateAffine s)
    (i : ℕ) (hi : i < 1600) : Affine (fromLanes s)[i] := by
  rw [fromLanes_getElem s i hi]
  exact hs (i / 64) (by omega) (i % 64) (by omega)

theorem r1cs_round (c : ℕ) (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (KeccakRound.main c state) :=
  IsR1CSCirc.bind_out (r1cs_sub_theta state hs) fun n1 =>
  IsR1CSCirc.bind_out
    (r1cs_sub_chi _ (stateAffine_rhoPiWire (stateAffine_subOut_theta state n1))) fun _ =>
  IsR1CSCirc.pure _

theorem r1cs_sub_round (c : ℕ) (hc : c < 2^64) (state : Var KeccakBitState (F circomPrime))
    (hs : StateAffine state) : IsR1CSCirc (subcircuit (KeccakRound.circuit c hc) state) :=
  IsR1CSCirc.subcircuit (r1cs_round c state hs)

end Cost
end Solution.KeccakF1600
