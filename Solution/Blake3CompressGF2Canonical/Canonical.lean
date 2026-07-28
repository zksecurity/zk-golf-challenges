import Solution.Blake3CompressGF2Canonical.Cost

/-!
# Ordered identity-C composition

Every composite boundary is pinned. Consequently, the only nontrivial
affineness obligations are the pure word/state selections feeding the next
canonical subcircuit.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.Instances.Blake3CompressGF2Canonical.Interface.Blake3Bits
open Challenge.F2Bits
open Challenge.CostR1CS

theorem affineW_xorWord {x y : Word (Expression (F p2))}
    (hx : AffineW x) (hy : AffineW y) :
    AffineW (Vector.ofFn fun i : Fin 32 => x[i.val] + y[i.val]) := by
  intro i hi
  rw [Vector.getElem_ofFn]
  exact Affine.add (hx i hi) (hy i hi)

theorem affineW_rotRight {x : Word (Expression (F p2))}
    (hx : AffineW x) (n : ℕ) :
    AffineW (Vector.ofFn fun i : Fin 32 =>
      x[(i.val + n) % 32]'(Nat.mod_lt _ (by norm_num))) := by
  intro i hi
  rw [Vector.getElem_ofFn]
  exact hx _ (Nat.mod_lt _ (by norm_num))

theorem affineW_stateWord {v : State (Expression (F p2))}
    (hv : AffineW v) (i : Fin 16) :
    AffineW (Vector.ofFn fun j : Fin 32 =>
      v[32 * i.val + j.val]'(by omega)) := by
  intro j hj
  rw [Vector.getElem_ofFn]
  exact hv _ (by omega)

theorem affineW_setWord {v : State (Expression (F p2))}
    (hv : AffineW v) (i : Fin 16) {x : Word (Expression (F p2))}
    (hx : AffineW x) :
    AffineW (Vector.ofFn fun j : Fin 512 =>
      if _h : j.val / 32 = i.val then
        x[j.val % 32]'(Nat.mod_lt _ (by norm_num))
      else
        v[j.val]) := by
  intro j hj
  rw [Vector.getElem_ofFn]
  split
  · exact hx _ (Nat.mod_lt _ (by norm_num))
  · exact hv j hj

theorem affineW_writeQuad {v : State (Expression (F p2))}
    (hv : AffineW v) (a b c d : Fin 16) {q : Var Quad (F p2)}
    (ha : AffineW q.a) (hb : AffineW q.b) (hc : AffineW q.c) (hd : AffineW q.d) :
    AffineW (writeQuad v a b c d q) := by
  unfold writeQuad
  apply affineW_setWord
  · apply affineW_setWord
    · apply affineW_setWord
      · exact affineW_setWord hv a ha
      · exact hb
    · exact hc
  · exact hd

theorem affineW_permuteState {v : State (Expression (F p2))}
    (hv : AffineW v) :
    AffineW (Vector.ofFn fun i : Fin 512 =>
      v[32 * (messagePermutation[i.val / 32]'(by omega)).val + i.val % 32]'(by
        have hp := (messagePermutation[i.val / 32]'(by omega)).isLt
        omega)) := by
  intro i hi
  rw [Vector.getElem_ofFn]
  have hp := (messagePermutation[i / 32]'(by omega)).isLt
  exact hv _ (by omega)

theorem affineW_finalizeState {v initial : State (Expression (F p2))}
    (hv : AffineW v) (hi : AffineW initial) :
    AffineW (Vector.ofFn fun i : Fin 512 =>
      if h : i.val < 256 then
        v[i.val] + v[i.val + 256]'(by omega)
      else
        v[i.val] + initial[i.val - 256]'(by omega)) := by
  intro i hidx
  rw [Vector.getElem_ofFn]
  split
  · exact Affine.add (hv i hidx) (hv _ (by omega))
  · exact Affine.add (hv i hidx) (hi _ (by omega))

theorem affineW_initialStateBits {bits : Vector (Expression (F p2)) 896}
    (hbits : AffineW bits) :
    AffineW (Vector.ofFn fun i : Fin 512 =>
      if hcv : i.val / 32 < 8 then
        bits[32 * (i.val / 32) + i.val % 32]'(by omega)
      else if hiv : i.val / 32 < 12 then
        atWord (constWord (Specs.Blake3.iv[i.val / 32 - 8]'(by omega))) i.val
      else
        bits[32 * (i.val / 32 + 12) + i.val % 32]'(by omega)) := by
  intro i hi
  rw [Vector.getElem_ofFn]
  split
  · exact hbits _ (by omega)
  · split
    · unfold constWord
      unfold atWord
      rw [Vector.getElem_ofFn]
      split
      · exact Affine.one
      · exact Affine.zero
    · exact hbits _ (by omega)

theorem affineW_initialBlockBits {bits : Vector (Expression (F p2)) 896}
    (hbits : AffineW bits) :
    AffineW (Vector.ofFn fun i : Fin 512 =>
      bits[32 * (i.val / 32 + 8) + i.val % 32]'(by omega)) := by
  intro i hi
  rw [Vector.getElem_ofFn]
  exact hbits _ (by omega)

theorem affineW_input_bits {input : Var Input (F p2)}
    (hinput : AffineProvable input) : AffineW input.bits := by
  intro i hi
  simp only [inputBits] at hi
  have hsz : size Input = 896 := rfl
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz, hi] using
    hinput i (by omega)

theorem affineW_quad_a {q : Var Quad (F p2)} (hq : AffineProvable q) :
    AffineW q.a := by
  have hflat : AffineW (q.a ++ (q.b ++ (q.c ++ q.d))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hq i hi
  exact hflat.left_of_append

theorem affineW_quad_b {q : Var Quad (F p2)} (hq : AffineProvable q) :
    AffineW q.b := by
  have hflat : AffineW (q.a ++ (q.b ++ (q.c ++ q.d))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hq i hi
  exact hflat.right_of_append.left_of_append

theorem affineW_quad_c {q : Var Quad (F p2)} (hq : AffineProvable q) :
    AffineW q.c := by
  have hflat : AffineW (q.a ++ (q.b ++ (q.c ++ q.d))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hq i hi
  exact hflat.right_of_append.right_of_append.left_of_append

theorem affineW_quad_d {q : Var Quad (F p2)} (hq : AffineProvable q) :
    AffineW q.d := by
  have hflat : AffineW (q.a ++ (q.b ++ (q.c ++ q.d))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hq i hi
  exact hflat.right_of_append.right_of_append.right_of_append

theorem affineW_config_state {x : Var Config (F p2)} (hx : AffineProvable x) :
    AffineW x.state := by
  have hflat : AffineW (x.state ++ x.block) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hx i hi
  exact hflat.left_of_append

theorem affineW_config_block {x : Var Config (F p2)} (hx : AffineProvable x) :
    AffineW x.block := by
  have hflat : AffineW (x.state ++ x.block) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hx i hi
  exact hflat.right_of_append

namespace Add32Canon

theorem affineW_subOut (b : Var Add32.Inputs (F p2))
    (hx : AffineW b.x) (hy : AffineW b.y) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n) := by
  intro j hj
  simp only [circuit_norm, subcircuit, circuit, elaborated, Vector.getElem_ofFn]
  refine Affine.add (Affine.add (hx _ (Nat.mod_lt _ (by norm_num)))
    (hy _ (Nat.mod_lt _ (by norm_num)))) ?_
  unfold Add32.carryE
  split
  · exact Affine.zero
  · exact affineW_mapRange_var _ _ (Nat.mod_lt _ (by norm_num))

end Add32Canon

namespace Pin32Canon

theorem affineW_subOut (b : Var (fields 32) (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

end Pin32Canon

namespace PinStateCanon

theorem affineW_subOut (b : Var (fields 512) (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

end PinStateCanon

namespace AddExact

theorem isCidentity_main (b : Var Add32.Inputs (F p2))
    (hx : AffineW b.x) (hy : AffineW b.y) :
    IsCidCirc (main b) := by
  unfold main
  refine IsCidCirc.bind_out (Add32Canon.isCidentity_sub b hx hy)
    (Add32Canon.balanced_sub b) fun n => ?_
  exact Pin32Canon.isCidentity_sub _ (Add32Canon.affineW_subOut b hx hy n)

theorem isCidentity_sub (b : Var Add32.Inputs (F p2))
    (hx : AffineW b.x) (hy : AffineW b.y) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_main b hx hy).ops

theorem affineW_subOut (b : Var Add32.Inputs (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

end AddExact

namespace XorRotateExact

theorem isCidentity_main (n : ℕ) (b : Var Inputs (F p2))
    (hx : AffineW b.x) (hy : AffineW b.y) :
    IsCidCirc (main n b) := by
  apply Pin32Canon.isCidentity_sub
  unfold rotRight atWord xorWord
  exact affineW_rotRight (affineW_xorWord hx hy) n

theorem isCidentity_sub (n : ℕ) (b : Var Inputs (F p2))
    (hx : AffineW b.x) (hy : AffineW b.y) :
    IsCidCirc (subcircuit (circuit n) b) :=
  IsCidCirc.subcircuit (isCidentity_main n b hx hy).ops

theorem affineW_subOut (n : ℕ) (b : Var Inputs (F p2)) (k : ℕ) :
    AffineW ((subcircuit (circuit n) b).output k) := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

end XorRotateExact

namespace PinQuadExact

theorem isCidentity_main (b : Var Quad (F p2))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) (hd : AffineW b.d) :
    IsCidCirc (main b) := by
  unfold main
  refine IsCidCirc.bind_out (Pin32Canon.isCidentity_sub b.a ha)
    (Pin32Canon.balanced_sub b.a) fun _ => ?_
  refine IsCidCirc.bind_out (Pin32Canon.isCidentity_sub b.b hb)
    (Pin32Canon.balanced_sub b.b) fun _ => ?_
  refine IsCidCirc.bind_out (Pin32Canon.isCidentity_sub b.c hc)
    (Pin32Canon.balanced_sub b.c) fun _ => ?_
  refine IsCidCirc.bind_out (Pin32Canon.isCidentity_sub b.d hd)
    (Pin32Canon.balanced_sub b.d) fun _ => ?_
  exact IsCidCirc.pure _

theorem isCidentity_sub (b : Var Quad (F p2))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) (hd : AffineW b.d) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_main b ha hb hc hd).ops

theorem affineW_subOut_a (b : Var Quad (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n).a := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

theorem affineW_subOut_b (b : Var Quad (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n).b := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

theorem affineW_subOut_c (b : Var Quad (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n).c := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

theorem affineW_subOut_d (b : Var Quad (F p2)) (n : ℕ) :
    AffineW ((subcircuit circuit b).output n).d := by
  simp only [circuit_norm, subcircuit, circuit, elaborated]
  exact affineW_mapRange_var _

end PinQuadExact

namespace GFirst

theorem isCidentity_main (b : Var GInputs (F p2))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c)
    (hd : AffineW b.d) (hmx : AffineW b.mx) :
    IsCidCirc (main b) := by
  unfold main
  refine IsCidCirc.bind_out (AddExact.isCidentity_sub _ ha hb)
    (AddExact.balanced_sub _) fun na0 => ?_
  have ha0 := AddExact.affineW_subOut (⟨b.a, b.b⟩ : Var Add32.Inputs (F p2)) na0
  refine IsCidCirc.bind_out (AddExact.isCidentity_sub _ ha0 hmx)
    (AddExact.balanced_sub _) fun nav => ?_
  let avInput : Var Add32.Inputs (F p2) :=
    ⟨(subcircuit AddExact.circuit ⟨b.a, b.b⟩).output na0, b.mx⟩
  have hav := AddExact.affineW_subOut avInput nav
  refine IsCidCirc.bind_out (XorRotateExact.isCidentity_sub 16 _ hd hav)
    (XorRotateExact.balanced_sub 16 _) fun ndv => ?_
  let dvInput : Var XorRotateExact.Inputs (F p2) :=
    ⟨b.d, (subcircuit AddExact.circuit avInput).output nav⟩
  have hdv := XorRotateExact.affineW_subOut 16 dvInput ndv
  refine IsCidCirc.bind_out (AddExact.isCidentity_sub _ hc hdv)
    (AddExact.balanced_sub _) fun ncv => ?_
  let cvInput : Var Add32.Inputs (F p2) :=
    ⟨b.c, (subcircuit (XorRotateExact.circuit 16) dvInput).output ndv⟩
  have hcv := AddExact.affineW_subOut cvInput ncv
  refine IsCidCirc.bind_out (XorRotateExact.isCidentity_sub 12 _ hb hcv)
    (XorRotateExact.balanced_sub 12 _) fun nbv => ?_
  let bvInput : Var XorRotateExact.Inputs (F p2) :=
    ⟨b.b, (subcircuit AddExact.circuit cvInput).output ncv⟩
  have hbv := XorRotateExact.affineW_subOut 12 bvInput nbv
  exact PinQuadExact.isCidentity_sub _ hav hbv hcv hdv

theorem isCidentity_sub (b : Var GInputs (F p2))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c)
    (hd : AffineW b.d) (hmx : AffineW b.mx) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_main b ha hb hc hd hmx).ops

theorem output_a_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).a =
      (varFromOffset (fields 32) (n + 346) : Var (fields 32) (F p2)) := rfl

theorem output_b_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).b =
      (varFromOffset (fields 32) (n + 346 + 32) : Var (fields 32) (F p2)) := rfl

theorem output_c_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).c =
      (varFromOffset (fields 32) (n + 346 + 32 + 32) : Var (fields 32) (F p2)) := rfl

theorem output_d_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).d =
      (varFromOffset (fields 32) (n + 346 + 32 + 32 + 32) :
        Var (fields 32) (F p2)) := rfl

end GFirst

namespace GSecond

theorem isCidentity_main (b : Var GInputs (F p2))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c)
    (hd : AffineW b.d) (hmy : AffineW b.my) :
    IsCidCirc (main b) := by
  unfold main
  refine IsCidCirc.bind_out (AddExact.isCidentity_sub _ ha hb)
    (AddExact.balanced_sub _) fun na0 => ?_
  have ha0 := AddExact.affineW_subOut (⟨b.a, b.b⟩ : Var Add32.Inputs (F p2)) na0
  refine IsCidCirc.bind_out (AddExact.isCidentity_sub _ ha0 hmy)
    (AddExact.balanced_sub _) fun nav => ?_
  let avInput : Var Add32.Inputs (F p2) :=
    ⟨(subcircuit AddExact.circuit ⟨b.a, b.b⟩).output na0, b.my⟩
  have hav := AddExact.affineW_subOut avInput nav
  refine IsCidCirc.bind_out (XorRotateExact.isCidentity_sub 8 _ hd hav)
    (XorRotateExact.balanced_sub 8 _) fun ndv => ?_
  let dvInput : Var XorRotateExact.Inputs (F p2) :=
    ⟨b.d, (subcircuit AddExact.circuit avInput).output nav⟩
  have hdv := XorRotateExact.affineW_subOut 8 dvInput ndv
  refine IsCidCirc.bind_out (AddExact.isCidentity_sub _ hc hdv)
    (AddExact.balanced_sub _) fun ncv => ?_
  let cvInput : Var Add32.Inputs (F p2) :=
    ⟨b.c, (subcircuit (XorRotateExact.circuit 8) dvInput).output ndv⟩
  have hcv := AddExact.affineW_subOut cvInput ncv
  refine IsCidCirc.bind_out (XorRotateExact.isCidentity_sub 7 _ hb hcv)
    (XorRotateExact.balanced_sub 7 _) fun nbv => ?_
  let bvInput : Var XorRotateExact.Inputs (F p2) :=
    ⟨b.b, (subcircuit AddExact.circuit cvInput).output ncv⟩
  have hbv := XorRotateExact.affineW_subOut 7 bvInput nbv
  exact PinQuadExact.isCidentity_sub _ hav hbv hcv hdv

theorem isCidentity_sub (b : Var GInputs (F p2))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c)
    (hd : AffineW b.d) (hmy : AffineW b.my) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_main b ha hb hc hd hmy).ops

theorem output_a_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).a =
      (varFromOffset (fields 32) (n + 346) : Var (fields 32) (F p2)) := rfl

theorem output_b_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).b =
      (varFromOffset (fields 32) (n + 346 + 32) : Var (fields 32) (F p2)) := rfl

theorem output_c_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).c =
      (varFromOffset (fields 32) (n + 346 + 32 + 32) : Var (fields 32) (F p2)) := rfl

theorem output_d_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).d =
      (varFromOffset (fields 32) (n + 346 + 32 + 32 + 32) :
        Var (fields 32) (F p2)) := rfl

end GSecond

namespace G

theorem isCidentity_main (b : Var GInputs (F p2))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c)
    (hd : AffineW b.d) (hmx : AffineW b.mx) (hmy : AffineW b.my) :
    IsCidCirc (main b) := by
  unfold main
  refine IsCidCirc.bind_out (GFirst.isCidentity_sub b ha hb hc hd hmx)
    (GFirst.balanced_sub b) fun nfirst => ?_
  rw [GFirst.output_a_eq, GFirst.output_b_eq, GFirst.output_c_eq,
    GFirst.output_d_eq]
  exact GSecond.isCidentity_sub _
    (affineW_varFromOffset _ _) (affineW_varFromOffset _ _)
    (affineW_varFromOffset _ _) (affineW_varFromOffset _ _) hmy

theorem isCidentity_sub (b : Var GInputs (F p2))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c)
    (hd : AffineW b.d) (hmx : AffineW b.mx) (hmy : AffineW b.my) :
    IsCidCirc (subcircuit circuit b) :=
  IsCidCirc.subcircuit (isCidentity_main b ha hb hc hd hmx hmy).ops

theorem output_a_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).a =
      (varFromOffset (fields 32) (n + 474 + 346) : Var (fields 32) (F p2)) := rfl

theorem output_b_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).b =
      (varFromOffset (fields 32) (n + 474 + 346 + 32) :
        Var (fields 32) (F p2)) := rfl

theorem output_c_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).c =
      (varFromOffset (fields 32) (n + 474 + 346 + 32 + 32) :
        Var (fields 32) (F p2)) := rfl

theorem output_d_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).d =
      (varFromOffset (fields 32) (n + 474 + 346 + 32 + 32 + 32) :
        Var (fields 32) (F p2)) := rfl

end G

namespace ApplyG

theorem isCidentity_main (a b c d : Fin 16) (x : Var Inputs (F p2))
    (hs : AffineW x.state) (hmx : AffineW x.mx) (hmy : AffineW x.my) :
    IsCidCirc (main a b c d x) := by
  unfold main
  refine IsCidCirc.bind_out (G.isCidentity_sub _ (affineW_stateWord hs a)
    (affineW_stateWord hs b) (affineW_stateWord hs c) (affineW_stateWord hs d)
    hmx hmy) (G.balanced_sub _) fun nq => ?_
  exact PinStateCanon.isCidentity_sub _
    (affineW_writeQuad hs a b c d
      (by rw [G.output_a_eq]; exact affineW_varFromOffset _ _)
      (by rw [G.output_b_eq]; exact affineW_varFromOffset _ _)
      (by rw [G.output_c_eq]; exact affineW_varFromOffset _ _)
      (by rw [G.output_d_eq]; exact affineW_varFromOffset _ _))

theorem isCidentity_sub (a b c d : Fin 16) (x : Var Inputs (F p2))
    (hs : AffineW x.state) (hmx : AffineW x.mx) (hmy : AffineW x.my) :
    IsCidCirc (subcircuit (circuit a b c d) x) :=
  IsCidCirc.subcircuit (isCidentity_main a b c d x hs hmx hmy).ops

theorem output_eq (a b c d : Fin 16) (x : Var Inputs (F p2)) (n : ℕ) :
    (subcircuit (circuit a b c d) x).output n =
      (varFromOffset (fields 512) (n + 948) : Var (fields 512) (F p2)) := rfl

end ApplyG

namespace Round.Pair

theorem isCidentity_main
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (x : Var Round.Inputs (F p2))
    (hs : AffineW x.state) (hm : AffineW x.block) :
    IsCidCirc (main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 x) := by
  unfold main
  refine IsCidCirc.bind_out (ApplyG.isCidentity_sub a0 b0 c0 d0 _
    hs (affineW_stateWord hm mx0) (affineW_stateWord hm my0))
    (ApplyG.balanced_sub a0 b0 c0 d0 _) fun ns0 => ?_
  rw [ApplyG.output_eq]
  exact ApplyG.isCidentity_sub a1 b1 c1 d1 _
    (affineW_varFromOffset _ _)
    (affineW_stateWord hm mx1) (affineW_stateWord hm my1)

theorem isCidentity_sub
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (x : Var Round.Inputs (F p2))
    (hs : AffineW x.state) (hm : AffineW x.block) :
    IsCidCirc
      (subcircuit (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) x) :=
  IsCidCirc.subcircuit
    (isCidentity_main a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 x hs hm).ops

theorem output_eq
    (a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1 : Fin 16)
    (x : Var Round.Inputs (F p2)) (n : ℕ) :
    (subcircuit
      (circuit a0 b0 c0 d0 mx0 my0 a1 b1 c1 d1 mx1 my1) x).output n =
      (varFromOffset (fields 512) (n + 1460 + 948) :
        Var (fields 512) (F p2)) := rfl

end Round.Pair

namespace Round.Columns

theorem isCidentity_main (x : Var Round.Inputs (F p2))
    (hs : AffineW x.state) (hm : AffineW x.block) :
    IsCidCirc (main x) := by
  unfold main
  refine IsCidCirc.bind_out
    (Round.Pair.isCidentity_sub 0 4 8 12 0 1 1 5 9 13 2 3 x hs hm)
    (Round.Pair.balanced_sub 0 4 8 12 0 1 1 5 9 13 2 3 x) fun ns01 => ?_
  rw [Round.Pair.output_eq]
  exact Round.Pair.isCidentity_sub 2 6 10 14 4 5 3 7 11 15 6 7 _
    (affineW_varFromOffset _ _) hm

theorem isCidentity_sub (x : Var Round.Inputs (F p2))
    (hs : AffineW x.state) (hm : AffineW x.block) :
    IsCidCirc (subcircuit circuit x) :=
  IsCidCirc.subcircuit (isCidentity_main x hs hm).ops

theorem output_eq (x : Var Round.Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit x).output n =
      (varFromOffset (fields 512) (n + 2920 + 1460 + 948) :
        Var (fields 512) (F p2)) := rfl

end Round.Columns

namespace Round.Diagonals

theorem isCidentity_main (x : Var Round.Inputs (F p2))
    (hs : AffineW x.state) (hm : AffineW x.block) :
    IsCidCirc (main x) := by
  unfold main
  refine IsCidCirc.bind_out
    (Round.Pair.isCidentity_sub 0 5 10 15 8 9 1 6 11 12 10 11 x hs hm)
    (Round.Pair.balanced_sub 0 5 10 15 8 9 1 6 11 12 10 11 x) fun ns45 => ?_
  rw [Round.Pair.output_eq]
  exact Round.Pair.isCidentity_sub 2 7 8 13 12 13 3 4 9 14 14 15 _
    (affineW_varFromOffset _ _) hm

theorem isCidentity_sub (x : Var Round.Inputs (F p2))
    (hs : AffineW x.state) (hm : AffineW x.block) :
    IsCidCirc (subcircuit circuit x) :=
  IsCidCirc.subcircuit (isCidentity_main x hs hm).ops

theorem output_eq (x : Var Round.Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit x).output n =
      (varFromOffset (fields 512) (n + 2920 + 1460 + 948) :
        Var (fields 512) (F p2)) := rfl

end Round.Diagonals

namespace Round

theorem isCidentity_main (x : Var Inputs (F p2))
    (hs : AffineW x.state) (hm : AffineW x.block) :
    IsCidCirc (main x) := by
  unfold main
  refine IsCidCirc.bind_out (Columns.isCidentity_sub x hs hm)
    (Columns.balanced_sub x) fun ncolumns => ?_
  rw [Columns.output_eq]
  exact Diagonals.isCidentity_sub _ (affineW_varFromOffset _ _) hm

theorem isCidentity_sub (x : Var Inputs (F p2))
    (hs : AffineW x.state) (hm : AffineW x.block) :
    IsCidCirc (subcircuit circuit x) :=
  IsCidCirc.subcircuit (isCidentity_main x hs hm).ops

theorem output_eq (x : Var Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit x).output n =
      (varFromOffset (fields 512) (n + 5840 + 2920 + 1460 + 948) :
        Var (fields 512) (F p2)) := rfl

end Round

namespace Prepare

theorem isCidentity_main (input : Var Input (F p2)) (hbits : AffineW input.bits) :
    IsCidCirc (main input) := by
  unfold main
  refine IsCidCirc.bind_out (PinStateCanon.isCidentity_sub _ ?_)
    (PinStateCanon.balanced_sub _) fun _ => ?_
  · intro i hi
    simp only [initialState, splitWords, atWord, Vector.getElem_ofFn]
    rw [Vector.getElem_ofFn]
    split
    · apply hbits
    · split
      · unfold constWord
        rw [Vector.getElem_ofFn]
        split
        · exact Affine.one
        · exact Affine.zero
      · apply hbits
  refine IsCidCirc.bind_out (PinStateCanon.isCidentity_sub _ ?_)
    (PinStateCanon.balanced_sub _) fun _ => ?_
  · intro i hi
    simp only [initialBlock, splitWords, atWord, Vector.getElem_ofFn]
    rw [Vector.getElem_ofFn]
    apply hbits
  exact IsCidCirc.pure _

theorem isCidentity_sub (input : Var Input (F p2)) (hbits : AffineW input.bits) :
    IsCidCirc (subcircuit circuit input) :=
  IsCidCirc.subcircuit (isCidentity_main input hbits).ops

theorem output_state_eq (input : Var Input (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).state =
      (varFromOffset (fields 512) n : Var (fields 512) (F p2)) := rfl

theorem output_block_eq (input : Var Input (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).block =
      (varFromOffset (fields 512) (n + 512) : Var (fields 512) (F p2)) := rfl

end Prepare

namespace Step

theorem isCidentity_main (input : Var Config (F p2))
    (hs : AffineW input.state) (hm : AffineW input.block) :
    IsCidCirc (main input) := by
  unfold main
  refine IsCidCirc.bind_out (Round.isCidentity_sub _ hs hm)
    (Round.balanced_sub _) fun _ => ?_
  refine IsCidCirc.bind_out (PinStateCanon.isCidentity_sub _ ?_)
    (PinStateCanon.balanced_sub _) fun _ => ?_
  · intro i hi
    simp only [permuteState, flattenWords, permute, splitWords,
      Vector.getElem_ofFn]
    rw [Vector.getElem_ofFn]
    have hp := (messagePermutation[i / 32]'(by omega)).isLt
    exact hm _ (by omega)
  exact IsCidCirc.pure _

theorem isCidentity_sub (input : Var Config (F p2))
    (hs : AffineW input.state) (hm : AffineW input.block) :
    IsCidCirc (subcircuit circuit input) :=
  IsCidCirc.subcircuit (isCidentity_main input hs hm).ops

theorem output_state_eq (input : Var Config (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).state =
      (varFromOffset (fields 512) (n + 5840 + 2920 + 1460 + 948) :
        Var (fields 512) (F p2)) := rfl

theorem output_block_eq (input : Var Config (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).block =
      (varFromOffset (fields 512) (n + 11680) :
        Var (fields 512) (F p2)) := rfl

end Step

namespace Steps2

theorem isCidentity_main (input : Var Config (F p2))
    (hs : AffineW input.state) (hm : AffineW input.block) :
    IsCidCirc (main input) := by
  unfold main
  refine IsCidCirc.bind_out (Step.isCidentity_sub input hs hm)
    (Step.balanced_sub input) fun nx1 => ?_
  exact Step.isCidentity_sub _
    (by rw [Step.output_state_eq]; exact affineW_varFromOffset _ _)
    (by rw [Step.output_block_eq]; exact affineW_varFromOffset _ _)

theorem isCidentity_sub (input : Var Config (F p2))
    (hs : AffineW input.state) (hm : AffineW input.block) :
    IsCidCirc (subcircuit circuit input) :=
  IsCidCirc.subcircuit (isCidentity_main input hs hm).ops

theorem output_state_eq (input : Var Config (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).state =
      (varFromOffset (fields 512) (n + 12192 + 11168) :
        Var (fields 512) (F p2)) := rfl

theorem output_block_eq (input : Var Config (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).block =
      (varFromOffset (fields 512) (n + 12192 + 11680) :
        Var (fields 512) (F p2)) := rfl

end Steps2

namespace Steps4

theorem isCidentity_main (input : Var Config (F p2))
    (hs : AffineW input.state) (hm : AffineW input.block) :
    IsCidCirc (main input) := by
  unfold main
  refine IsCidCirc.bind_out (Steps2.isCidentity_sub input hs hm)
    (Steps2.balanced_sub input) fun nx2 => ?_
  exact Steps2.isCidentity_sub _
    (by rw [Steps2.output_state_eq]; exact affineW_varFromOffset _ _)
    (by rw [Steps2.output_block_eq]; exact affineW_varFromOffset _ _)

theorem isCidentity_sub (input : Var Config (F p2))
    (hs : AffineW input.state) (hm : AffineW input.block) :
    IsCidCirc (subcircuit circuit input) :=
  IsCidCirc.subcircuit (isCidentity_main input hs hm).ops

theorem output_state_eq (input : Var Config (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).state =
      (varFromOffset (fields 512) (n + 24384 + 23360) :
        Var (fields 512) (F p2)) := rfl

theorem output_block_eq (input : Var Config (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).block =
      (varFromOffset (fields 512) (n + 24384 + 23872) :
        Var (fields 512) (F p2)) := rfl

end Steps4

namespace Steps7

theorem isCidentity_main (input : Var Config (F p2))
    (hs : AffineW input.state) (hm : AffineW input.block) :
    IsCidCirc (main input) := by
  unfold main
  refine IsCidCirc.bind_out (Steps4.isCidentity_sub input hs hm)
    (Steps4.balanced_sub input) fun nx4 => ?_
  refine IsCidCirc.bind_out
    (Steps2.isCidentity_sub _
      (by rw [Steps4.output_state_eq]; exact affineW_varFromOffset _ _)
      (by rw [Steps4.output_block_eq]; exact affineW_varFromOffset _ _))
    (Steps2.balanced_sub _) fun nx6 => ?_
  exact Step.isCidentity_sub _
    (by rw [Steps2.output_state_eq]; exact affineW_varFromOffset _ _)
    (by rw [Steps2.output_block_eq]; exact affineW_varFromOffset _ _)

theorem isCidentity_sub (input : Var Config (F p2))
    (hs : AffineW input.state) (hm : AffineW input.block) :
    IsCidCirc (subcircuit circuit input) :=
  IsCidCirc.subcircuit (isCidentity_main input hs hm).ops

theorem output_state_eq (input : Var Config (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).state =
      (varFromOffset (fields 512) (n + 48768 + 24384 + 11168) :
        Var (fields 512) (F p2)) := rfl

theorem output_block_eq (input : Var Config (F p2)) (n : ℕ) :
    ((subcircuit circuit input).output n).block =
      (varFromOffset (fields 512) (n + 48768 + 24384 + 11680) :
        Var (fields 512) (F p2)) := rfl

end Steps7

namespace Finalize

theorem isCidentity_main (input : Var Inputs (F p2))
    (hs : AffineW input.state) (hi : AffineW input.initial) :
    IsCidCirc (main input) := by
  apply PinStateCanon.isCidentity_sub
  unfold finalizeState
  exact affineW_finalizeState hs hi

theorem isCidentity_sub (input : Var Inputs (F p2))
    (hs : AffineW input.state) (hi : AffineW input.initial) :
    IsCidCirc (subcircuit circuit input) :=
  IsCidCirc.subcircuit (isCidentity_main input hs hi).ops

theorem output_eq (input : Var Inputs (F p2)) (n : ℕ) :
    (subcircuit circuit input).output n =
      (varFromOffset (fields 512) n : Var (fields 512) (F p2)) := rfl

end Finalize

theorem output_bits_eq (input : Var Input (F p2)) (n : ℕ) :
    ((main input).output n).bits =
      (varFromOffset (fields 512) (n + 1024 + 85344) :
        Var (fields 512) (F p2)) := rfl

theorem isR1CS_CidentityInternal : Challenge.CostR1CS.isR1CS_Cidentity main :=
  isR1CS_Cidentity_of_IsCidCirc
    (fun input hinput => by
      have hbits := affineW_input_bits hinput
      unfold main
      refine IsCidCirc.bind_out (Prepare.isCidentity_sub input hbits)
        (Prepare.balanced_sub input) fun nprepared => ?_
      refine IsCidCirc.bind_out
        (Steps7.isCidentity_sub _
          (by rw [Prepare.output_state_eq]; exact affineW_varFromOffset _ _)
          (by rw [Prepare.output_block_eq]; exact affineW_varFromOffset _ _))
        (Steps7.balanced_sub _) fun nresult => ?_
      refine IsCidCirc.bind_out
        (Finalize.isCidentity_sub _
          (by rw [Steps7.output_state_eq]; exact affineW_varFromOffset _ _)
          (by rw [Prepare.output_state_eq]; exact affineW_varFromOffset _ _))
        (Finalize.balanced_sub _) fun _ => ?_
      exact IsCidCirc.pure _)
    (fun input _ n => by
      intro i hi
      have hi512 : i < 512 := by
        have hsz : size Output = 512 := rfl
        omega
      rw [show (toElements (M := Output) ((main input).output n))[i] =
        ((main input).output n).bits[i]'hi512 from rfl, output_bits_eq]
      exact affineW_varFromOffset 512 _ i hi512)

end Solution.Blake3CompressGF2Canonical
