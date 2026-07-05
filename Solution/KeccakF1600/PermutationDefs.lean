import Solution.KeccakF1600.KeccakRound
import Solution.KeccakF1600.MainTheorems

namespace Solution.KeccakF1600.Permutation

open Challenge.Instances.KeccakF1600.Interface

/-!
The Keccak-f[1600] permutation as a `foldl` over its 24 rounds. The trusted round
value `keccakF 6` is the same `Fin.foldl`; `stateVar`/`acc` describe the symbolic
state entering/leaving each round so the soundness/completeness inductions in the
companion files can chain the per-round `KeccakRound` spec.
-/

/-- Each round has constant local length 6400 (structure-independent of `rc`). -/
lemma keccakRound_localLength (c : ℕ) (hc : c < 2 ^ 64)
    (s : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    (KeccakRound.circuit c hc s).localLength n = 6400 := by
  simp only [circuit_norm, KeccakRound.circuit, KeccakRound.elaborated]

/-- Round constant as a total function of `ℕ` (agrees with `rc` for `i < 24`). -/
def rcN (i : ℕ) : ℕ := if h : i < 24 then rc ⟨i, h⟩ else 0

lemma rcN_eq (i : Fin 24) : rcN i.val = rc i := by
  rw [rcN, dif_pos i.isLt]

/-- The fold body: one Keccak round with the `i`-th round constant. -/
def body (state : Var KeccakBitState (F circomPrime)) (i : Fin 24) :
    Circuit (F circomPrime) (Var KeccakBitState (F circomPrime)) :=
  KeccakRound.circuit (rc i) (rc_lt i) state

/-- The body has constant length, supplied explicitly to avoid the default
`infer_constant_length` reducing a round's length through a symbolic `rc i`. -/
def foldConstant :
    Circuit.ConstantLength (fun (t : Var KeccakBitState (F circomPrime) × Fin 24) => body t.1 t.2) :=
  Circuit.ConstantLength.fromConstantLength' _ (fun acc i i' n => by
    rw [body, body, keccakRound_localLength, keccakRound_localLength])

/-- The permutation: `foldl` of the 24 rounds. -/
def main (state : Var KeccakBitState (F circomPrime)) :
    Circuit (F circomPrime) (Var KeccakBitState (F circomPrime)) :=
  Circuit.foldlRange 24 state body foldConstant

/-- The symbolic state after round `i` of a fold starting at offset `n`: `iotaWire`
of the χ-output witnesses (ι is free wiring). -/
def stateVar (n i : ℕ) : Var KeccakBitState (F circomPrime) :=
  iotaWire (rcN i)
    (Vector.mapFinRange 25 fun j => Vector.mapRange 64 fun z =>
      Expression.var ⟨n + i * 6400 + 3200 + j.val * 128 + 64 + z⟩)

/-- The accumulator entering round `k`. -/
abbrev acc (n : ℕ) (init : Var KeccakBitState (F circomPrime)) (k : Fin 24) :
    Var KeccakBitState (F circomPrime) :=
  Circuit.FoldlM.foldlAcc n (Vector.finRange 24) body init k

/-- Round `k`'s output is `stateVar n k` (input-independent). -/
lemma body_output (init : Var KeccakBitState (F circomPrime)) (n : ℕ) (k : Fin 24) :
    (body (acc n init k) k).output (n + k.val * 6400) = stateVar n k.val := by
  simp only [body, stateVar, circuit_norm, KeccakRound.circuit, KeccakRound.elaborated]
  congr 1
  exact (rcN_eq k).symm

/-- `foldAcc` successor: entering round `k+1` is round `k`'s output. -/
lemma foldAcc_succ (init : Var KeccakBitState (F circomPrime)) (n : ℕ) (k : ℕ) (hk : k + 1 < 24) :
    acc n init ⟨k + 1, hk⟩ =
      (body (acc n init ⟨k, by omega⟩) ⟨k, by omega⟩).output (n + k * 6400) := by
  show Circuit.FoldlM.foldlAcc n (Vector.finRange 24) body init ⟨k + 1, hk⟩ = _
  simp only [Circuit.FoldlM.foldlAcc, Fin.foldl_succ_last, Fin.val_last, Vector.getElem_finRange,
    Fin.val_castSucc, body, keccakRound_localLength]

lemma acc_succ (init : Var KeccakBitState (F circomPrime)) (n : ℕ) (k : ℕ) (hk : k + 1 < 24) :
    acc n init ⟨k + 1, hk⟩ = stateVar n k := by
  rw [foldAcc_succ init n k hk, body_output init n ⟨k, by omega⟩]

lemma acc_zero (init : Var KeccakBitState (F circomPrime)) (n : ℕ) (h : (0 : ℕ) < 24) :
    acc n init ⟨0, h⟩ = init :=
  Circuit.FoldlM.foldlAcc_zero

def Assumptions (state : KeccakBitState (F circomPrime)) : Prop := StateNormalized state

def Spec (state : KeccakBitState (F circomPrime)) (out : KeccakBitState (F circomPrime)) : Prop :=
  StateNormalized out ∧ stateValue out = Specs.Keccak.keccakF 6 (stateValue state)

instance elaborated : ElaboratedCircuit (F circomPrime) KeccakBitState KeccakBitState main := by
  elaborate_circuit_with {
    output _ i0 := stateVar i0 23
  } using by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a; simp only [circuit_norm]
    · intro a n
      simp only [Fin.foldl_succ_last, circuit_norm, stateVar, Fin.val_last,
        Vector.mapRange_eq_mapFinRange]
      congr 1
    · simp only [circuit_norm]
    · simp only [circuit_norm]

/-- The round-value fold (with `rcN`), bridging to the trusted `keccakF 6`. -/
def vfold (X : Vector ℕ 25) (k : ℕ) : Vector ℕ 25 :=
  Fin.foldl k (fun A (j : Fin k) => Specs.Keccak.keccakRound 64 (rcN j.val) A) X

lemma vfold_succ (X : Vector ℕ 25) (k : ℕ) :
    vfold X (k + 1) = Specs.Keccak.keccakRound 64 (rcN k) (vfold X k) := by
  rw [vfold, Fin.foldl_succ_last]
  simp only [Fin.val_last, Fin.val_castSucc, vfold]

lemma vfold_24 (X : Vector ℕ 25) : vfold X 24 = Specs.Keccak.keccakF 6 X := by
  rw [keccakF6_eq_rounds, vfold]
  simp only [Fin.foldl_succ, Fin.foldl_zero, Fin.isValue]
  rfl

end Solution.KeccakF1600.Permutation
