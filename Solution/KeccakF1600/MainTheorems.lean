import Challenge.Instances.KeccakF1600.Interface
import Solution.KeccakF1600.KeccakRound

namespace Solution.KeccakF1600

open Challenge.Instances.KeccakF1600.Interface

instance : Fact (circomPrime > 2) := ⟨by norm_num [circomPrime]⟩

/-- A field element with a boolean canonical representative is 0 or 1. -/
lemma bit_of_val_lt_two {x : F circomPrime} (h : x.val < 2) : x = 0 ∨ x = 1 := by
  have hcase : x.val = 0 ∨ x.val = 1 := by omega
  rcases hcase with h0 | h1
  · left; exact (ZMod.val_eq_zero x).mp h0
  · right
    have hh : ((x.val : ℕ) : F circomPrime) = x := by rw [ZMod.natCast_val, ZMod.cast_id]
    rw [← hh, h1]; simp

/-- The round constant of round `i`, reduced to 64 bits like
`Specs.Keccak.keccakF` does. -/
def rc (i : Fin 24) : ℕ := Specs.Keccak.roundConstants[i.val] % 2^64

lemma rc_lt (i : Fin 24) : rc i < 2^64 := Nat.mod_lt _ (Nat.two_pow_pos 64)

set_option maxRecDepth 4000 in
/-- `Specs.Keccak.keccakF 6` is 24 explicit rounds. -/
lemma keccakF6_eq_rounds (A : Vector ℕ 25) :
    Specs.Keccak.keccakF 6 A =
      Specs.Keccak.keccakRound 64 (rc 23) (Specs.Keccak.keccakRound 64 (rc 22)
      (Specs.Keccak.keccakRound 64 (rc 21) (Specs.Keccak.keccakRound 64 (rc 20)
      (Specs.Keccak.keccakRound 64 (rc 19) (Specs.Keccak.keccakRound 64 (rc 18)
      (Specs.Keccak.keccakRound 64 (rc 17) (Specs.Keccak.keccakRound 64 (rc 16)
      (Specs.Keccak.keccakRound 64 (rc 15) (Specs.Keccak.keccakRound 64 (rc 14)
      (Specs.Keccak.keccakRound 64 (rc 13) (Specs.Keccak.keccakRound 64 (rc 12)
      (Specs.Keccak.keccakRound 64 (rc 11) (Specs.Keccak.keccakRound 64 (rc 10)
      (Specs.Keccak.keccakRound 64 (rc 9) (Specs.Keccak.keccakRound 64 (rc 8)
      (Specs.Keccak.keccakRound 64 (rc 7) (Specs.Keccak.keccakRound 64 (rc 6)
      (Specs.Keccak.keccakRound 64 (rc 5) (Specs.Keccak.keccakRound 64 (rc 4)
      (Specs.Keccak.keccakRound 64 (rc 3) (Specs.Keccak.keccakRound 64 (rc 2)
      (Specs.Keccak.keccakRound 64 (rc 1) (Specs.Keccak.keccakRound 64 (rc 0)
        A)))))))))))))))))))))))  := by
  show Fin.foldl 24 (fun A i => Specs.Keccak.keccakRound 64 (rc i) A) A = _
  simp only [Fin.foldl_succ, Fin.foldl_zero]
  rfl

/-- A `Fin.foldl` accumulating `+ f i` is the finite sum. -/
lemma finFoldl_add_eq_sum (n : ℕ) (f : Fin n → ℕ) :
    Fin.foldl n (fun acc i => acc + f i) 0 = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    congr 1
    exact ih (fun i => f i.castSucc)

/-- `toLanes` lane `i` is the vector of bits `64·i + z`. -/
lemma toLanes_getElem {T : Type} (bits : Vector T 1600) (i : ℕ) (hi : i < 25) :
    (toLanes bits)[i] = Vector.ofFn (fun (w : Fin 64) => bits[64 * i + w.val]'(by omega)) := by
  rw [toLanes, Vector.getElem_ofFn]

/-- The lanes of `toLanes bits` have the values `Specs.Keccak.bitsToState` of
the bit values. -/
lemma stateValue_toLanes (bits : Vector (F circomPrime) 1600) :
    stateValue (toLanes bits) = Specs.Keccak.bitsToState (bits.map ZMod.val) := by
  apply Vector.ext
  intro i hi
  rw [show (stateValue (toLanes bits))[i] = valueBits (toLanes bits)[i] from
    Vector.getElem_map ..,
    show (Specs.Keccak.bitsToState (bits.map ZMod.val))[i] =
      Fin.foldl 64 (fun acc (z : Fin 64) =>
        acc + (bits.map ZMod.val)[64 * i + z.val] * 2 ^ z.val) 0 from
    Vector.getElem_ofFn ..,
    finFoldl_add_eq_sum 64 (fun z => (bits.map ZMod.val)[64 * i + z.val] * 2 ^ z.val)]
  unfold valueBits
  apply Finset.sum_congr rfl
  intro z _
  rw [toLanes_getElem bits i hi,
    show (Vector.ofFn fun w : Fin 64 => bits[64 * i + w.val]'(by omega))[z] = bits[64 * i + z.val]
      from by rw [Fin.getElem_fin, Vector.getElem_ofFn],
    show (Vector.map ZMod.val bits)[64 * i + z.val] = ZMod.val bits[64 * i + z.val]
      from Vector.getElem_map ..]

/-- The lanes of `toLanes` of a bit string are normalized. -/
lemma StateNormalized_toLanes (bits : Vector (F circomPrime) 1600)
    (h : ∀ i : Fin 1600, (bits[i] : F circomPrime).val < 2) :
    StateNormalized (toLanes bits) := by
  intro i z
  rw [toLanes_getElem bits i.val i.isLt]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact bit_of_val_lt_two (h ⟨64 * i.val + z.val, by omega⟩)

/-- Bit extraction from `valueBits` of a normalized lane. -/
lemma valueBits_div_mod (x : fields 64 (F circomPrime)) (hx : Normalized x) (z : Fin 64) :
    valueBits x / 2 ^ z.val % 2 = (x[z] : F circomPrime).val := by
  rw [← Nat.toNat_testBit, valueBits_testBit x hx.val_bool z]
  rcases hx.val_bool z with h | h <;> rw [h] <;> simp

/-- `fromLanes` bit `j` is bit `j % 64` of lane `j / 64`. -/
lemma fromLanes_getElem {T : Type} (s : Vector (Vector T 64) 25) (j : ℕ) (hj : j < 1600) :
    (fromLanes s)[j] = (s[j / 64]'(by omega))[j % 64]'(by omega) := by
  rw [fromLanes, Vector.getElem_ofFn]

/-- The bit values of `fromLanes` are `Specs.Keccak.stateToBits` of the lane
values. -/
lemma fieldElems_fromLanes (s : KeccakBitState (F circomPrime)) (hs : StateNormalized s) :
    (fromLanes s).map ZMod.val = Specs.Keccak.stateToBits (stateValue s) := by
  apply Vector.ext
  intro j hj
  rw [show ((fromLanes s).map ZMod.val)[j] = ZMod.val ((fromLanes s)[j]) from Vector.getElem_map ..,
    fromLanes_getElem s j hj,
    show (Specs.Keccak.stateToBits (stateValue s))[j] =
      (stateValue s)[j / 64]'(by omega) / 2 ^ (j % 64) % 2 from Vector.getElem_ofFn ..,
    show (stateValue s)[j / 64]'(by omega) = valueBits (s[j / 64]'(by omega)) from
      Vector.getElem_map ..]
  exact (valueBits_div_mod (s[j / 64]'(by omega)) (hs ⟨j / 64, by omega⟩)
    ⟨j % 64, by omega⟩).symm

/-- Evaluation commutes with `toLanes`. -/
lemma eval_toLanes_vec (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) 1600) :
    Vector.map (Vector.map (Expression.eval env)) (toLanes bits)
      = toLanes (bits.map (Expression.eval env)) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map, toLanes_getElem bits i hi, toLanes_getElem _ i hi]
  apply Vector.ext
  intro z hz
  rw [Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_ofFn, Vector.getElem_map]

/-- Evaluation commutes with `fromLanes`. -/
lemma eval_fromLanes_vec (env : Environment (F circomPrime))
    (s : Vector (Vector (Expression (F circomPrime)) 64) 25) :
    Vector.map (Expression.eval env) (fromLanes s)
      = fromLanes (Vector.map (Vector.map (Expression.eval env)) s) := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, fromLanes_getElem s j hj, fromLanes_getElem _ j hj,
    Vector.getElem_map, Vector.getElem_map]

end Solution.KeccakF1600
