import Solution.KeccakF1600.Theorems
import Mathlib.Tactic.IntervalCases

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.KeccakF1600

lemma map_rotate {α β : Type} (g : α → β) (v : Vector α 64) (off : ℕ) :
    (v.rotate off).map g = (v.map g).rotate off := by
  ext i hi
  rw [Vector.getElem_map, Vector.getElem_rotate, Vector.getElem_rotate, Vector.getElem_map]

/-- `eval` of a Keccak state is the double lane/bit map. Bridges the
subcircuit-generated `eval env X` to the explicit-map form the wiring lemmas
below are stated in. -/
lemma eval_keccakState (env : Environment (F p)) (X : Var KeccakBitState (F p)) :
    eval env X = Vector.map (Vector.map (Expression.eval env)) X := by
  apply Vector.ext
  intro j hj
  rw [← getElem_eval_vector (α := fields 64) env X j hj, CircuitType.eval_var_fields,
    Vector.getElem_map]

/-- `rhoPiWire` lane by lane. -/
lemma rhoPiWire_getElem {T : Type} (s : Vector (Vector T 64) 25) (j : ℕ) (hj : j < 25) :
    (rhoPiWire s)[j] =
      rotl (Specs.Keccak.rhoOffsets[(piSource ⟨j, hj⟩).val]) s[(piSource ⟨j, hj⟩).val] :=
  Vector.getElem_ofFn ..

/-- Evaluation commutes with the ρ/π wiring. -/
lemma eval_rhoPiWire_vec (env : Environment (F p)) (v : Var KeccakBitState (F p)) :
    Vector.map (Vector.map (Expression.eval env)) (rhoPiWire v)
      = rhoPiWire (Vector.map (Vector.map (Expression.eval env)) v) := by
  ext j hj i hi
  rw [Vector.getElem_map, rhoPiWire_getElem _ j hj, rhoPiWire_getElem _ j hj]
  show ((rotl _ v[(piSource ⟨j, hj⟩).val]).map (Expression.eval env))[i] = _
  rw [show (rotl (Specs.Keccak.rhoOffsets[(piSource ⟨j, hj⟩).val])
        (Vector.map (Vector.map (Expression.eval env)) v)[(piSource ⟨j, hj⟩).val]) =
      rotl (Specs.Keccak.rhoOffsets[(piSource ⟨j, hj⟩).val])
        (v[(piSource ⟨j, hj⟩).val].map (Expression.eval env)) from by
    rw [Vector.getElem_map]]
  rw [show ∀ (w : Vector (Expression (F p)) 64) k,
      rotl k (w.map (Expression.eval env)) = (rotl k w).map (Expression.eval env) from
    fun w k => (map_rotate _ w _).symm]

/-- The ρ/π wiring of a normalized state is normalized. -/
lemma StateNormalized_rhoPiWire (s : KeccakBitState (F p)) (hs : StateNormalized s) :
    StateNormalized (rhoPiWire s) := by
  intro j
  rw [rhoPiWire_getElem s j.val j.isLt]
  exact Normalized_rotl _ _ (hs (piSource j))

/-- The value of the ρ/π wiring is `rhoPiSpec` of the value. -/
lemma stateValue_rhoPiWire (s : KeccakBitState (F p)) (hs : StateNormalized s) :
    stateValue (rhoPiWire s) = rhoPiSpec (stateValue s) := by
  apply Vector.ext
  intro j hj
  rw [show (stateValue (rhoPiWire s))[j] = valueBits (rhoPiWire s)[j] from Vector.getElem_map ..,
      rhoPiWire_getElem s j hj,
      valueBits_rotl _ _ (hs (piSource ⟨j, hj⟩))]
  rw [show (rhoPiSpec (stateValue s))[j] =
      Specs.Keccak.rotLeft 64 (stateValue s)[(piSource ⟨j, hj⟩).val]
        (Specs.Keccak.rhoOffsets[(piSource ⟨j, hj⟩).val]) from Vector.getElem_ofFn ..]
  rw [show (stateValue s)[(piSource ⟨j, hj⟩).val] = valueBits s[(piSource ⟨j, hj⟩).val] from
    Vector.getElem_map ..]

/-- The per-lane ι map: lane 0 gets the round constant, other lanes are
unchanged (`xorConst 0 = id`). -/
lemma stateValue_iotaMap (rc : ℕ) (hrc : rc < 2^64) (s : KeccakBitState (F p))
    (hs : StateNormalized s) :
    stateValue (iotaWire rc s)
      = iotaSpec rc (stateValue s) := by
  apply Vector.ext
  intro i hi
  rw [show (stateValue (iotaWire rc s))[i]
      = valueBits (xorConst (if i = 0 then rc else 0) s[i]) from by
    rw [show stateValue _ = Vector.map valueBits _ from rfl, Vector.getElem_map, iotaWire,
      Vector.getElem_mapFinRange],
    show iotaSpec rc (stateValue s) = (stateValue s).set 0 ((stateValue s)[0] ^^^ rc) from rfl]
  by_cases hi0 : i = 0
  · subst hi0
    simp only [reduceIte, Vector.getElem_set]
    rw [valueBits_xorConst rc hrc s[0] (hs 0), Nat.xor_comm,
      show (stateValue s)[0] = valueBits s[0] from Vector.getElem_map ..]
  · rw [show (if i = 0 then rc else 0) = 0 from by simp [hi0],
      show ((stateValue s).set 0 ((stateValue s)[0] ^^^ rc))[i] = (stateValue s)[i] from by
        simp [Ne.symm hi0],
      show (stateValue s)[i] = valueBits s[i] from Vector.getElem_map ..]
    rw [valueBits_xorConst 0 (by norm_num) s[i] (hs ⟨i, hi⟩)]
    simp

/-- The per-lane ι map preserves normalization. -/
lemma StateNormalized_iotaMap (rc : ℕ) (s : KeccakBitState (F p)) (hs : StateNormalized s) :
    StateNormalized (iotaWire rc s) := by
  intro i
  rw [show (iotaWire rc s)[i.val]
      = xorConst (if i.val = 0 then rc else 0) s[i.val] from by
    rw [iotaWire, Vector.getElem_mapFinRange]]
  exact Normalized_xorConst _ s[i.val] (hs i)

/-- `Vector.map` distributes over the per-lane ι map. -/
lemma map_iotaWire (env : Environment (F p)) (v : Var KeccakBitState (F p)) (rc : ℕ) :
    Vector.map (Vector.map (Expression.eval env)) (iotaWire rc v)
      = iotaWire rc (Vector.map (Vector.map (Expression.eval env)) v) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map, iotaWire, iotaWire, Vector.getElem_mapFinRange,
    Vector.getElem_mapFinRange, eval_xorConst_vec, Vector.getElem_map]

set_option maxRecDepth 4000 in
/-- θ decomposes into the three θ step functions. -/
lemma theta_eq (A : Vector ℕ 25) :
    Specs.Keccak.theta 64 A = thetaXorSpec A (thetaDSpec (thetaCSpec A)) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [Specs.Keccak.theta, Specs.Keccak.ofLanes, Specs.Keccak.lane,
      thetaXorSpec, thetaDSpec, thetaCSpec]

set_option maxRecDepth 4000 in
/-- π ∘ ρ is the combined ρ/π wiring. -/
lemma rhoPi_eq (B : Vector ℕ 25) :
    Specs.Keccak.pi (Specs.Keccak.rho 64 B) = rhoPiSpec B := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [Specs.Keccak.pi, Specs.Keccak.rho, Specs.Keccak.ofLanes, Specs.Keccak.lane,
      rhoPiSpec, piSource, Specs.Keccak.rhoOffsets]

set_option maxRecDepth 4000 in
/-- χ matches the per-lane `chiSpec`. -/
lemma chi_eq (C : Vector ℕ 25) :
    Specs.Keccak.chi 64 C = chiSpec C := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [Specs.Keccak.chi, Specs.Keccak.ofLanes, Specs.Keccak.lane,
      chiSpec, chiSource1, chiSource2]

/-- The trusted round function decomposes through the per-gadget ℕ-level step
functions. -/
lemma keccakRound_decompose (rc : ℕ) (A : Vector ℕ 25) :
    Specs.Keccak.keccakRound 64 rc A =
      iotaSpec rc (chiSpec (rhoPiSpec (thetaXorSpec A (thetaDSpec (thetaCSpec A))))) := by
  rw [Specs.Keccak.keccakRound, theta_eq, rhoPi_eq, chi_eq]
  rfl

end Solution.KeccakF1600
end
