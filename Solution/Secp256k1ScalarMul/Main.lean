import Solution.Secp256k1ScalarMul.ScalarMul
import Solution.Secp256k1ScalarMul.MainTheorems
import Solution.Secp256k1ScalarMul.Cost
import Challenge.Instances.Secp256k1ScalarMul.Interface

/-!
# Top-level circuit — comparator entry point

Adapts the instance Interface (byte-encoded points, SEC1-style big-endian) to
the `ScalarMul` gadget (4×64-bit little-endian limbs) and exports the four
comparator obligations.

The byte→limb packing is a pure affine reindexing (no constraints): the
interface `Assumptions` already say the inputs are bytes, so each packed limb
is a canonical 64-bit value by assumption, not by an in-circuit check. The
output side needs no conversion at all — the gadget already produces
big-endian bytes with a masked infinity flag, matching `Interface.Output`
field for field.

-/

namespace Solution.Secp256k1ScalarMul

open Challenge.Instances.Secp256k1ScalarMul

/-- Pack a big-endian byte-encoded coordinate into 4 little-endian 64-bit
limbs, as affine expressions: big-endian byte `j` sits at little-endian byte
index `31 − j`, and limb `k` collects little-endian bytes `[8k, 8k+8)`. -/
def packCoord (v : Vector (Expression (F Interface.circomPrime)) Interface.coordBytes) :
    Var Emu (F Interface.circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    Fin.foldl bytesPerLimb (fun acc t =>
      acc + v[Interface.coordBytes - 1 - (bytesPerLimb * k.val + t.val)]'(by
          have hk := k.isLt; have ht := t.isLt
          simp only [numLimbs, bytesPerLimb, Interface.coordBytes] at hk ht ⊢
          omega)
        * (((2 ^ (8 * t.val) : ℕ) : F Interface.circomPrime) : Expression (F Interface.circomPrime)))
      0

def main (input : Var Interface.Input (F Interface.circomPrime)) :
    Circuit (F Interface.circomPrime) (Var Interface.Output (F Interface.circomPrime)) := do
  let out ← subcircuit ScalarMul.circuit
    { bits := input.bits, px := packCoord input.px, py := packCoord input.py }
  return { x := out.x, y := out.y, isInf := out.isInf }

instance elaborated :
    ElaboratedCircuit (F Interface.circomPrime) Interface.Input Interface.Output main := by
  elaborate_circuit

/-- Claimed circuit cost (certified in `Cost.lean` / `mainCost` below). -/
@[reducible] def allocations : Nat := 8182144
@[reducible] def constraints : Nat := 8279944

theorem soundness :
    GeneralFormalCircuit.Soundness (F Interface.circomPrime) main
      Interface.Assumptions Interface.Spec := by
  circuit_proof_start
  obtain ⟨h_bits_eq, h_px_eq, h_py_eq⟩ := h_input
  obtain ⟨h_bits, h_px_bytes, h_py_bytes, h_px_lt, h_py_lt, h_curve⟩ := h_assumptions
  rw [show ScalarMul.circuit.Assumptions = ScalarMul.Assumptions from rfl,
    show ScalarMul.circuit.Spec = ScalarMul.Spec from rfl,
    show packCoord = MainTheorems.packCoordE from rfl,
    MainTheorems.eval_packCoordE, MainTheorems.eval_packCoordE,
    h_px_eq, h_py_eq] at h_holds
  simp only [ScalarMul.Assumptions, ScalarMul.Spec] at h_holds
  obtain ⟨h_valid, h_spec⟩ := h_holds
    ⟨fun i => MainTheorems.isBool_of_val_lt_two (h_bits i),
     MainTheorems.pack_valid input_px h_px_bytes h_px_lt,
     MainTheorems.pack_valid input_py h_py_bytes h_py_lt,
     by rw [MainTheorems.decodeFe_pack input_px h_px_bytes,
            MainTheorems.decodeFe_pack input_py h_py_bytes]
        exact h_curve⟩
  simp only [circuit_norm, ScalarMul.circuit, ScalarMul.elaborated] at h_valid h_spec
  refine ⟨?_, ?_⟩
  · rw [MainTheorems.decodeFe_pack input_px h_px_bytes,
        MainTheorems.decodeFe_pack input_py h_py_bytes,
        ← MainTheorems.decodeOutput_eq] at h_spec
    exact ⟨MainTheorems.outputValid_of_valid h_valid, h_spec⟩
  · exact Or.inl rfl

theorem completeness :
    GeneralFormalCircuit.Completeness (F Interface.circomPrime) main
      Interface.ProverAssumptions Interface.ProverSpec := by
  circuit_proof_start
  obtain ⟨h_bits_eq, h_px_eq, h_py_eq⟩ := h_input
  obtain ⟨h_bits, h_px_bytes, h_py_bytes, h_px_lt, h_py_lt, h_curve⟩ := h_assumptions
  rw [show ScalarMul.circuit.Assumptions = ScalarMul.Assumptions from rfl,
    show packCoord = MainTheorems.packCoordE from rfl,
    MainTheorems.eval_packCoordE, MainTheorems.eval_packCoordE,
    h_px_eq, h_py_eq]
  refine ⟨⟨fun i => MainTheorems.isBool_of_val_lt_two (h_bits i),
    MainTheorems.pack_valid input_px h_px_bytes h_px_lt,
    MainTheorems.pack_valid input_py h_py_bytes h_py_lt, ?_⟩, trivial⟩
  rw [MainTheorems.decodeFe_pack input_px h_px_bytes,
      MainTheorems.decodeFe_pack input_py h_py_bytes]
  exact h_curve

section Cost

open Challenge.CostR1CS
open Solution.Secp256k1ScalarMul.Cost

-- Keep the trusted R1CS predicates opaque while *applying* the per-gadget
-- certificates (see `Cost.lean`): otherwise the unifier evaluates
-- `r1csProducts` on the asserted expressions and loops on neutral subterms.
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- Each packed limb is an affine fold `Σ byte·2^(8t)` of the (affine) input
bytes, hence affine. -/
private theorem affineW_packCoord (v : Vector (Expression (F Interface.circomPrime)) Interface.coordBytes)
    (hv : AffineW v) : AffineW (packCoord v) := by
  intro k hk
  unfold packCoord
  rw [Vector.getElem_ofFn]
  refine affine_finFoldl' _ _ Affine.zero fun acc t hacc => ?_
  exact Affine.add hacc (Affine.mul_deg0 (hv _ (by
    simp only [bytesPerLimb, Interface.coordBytes]
    omega)) (degree_const _))

/-- Compositional `CostIs` certificate for the whole circuit: one `ScalarMul`
subcircuit (`packCoord` is a pure reindexing, no operations) and a pure field
re-wrap. -/
private theorem costIs_main (input : Var Interface.Input (F Interface.circomPrime)) :
    CostIs (main input) ⟨allocations, constraints⟩ := by
  rw [show (⟨allocations, constraints⟩ : Count) = scalarMulCost + Count.zero from by decide]
  unfold main
  exact CostIs.bind (costIs_sub_scalarMul _) fun out => CostIs.pure _

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ :=
  fun input => costIs_main input

/-- Top-level single-row R1CS assembly: the packed limbs are affine
combinations of the affine input bytes, so the single `ScalarMul` subcircuit
invocation is single-row R1CS; the returned struct is a pure re-wrap. -/
private theorem isR1CS_main_param (input : Var Interface.Input (F Interface.circomPrime))
    (hbits : AffineW input.bits) (hpx : AffineW input.px) (hpy : AffineW input.py) :
    IsR1CSCirc (main input) := by
  unfold main
  refine IsR1CSCirc.bind_out (isR1CS_sub_scalarMul _ ?_ ?_ ?_) fun nout => ?_
  · exact fun i hi => hbits i hi
  · exact affineW_packCoord _ hpx
  · exact affineW_packCoord _ hpy
  exact IsR1CSCirc.pure _

/-- The circuit's output wires are the `ScalarMul` output wires re-wrapped
field-for-field: reindexed fresh `Mux` witness cells plus the fold
accumulator's flag cell — all affine. -/
private theorem affineOutput_main (input : Var Interface.Input (F Interface.circomPrime)) :
    AffineOutput (main input) := by
  intro n
  unfold main
  rw [Circuit.bind_output_eq, Circuit.pure_output_eq]
  have h := affineOut_sub_scalarMul
    { bits := input.bits, px := packCoord input.px, py := packCoord input.py } n
  exact affineProvable_interfaceOutput h.1 h.2.1 h.2.2

theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput =>
      isR1CS_main_param input (affineInput_components input hinput).1
        (affineInput_components input hinput).2.1
        (affineInput_components input hinput).2.2)
    (fun input _ => affineOutput_main input)

end Cost

-- No `formalCircuit` bundle here: unifying the theorems against the
-- `GeneralFormalCircuit` field types forces a `whnf` of the 256-step fold
-- term and times out, and the comparator only requires `main`, `elaborated`,
-- and the four theorems above.

end Solution.Secp256k1ScalarMul
