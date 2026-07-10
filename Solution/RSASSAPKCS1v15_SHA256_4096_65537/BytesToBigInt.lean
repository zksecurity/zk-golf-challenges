import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ByteBlock

/-!
# `BytesToBigInt` subcircuit — 512 big-endian bytes → `BigInt 34`

A self-contained `FormalCircuit` converting a `modulusBytesLen`-byte big-endian
octet string into the `BigInt 34` little-endian-limb representation of the
integer it denotes (`os2ip`).

It witnesses all `4096` bits at once (one clean `varFromOffset`, global bit `i` =
bit `i % 8` of big-endian byte `511 − i / 8`, exactly the layout `packLimbs`
expects), then discharges booleanity + byte/bit consistency by running 16
`ByteBlock` assertions, one per contiguous 32-byte block (block `b` covers global
bits `[256·(15−b), 256·(16−b))`). Finally it packs the witnessed bits with
`packLimbs`. Factoring the bulk constraints into `ByteBlock` keeps the direct
operation count tiny (1 witness + 16 assertions), so the `FormalCircuit` bundle
elaborates, while `packLimbs` still runs over the clean witnessed bits.

Used twice by `main` — once for the modulus, once for the signature.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace BytesToBigInt

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open Specs.RSASSAPKCS1v15

/-- Bit-witness generator reading from the byte vector: bit `i` is bit `i % 8` of
big-endian byte `511 - i / 8`. -/
def bitsWitness (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : Vector (F circomPrime) totalBits :=
  Vector.ofFn fun i : Fin totalBits =>
    let j : ℕ := 511 - i.val / 8
    let t : ℕ := i.val % 8
    let byteVal : ℕ :=
      if h : j < modulusBytesLen then
        (Expression.eval env.toEnvironment (bytes[j]'h)).val
      else 0
    ((byteVal / 2 ^ t % 2 : ℕ) : F circomPrime)

/-- The 32-byte slice of block `b` (`b = 0` most significant): global bytes
`[32·b, 32·b+32)`. -/
def byteSlice (bytes : Var (fields modulusBytesLen) (F circomPrime)) (b : Fin 16) :
    Vector (Expression (F circomPrime)) 32 :=
  Vector.ofFn fun dj : Fin 32 =>
    bytes[32 * b.val + dj.val]'(by
      have := b.isLt; have := dj.isLt
      show 32 * b.val + dj.val < 512; omega)

/-- The 256-bit slice of block `b`: global bits `[256·(15−b), 256·(16−b))`. -/
def bitSlice (allBits : Vector (Expression (F circomPrime)) totalBits) (b : Fin 16) :
    Vector (Expression (F circomPrime)) 256 :=
  Vector.ofFn fun l : Fin 256 =>
    allBits[256 * (15 - b.val) + l.val]'(by have := b.isLt; have := l.isLt; simp only [totalBits]; omega)

/-- The `main` circuit: witness the 4096 bits, check each 32-byte block with a
`ByteBlock` assertion, and pack the witnessed bits into a `BigInt 34`. -/
def main (bytes : Var (fields modulusBytesLen) (F circomPrime)) :
    Circuit (F circomPrime) (Var (BigInt numLimbs) (F circomPrime)) := do
  let allBits ← witnessVector totalBits (bitsWitness bytes)
  Circuit.forEach (Vector.finRange 16)
    (fun b => ByteBlock.circuit { bytes := byteSlice bytes b, bits := bitSlice allBits b })
    (_constant := ⟨0, by
      intro _ _
      simp only [circuit_norm, ByteBlock.circuit, ByteBlock.elaborated]⟩)
  return Bytes.packLimbs allBits

instance elaborated :
    ElaboratedCircuit (F circomPrime) (fields modulusBytesLen) (BigInt numLimbs) main where
  localLength _ := totalBits
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, ByteBlock.circuit, ByteBlock.elaborated]
  output _ offset := Bytes.packLimbs (varFromOffset (fields totalBits) offset)
  output_eq := by
    intro input offset
    simp only [main, circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith [main, circuit_norm, ByteBlock.circuit, ByteBlock.elaborated]
  channelsLawful := by
    intro input offset
    simp +arith [main, circuit_norm, ByteBlock.circuit, ByteBlock.elaborated]

/-- Precondition: the input is a genuine octet string (each byte `< 256`). -/
def Assumptions (bytes : (fields modulusBytesLen) (F circomPrime)) : Prop :=
  IsOctetString (fieldBytesToNat bytes)

/-- Postcondition: the output is a normalized big integer denoting `os2ip bytes`. -/
def Spec (bytes : (fields modulusBytesLen) (F circomPrime))
    (out : BigInt numLimbs (F circomPrime)) : Prop :=
  out.Normalized limbBits ∧
    out.value limbBits = os2ip (fieldBytesToNat bytes)

/-! ## Index bridges between the per-block `ByteBlock` slices and the global
`packLimbs` bit/byte vectors. -/

/-- The evaluated `bitSlice` of block `b` at local index `l` equals the evaluated
global bit at `256·(15−b) + l`. -/
theorem bitSlice_map_getElem
    (env : Environment (F circomPrime))
    (allBits : Vector (Expression (F circomPrime)) totalBits) (b : Fin 16)
    (l : ℕ) (hl : l < 256) :
    (Vector.map (Expression.eval env) (bitSlice allBits b))[l]'(by simpa using hl)
      = Expression.eval env (allBits[256 * (15 - b.val) + l]'(by
          have := b.isLt; simp only [totalBits]; omega)) := by
  rw [Vector.getElem_map, bitSlice, Vector.getElem_ofFn]

/-- The evaluated `byteSlice` of block `b` at local byte `dj` equals the evaluated
global byte `32·b + dj`. -/
theorem byteSlice_map_getElem
    (env : Environment (F circomPrime))
    (input_var : Vector (Expression (F circomPrime)) modulusBytesLen) (b : Fin 16)
    (dj : ℕ) (hdj : dj < 32) :
    (Vector.map (Expression.eval env) (byteSlice input_var b))[dj]'(by simpa using hdj)
      = Expression.eval env (input_var[32 * b.val + dj]'(by
          have := b.isLt; show 32 * b.val + dj < 512; omega)) := by
  rw [Vector.getElem_map, byteSlice, Vector.getElem_ofFn]

set_option linter.constructorNameAsVariable false in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  set allBits := (Vector.mapRange totalBits fun i ↦ var (F := F circomPrime) { index := i₀ + i })
    with hAllBits
  -- Each big-endian byte `< 256` (from the octet-string assumption), so each
  -- `ByteBlock.Assumptions` is met, discharging it to a `ByteBlock.Spec`.
  have hbytes_lt : ∀ (j : ℕ) (hj : j < 512),
      (Expression.eval env (input_var[j]'hj)).val < 256 := by
    intro j hj
    have := h_assumptions ⟨j, hj⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map, ← h_input] at this
    simpa using this
  have hspec : ∀ b : Fin 16, ByteBlock.Spec
      { bytes := Vector.map (Expression.eval env) (byteSlice input_var b),
        bits := Vector.map (Expression.eval env) (bitSlice allBits b) } := by
    intro b
    apply h_holds b
    -- ByteBlock.Assumptions: each byte of the slice `< 256`.
    intro dj
    rw [byteSlice_map_getElem env input_var b dj.val dj.isLt]
    exact hbytes_lt (32 * b.val + dj.val) (by have := b.isLt; have := dj.isLt; omega)
  -- Unfold `ByteBlock.circuit.Spec` in `hspec`.
  simp only [ByteBlock.Spec] at hspec
  -- Booleanity of every global bit.
  have hbool : BytesLemmas.BitsBool env allBits := by
    intro p hp
    -- block `b = 15 - p / 256`, local index `l = p % 256`.
    have hb : 15 - p / 256 < 16 := by omega
    have hl : p % 256 < 256 := Nat.mod_lt _ (by norm_num)
    have := (hspec ⟨15 - p / 256, hb⟩).1 ⟨p % 256, hl⟩
    rw [bitSlice_map_getElem env allBits ⟨15 - p / 256, hb⟩ (p % 256) hl] at this
    have hidx : 256 * (15 - (15 - p / 256)) + p % 256 = p := by
      have h256 : p / 256 ≤ 15 := by simp only [totalBits] at hp; omega
      have heq : 15 - (15 - p / 256) = p / 256 := by omega
      rw [heq]; exact Nat.div_add_mod p 256
    rw [getElem_congr_idx hidx] at this
    exact this
  -- Byte-consistency: each global byte equals its bit recomposition.
  have hbyte : BytesLemmas.ByteConsistent env input_var allBits := by
    intro j hj
    -- block `b = j / 32`, local byte `dj = j % 32`.
    have hb : j / 32 < 16 := by omega
    have hdj : j % 32 < 32 := Nat.mod_lt _ (by norm_num)
    have hbyteeq := (hspec ⟨j / 32, hb⟩).2 ⟨j % 32, hdj⟩
    rw [byteSlice_map_getElem env input_var ⟨j / 32, hb⟩ (j % 32) hdj] at hbyteeq
    rw [getElem_congr_idx (show 32 * (j / 32) + j % 32 = j from by omega)] at hbyteeq
    rw [hbyteeq]
    apply Finset.sum_congr rfl
    intro t _
    rw [bitSlice_map_getElem env allBits ⟨j / 32, hb⟩
      (digestBitIndex (j % 32) t.val) (by have := t.isLt; simp only [digestBitIndex]; omega)]
    -- bridge: `256·(15 − j/32) + digestBitIndex (j%32) t = bitIndexOfByte j t`.
    rw [getElem_congr_idx (show
        256 * (15 - j / 32) + digestBitIndex (j % 32) t.val = bitIndexOfByte j t.val from by
      simp only [digestBitIndex, bitIndexOfByte]
      have : 32 * (j / 32) + j % 32 = j := by omega
      omega)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- Normalized.
    exact BytesLemmas.packLimbs_normalized env allBits hbool
  · -- value = os2ip.
    rw [BytesLemmas.packLimbs_value_eq_os2ip env input_var allBits hbool hbyte]
    congr 1
    rw [fieldBytesToNat, ← h_input, fieldBytesToNat]
  · -- channel requirements: `ByteBlock` is channel-free.
    intro b
    left
    rfl

set_option linter.constructorNameAsVariable false in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [main, Assumptions]
  set allBits := (Vector.mapRange totalBits fun i ↦ var (F := F circomPrime) { index := i₀ + i })
    with hAllBits
  have hmb : (modulusBytesLen : ℕ) = 512 := rfl
  -- The witnessed bit `p` evaluates to the `2^(p%8)` bit of big-endian byte
  -- `511 − p/8`.
  have hbiteval : ∀ (p : ℕ) (hp : p < totalBits),
      Expression.eval env.toEnvironment (allBits[p]'hp)
        = (((Expression.eval env.toEnvironment (input_var[511 - p / 8]'(by omega))).val
              / 2 ^ (p % 8) % 2 : ℕ) : F circomPrime) := by
    intro p hp
    rw [hAllBits, Vector.getElem_mapRange]
    show env.get (i₀ + p) = _
    rw [h_env ⟨p, hp⟩]
    simp only [bitsWitness, Vector.getElem_ofFn]
    rw [dif_pos (show 511 - p / 8 < modulusBytesLen by omega)]
  -- Booleanity: every witnessed bit is `< 2`.
  have hbool : BytesLemmas.BitsBool env.toEnvironment allBits := by
    intro p hp
    rw [hbiteval p hp, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by norm_num))
  -- Bytes are `< 256` (octet-string assumption, transported through `h_input`).
  have hbytes_lt : ∀ (j : ℕ) (hj : j < 512),
      (Expression.eval env.toEnvironment (input_var[j]'hj)).val < 256 := by
    intro j hj
    have := h_assumptions ⟨j, hj⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map, ← h_input] at this
    simpa using this
  -- Byte-consistency: each big-endian byte equals its bit recomposition.  Bit
  -- `bitIndexOfByte j t = 8·(511−j)+t` is the `2^t` bit of byte `j`, so the sum
  -- recovers the byte (binary decomposition, `byte < 256 = 2^8`).
  have hbyte : BytesLemmas.ByteConsistent env.toEnvironment input_var allBits := by
    intro j hj
    have hrecon : ∀ t : Fin 8,
        (Expression.eval env.toEnvironment
            (allBits[bitIndexOfByte j t.val]'(by
              have := t.isLt; simp only [bitIndexOfByte, totalBits]; omega))).val
          = (Expression.eval env.toEnvironment (input_var[j]'hj)).val / 2 ^ t.val % 2 := by
      intro t
      have hp : bitIndexOfByte j t.val < totalBits := by
        have := t.isLt; simp only [bitIndexOfByte, totalBits]; omega
      rw [hbiteval (bitIndexOfByte j t.val) hp, ZMod.val_natCast]
      have hidx1 : (bitIndexOfByte j t.val) / 8 = 511 - j := by
        simp only [bitIndexOfByte]; have := t.isLt; omega
      have hidx2 : (bitIndexOfByte j t.val) % 8 = t.val := by
        simp only [bitIndexOfByte]; have := t.isLt; omega
      rw [getElem_congr_idx (show 511 - bitIndexOfByte j t.val / 8 = j from by
            rw [hidx1]; omega), hidx2]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
        (le_of_lt (lt_trans (by norm_num) BytesLemmas.two_pow_256_lt_circomPrime)))
    rw [← BytesLemmas.sum_bits_eq (Expression.eval env.toEnvironment (input_var[j]'hj)).val 8
      (lt_of_lt_of_le (hbytes_lt j hj) (by norm_num)),
      ← Fin.sum_univ_eq_sum_range
        (fun t => (Expression.eval env.toEnvironment (input_var[j]'hj)).val / 2 ^ t % 2 * 2 ^ t) 8]
    apply Finset.sum_congr rfl
    intro t _
    rw [hrecon t]
  -- Discharge each block: `Assumptions` (bytes `< 256`) and `Spec` (boolean +
  -- byte recomposition), using the same index bridges as soundness.
  intro b
  refine ⟨?_, ?_, ?_⟩
  · -- ByteBlock.Assumptions.
    intro dj
    rw [byteSlice_map_getElem env.toEnvironment input_var b dj.val dj.isLt]
    exact hbytes_lt (32 * b.val + dj.val) (by have := b.isLt; have := dj.isLt; omega)
  · -- ByteBlock.Spec, part 1: bits boolean.
    intro l
    rw [bitSlice_map_getElem env.toEnvironment allBits b l.val l.isLt]
    exact hbool _ (by have := b.isLt; have := l.isLt; simp only [totalBits]; omega)
  · -- ByteBlock.Spec, part 2: byte = Σ bits · 2^t.
    intro dj
    rw [byteSlice_map_getElem env.toEnvironment input_var b dj.val dj.isLt]
    have hjlt : 32 * b.val + dj.val < 512 := by have := b.isLt; have := dj.isLt; omega
    rw [hbyte (32 * b.val + dj.val) hjlt]
    apply Finset.sum_congr rfl
    intro t _
    rw [bitSlice_map_getElem env.toEnvironment allBits b
      (digestBitIndex dj.val t.val) (by have := dj.isLt; have := t.isLt; simp only [digestBitIndex]; omega)]
    -- bridge: `256·(15−b) + digestBitIndex dj t = bitIndexOfByte (32b+dj) t`.
    rw [getElem_congr_idx (show
        256 * (15 - b.val) + digestBitIndex dj.val t.val
          = bitIndexOfByte (32 * b.val + dj.val) t.val from by
      have := b.isLt; have := dj.isLt
      simp only [digestBitIndex, bitIndexOfByte]; omega)]

/-- The `BytesToBigInt` formal circuit. -/
def circuit : FormalCircuit (F circomPrime) (fields modulusBytesLen) (BigInt numLimbs) := {
  main, elaborated, Assumptions, Spec, soundness, completeness
}

attribute [local irreducible] ByteBlock.circuit

open Challenge.Utils.ComputableWitnessLemmas in
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessVector_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    FormalAssertion.assertion_structuralComputableWitnesses_iff,
    and_true]
  refine ⟨?wbits, ?blocks⟩
  case wbits =>
    intro _ h_input
    have hbytes : ∀ (j : ℕ) (hj : j < modulusBytesLen),
        Expression.eval env.toEnvironment (input[j]'hj) = Expression.eval env'.toEnvironment (input[j]'hj) := by
      intro j hj
      have := congrArg (fun v : Vector (F circomPrime) modulusBytesLen => v[j]'hj) h_input
      simpa only [circuit_norm, Vector.getElem_map] using this
    simp only [bitsWitness]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    by_cases hj : 511 - i / 8 < modulusBytesLen
    · rw [dif_pos hj, dif_pos hj, hbytes _ hj]
    · rw [dif_neg hj, dif_neg hj]
  case blocks =>
    intro i
    have hlen : (witnessVector totalBits (bitsWitness input)).localLength offset = totalBits := by
      simp only [circuit_norm]
    set allBits := (witnessVector totalBits (bitsWitness input)).output offset with hAllBits
    set bs := byteSlice input (Vector.finRange 16)[i.val] with hbs
    set bt := bitSlice allBits (Vector.finRange 16)[i.val] with hbt
    have halen : (assertion ByteBlock.circuit
        { bytes := byteSlice input default,
          bits := bitSlice allBits default }).localLength = 0 := by
      simp only [circuit_norm, ByteBlock.circuit, ByteBlock.elaborated]
    rw [hlen, halen, Nat.mul_zero, Nat.add_zero]
    have hcond : ∀ (k : ℕ) (e1 e2 : ProverEnvironment (F circomPrime)),
        offset + totalBits ≤ k → e1.AgreesBelow k e2 →
        eval e1 input = eval e2 input →
        eval e1 ({ bytes := bs, bits := bt } : Var ByteBlock.Inputs (F circomPrime))
          = eval e2 ({ bytes := bs, bits := bt } : Var ByteBlock.Inputs (F circomPrime)) := by
      intro k e1 e2 hle h_agree h_input
      have hbytes : ∀ (j : ℕ) (hj : j < modulusBytesLen),
          Expression.eval e1.toEnvironment (input[j]'hj) = Expression.eval e2.toEnvironment (input[j]'hj) := by
        intro j hj
        have := congrArg (fun v : Vector (F circomPrime) modulusBytesLen => v[j]'hj) h_input
        simpa only [circuit_norm, Vector.getElem_map] using this
      have hbits : ∀ (q : ℕ) (hq : q < totalBits),
          Expression.eval e1.toEnvironment (allBits[q]'hq) = Expression.eval e2.toEnvironment (allBits[q]'hq) := by
        intro q hq
        have hvar : allBits[q]'hq = var (F := F circomPrime) { index := offset + q } := by
          rw [hAllBits]; simp only [circuit_norm]
        rw [hvar]
        simp only [Expression.eval]
        exact h_agree (offset + q) (by omega)
      have hbs_map : Vector.map (Expression.eval e1.toEnvironment) bs
          = Vector.map (Expression.eval e2.toEnvironment) bs := by
        apply Vector.ext; intro dj hdj
        rw [Vector.getElem_map, Vector.getElem_map, hbs, byteSlice, Vector.getElem_ofFn]
        exact hbytes _ _
      have hbt_map : Vector.map (Expression.eval e1.toEnvironment) bt
          = Vector.map (Expression.eval e2.toEnvironment) bt := by
        apply Vector.ext; intro l hl
        rw [Vector.getElem_map, Vector.getElem_map, hbt, bitSlice, Vector.getElem_ofFn]
        exact hbits _ _
      simp only [circuit_norm, hbs_map, hbt_map]
    have result := @FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
      (F circomPrime) _ (fields modulusBytesLen) ByteBlock.Inputs _ _
      ByteBlock.circuit input ({ bytes := bs, bits := bt } : Var ByteBlock.Inputs (F circomPrime))
      (offset + totalBits) hcond ByteBlock.computableWitnesses
    exact result env env'

/-- `Bytes.packLimbs` is affine over the bit variables, so its evaluation agrees
under any two environments that agree on all `totalBits` bit variables. -/
lemma eval_packLimbs_congr {env env' : Environment (F circomPrime)}
    (bits : Vector (Expression (F circomPrime)) totalBits)
    (h : ∀ (p : ℕ) (hp : p < totalBits),
      Expression.eval env (bits[p]'hp) = Expression.eval env' (bits[p]'hp)) :
    ∀ (k : ℕ) (hk : k < numLimbs),
      Expression.eval env ((Bytes.packLimbs bits)[k]'hk)
        = Expression.eval env' ((Bytes.packLimbs bits)[k]'hk) := by
  intro k hk
  unfold Bytes.packLimbs
  rw [Vector.getElem_ofFn, BytesLemmas.eval_foldl_add, BytesLemmas.eval_foldl_add]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : limbBits * k + i.val < totalBits
  · rw [dif_pos hi]
    simp only [Expression.eval]
    rw [h _ hi]
  · rw [dif_neg hi]
    simp only [Expression.eval]

/-- Vector-level agreement of the `BytesToBigInt` output (`packLimbs` of the
witnessed bit block). Mirrors `MulMod.eval_output_of_agreesBelow`. -/
lemma eval_output_of_agreesBelow {offset : ℕ} {env env' : ProverEnvironment (F circomPrime)}
    (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (h_agree : env.AgreesBelow (offset + totalBits) env') :
    eval env.toEnvironment ((main bytes).output offset)
      = eval env'.toEnvironment ((main bytes).output offset) := by
  have hout : (main bytes).output offset
      = Bytes.packLimbs (varFromOffset (fields totalBits) offset) :=
    elaborated.output_eq bytes offset
  rw [hout]
  have hbits : ∀ (p : ℕ) (hp : p < totalBits),
      Expression.eval env.toEnvironment
          ((varFromOffset (fields totalBits) offset : Var (fields totalBits) (F circomPrime))[p]'hp)
        = Expression.eval env'.toEnvironment
          ((varFromOffset (fields totalBits) offset : Var (fields totalBits) (F circomPrime))[p]'hp) := by
    intro p hp
    exact Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow
      h_agree (le_refl _) _ (Vector.getElem_mem hp)
  rw [CircuitType.eval_var_fields, CircuitType.eval_var_fields]
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map]
  exact eval_packLimbs_congr _ hbits k hk

/-- Circuit-level (subcircuit) output agreement, bridging `eval_output_of_agreesBelow`
through `elaborated.output_eq`. Mirrors `CompressBlock.eval_circuit_output_of_agreesBelow`;
used by `Main`. -/
lemma eval_circuit_output_of_agreesBelow {offset : ℕ}
    {env env' : ProverEnvironment (F circomPrime)}
    (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (h_agree : env.AgreesBelow (offset + totalBits) env') :
    eval env.toEnvironment (circuit.output bytes offset)
      = eval env'.toEnvironment (circuit.output bytes offset) := by
  change eval env.toEnvironment (ElaboratedCircuit.output main bytes offset) =
    eval env'.toEnvironment (ElaboratedCircuit.output main bytes offset)
  rw [← elaborated.output_eq bytes offset]
  exact eval_output_of_agreesBelow bytes h_agree

end BytesToBigInt
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
