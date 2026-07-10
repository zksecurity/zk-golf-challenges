import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MainTheorems
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Cost
import Challenge.Utils.ComputableWitnessLemmas

/-!
# Baseline solution — RSASSA-PKCS1-v1_5 / SHA256 / 4096 / e = 65537

This file holds the top-level circuit `main`, its elaboration `elaborated`, the
claimed cost (`allocations`/`constraints`), and the four checker obligations
(`soundness`, `completeness`, `mainCost`, `isR1CS`). All supporting material
lives in the sibling files: the parameter bundles and proof-support lemmas in
`MainTheorems.lean`, and the per-gadget compositional cost / R1CS certificates in
`Cost.lean`.

`main` witnesses the bit decompositions of the modulus (`4096` bits), signature
(`4096` bits) and digest (`256` bits), boolean-checks every bit, asserts each
public byte equals the little-endian sum of its 8 bits, packs the modulus and
signature bits into `BigInt 34` affine limbs and builds the PKCS#1-v1_5 encoded
message representative `h` from the digest bits plus the constant
DigestInfo/padding prefix, then asserts `sig < n` (`LessThan`), recovers
`sig ^ 65537 mod n` (`ModExp`), and asserts the recovered value equals `h`
(`Equal`). Limbs are normalized by construction (each is a sum of ≤ 121 boolean
bits), so no `Normalize` call is needed.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.GadgetCost

/-- Claimed witness-allocation count of `main` (proved by `mainCost`). -/
@[reducible] def allocations : Nat := 412130

/-- Claimed constraint-row count of `main` (proved by `mainCost`). -/
@[reducible] def constraints : Nat := 415006

section CircuitDef

/-- The top-level RSASSA-PKCS1-v1_5 / SHA256 / 4096 / e = 65537 verification
circuit. See the module docstring of `Main.lean` for the high-level structure. -/
def main (input : Var Input (F circomPrime)) :
    Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  -- 1. convert the public byte strings to big integers (split bits + pack),
  --    and build the PKCS#1-v1_5 padded message representative `h`.
  let n   ← subcircuit BytesToBigInt.circuit input.modulus
  let sig ← subcircuit BytesToBigInt.circuit input.signature
  let h   ← subcircuit PadDigest.circuit input.digest
  -- 2. sig < n, recover sig^e mod n, assert == h
  LessThan.circuit bigIntParams4096 { lhs := sig, rhs := n }
  let recovered ← subcircuit (ModExp.circuit params4096) { base := sig, modulus := n }
  Equal.circuit bigIntParams4096 { lhs := recovered, rhs := h }

-- Hand-written structural instance (rather than `elaborate_circuit`). The larger
-- per-`MulMod` length (now carrying the two `m*m` product matrices) pushes the whole
-- circuit's offset past the kernel's reduction-stack limit, so the automated tactic
-- (which forces a fully-reduced offset proof) hits "(kernel) deep recursion". Here every
-- obligation is discharged by `simp`/`omega` with the subcircuit lengths kept symbolic
-- (`ModExp`'s `modExpCount · mulModLen` is never reduced to a numeral), and the `unit`
-- output equality is closed by `Subsingleton` so the offset is never reduced.
instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main where
  localLength _ :=
    Bytes.totalBits + Bytes.totalBits + 256
      + (numLimbs + numLimbs * bigIntParams4096.B + numLimbs)
      + (ModExp.circuit params4096).localLength
          { base := varFromOffset (BigInt numLimbs) 0, modulus := varFromOffset (BigInt numLimbs) 0 }
  localLength_eq := by
    intro input offset
    have hML : ∀ x : Var (ModExp.Inputs numLimbs) (F circomPrime),
        (ModExp.circuit params4096).localLength x
          = (ModExp.circuit params4096).localLength
              { base := varFromOffset (BigInt numLimbs) 0, modulus := varFromOffset (BigInt numLimbs) 0 } :=
      fun _ => rfl
    simp only [main, circuit_norm, BytesToBigInt.circuit, BytesToBigInt.elaborated,
      PadDigest.circuit, PadDigest.elaborated, LessThan.circuit, LessThan.elaborated,
      Equal.circuit, Equal.elaborated, hML]
    ring
  output _ _ := ()
  output_eq := by
    intro input offset
    exact Subsingleton.elim (α := Unit) _ _
  subcircuitsConsistent := by
    intro input offset
    have hMEg : (ModExp.circuit params4096).channelsWithGuarantees = [] := rfl
    have hMEr : (ModExp.circuit params4096).channelsWithRequirements = [] := rfl
    simp +arith only [main, circuit_norm, BytesToBigInt.circuit, BytesToBigInt.elaborated,
      PadDigest.circuit, PadDigest.elaborated, LessThan.circuit, LessThan.elaborated,
      Equal.circuit, Equal.elaborated]
  channelsLawful := by
    intro input offset
    have hMEg : (ModExp.circuit params4096).channelsWithGuarantees = [] := rfl
    have hMEr : (ModExp.circuit params4096).channelsWithRequirements = [] := rfl
    simp only [main, circuit_norm, BytesToBigInt.circuit, BytesToBigInt.elaborated,
      PadDigest.circuit, PadDigest.elaborated, LessThan.circuit, LessThan.elaborated,
      Equal.circuit, Equal.elaborated, hMEg, hMEr]

end CircuitDef

/-! ## The four checker obligations -/

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  -- Decompose the six subcircuit obligations on `h_holds` only. Passing the
  -- subcircuit lemmas to the bracket form of `circuit_proof_start` would also
  -- apply them to the *goal*, making `circuit_norm` evaluate
  -- `(ModExp.circuit params4096)`'s channel lists; that unrolls the entire
  -- square-and-multiply loop and overflows the kernel reduction stack
  -- ("(kernel) deep recursion detected"). So we simplify `h_holds` directly and
  -- discharge the (empty) channel-requirement disjuncts of the goal by `Or.inl rfl`.
  simp only [circuit_norm,
    BytesToBigInt.circuit, BytesToBigInt.Spec, BytesToBigInt.Assumptions,
    PadDigest.circuit, PadDigest.Spec, PadDigest.Assumptions,
    LessThan.circuit, LessThan.elaborated, LessThan.Assumptions, LessThan.Spec,
    ModExp.circuit, ModExp.Spec, ModExp.Assumptions,
    Equal.circuit, Equal.elaborated, Equal.Assumptions, Equal.Spec] at h_holds
  obtain ⟨h_n, h_sig, h_pad, h_lt, h_modexp, h_eq⟩ := h_holds
  refine ⟨?_, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  -- The top-level Assumptions: each input is an octet string, and the modulus has
  -- exactly `4096` bits.
  simp only [Specs.RSASSAPKCS1v15_SHA256_4096_65537.Assumptions,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.algorithm,
    Specs.RSASSAPKCS1v15.Assumptions] at h_assumptions
  obtain ⟨hn_oct, hdig_oct, hsig_oct, hn_bits⟩ := h_assumptions
  -- Names for the *evaluated* recovered big integers.
  set nBI := Vector.map (Expression.eval env) (Bytes.packLimbs
    (Vector.mapRange Bytes.totalBits fun i ↦ var (F := F circomPrime) { index := i₀ + i }))
    with hnBI
  set sigBI := Vector.map (Expression.eval env) (Bytes.packLimbs
    (Vector.mapRange Bytes.totalBits fun i ↦
      var (F := F circomPrime) { index := i₀ + Bytes.totalBits + i })) with hsigBI
  set hBI := Vector.map (Expression.eval env) (Bytes.packLimbs (Bytes.emBits
    (Vector.mapRange 256 fun i ↦ var (F := F circomPrime)
      { index := i₀ + Bytes.totalBits + Bytes.totalBits + i }))) with hhBI
  -- Discharge `BytesToBigInt` (modulus + signature) and `PadDigest`.
  obtain ⟨hn_norm, hn_val⟩ := h_n hn_oct
  obtain ⟨hsig_norm, hsig_val⟩ := h_sig hsig_oct
  obtain ⟨hpad_norm, hpad_lt, EM, hEM_enc, hEM_oct, hpad_val⟩ := h_pad hdig_oct
  -- `params4096.bigIntParams.B = bigIntParams4096.B = Bytes.limbBits`.
  have hB1 : params4096.bigIntParams.B = Bytes.limbBits := rfl
  have hB2 : bigIntParams4096.B = Bytes.limbBits := rfl
  -- `1 < n.value`: the modulus has bit-size `4096`, so `2^4095 ≤ os2ip n = n.value`.
  have hn_gt1 : 1 < BigInt.value Bytes.limbBits nBI := by
    rw [hn_val]
    set bits := Specs.RSASSAPKCS1v15_SHA256_4096_65537.modulusBytesLen * 8 with hbits
    have hlb : 2 ^ (bits - 1) ≤ Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_modulus) :=
      hn_bits.1
    have h1 : (1 : ℕ) < 2 ^ (bits - 1) := Nat.one_lt_two_pow (by rw [hbits]; norm_num)
    exact lt_of_lt_of_le h1 hlb
  -- `LessThan`: sig.value < n.value (both normalized).
  have hsig_lt : BigInt.value Bytes.limbBits sigBI < BigInt.value Bytes.limbBits nBI := by
    have := h_lt ⟨by rw [hB2]; exact hsig_norm, by rw [hB2]; exact hn_norm⟩
    rwa [hB2] at this
  -- `ModExp`: recovered.value = sig.value ^ e % n.value.
  have hmodexp_assum :
      BigInt.Normalized params4096.bigIntParams.B sigBI ∧
        BigInt.Normalized params4096.bigIntParams.B nBI ∧
          BigInt.value params4096.bigIntParams.B sigBI < BigInt.value params4096.bigIntParams.B nBI ∧
            1 < BigInt.value params4096.bigIntParams.B nBI :=
    ⟨by rw [hB1]; exact hsig_norm, by rw [hB1]; exact hn_norm,
      by rw [hB1]; exact hsig_lt, by rw [hB1]; exact hn_gt1⟩
  obtain ⟨hrec_norm, hrec_val⟩ := h_modexp hmodexp_assum
  -- `hB1` rewrites the `params4096.bigIntParams.B` value arguments; `hB2` rewrites the
  -- `bigIntParams4096.B` occurrences in the recovered output's limb indices (the `ModExp`
  -- output closed form exposes them) so `hrec_val` matches `hrec_eq` syntactically.
  -- Keep the public exponent as the symbolic `publicExponent` (not the literal
  -- `65537`): this lets `hpow` match the trusted spec by `rfl` at the `exact`
  -- below without elaborating `_ ^ 65537`, which would trip the
  -- `exponentiation.threshold` reduction warning.
  rw [hB1, hB2, show params4096.e = Specs.RSASSAPKCS1v15_SHA256_4096_65537.publicExponent from rfl]
    at hrec_val
  rw [hB1, hB2] at hrec_norm
  -- `Equal`: recovered.value = h.value.
  have hrec_eq := h_eq ⟨by rw [hB2]; exact hrec_norm, by rw [hB2]; exact hpad_norm⟩
  rw [hB2] at hrec_eq
  -- The recovered value chain: os2ip sig ^ e % os2ip n = os2ip EM.
  have hpow : (Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_signature))
        ^ Specs.RSASSAPKCS1v15_SHA256_4096_65537.publicExponent
        % (Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_modulus))
      = Specs.RSASSAPKCS1v15.os2ip EM := by
    rw [← hsig_val, ← hn_val, ← hrec_val, hrec_eq, hpad_val]
  -- `sig < n` as `os2ip`.
  have hsig_lt' : Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_signature)
      < Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_modulus) := by
    rw [← hsig_val, ← hn_val]; exact hsig_lt
  -- Assemble the trusted spec. We deliberately leave `publicExponent` folded so the
  -- goal's exponent stays symbolic and `hpow` matches without a literal-power reduction.
  simp only [Specs.RSASSAPKCS1v15_SHA256_4096_65537.Spec,
    Specs.RSASSAPKCS1v15.Spec,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.algorithm]
  exact SoundnessLemmas.verifySignature_true _
    (fieldBytesToNat input_modulus) (fieldBytesToNat input_signature)
    (fieldBytesToNat input_digest) EM hsig_lt' hEM_enc hpow hEM_oct

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := by
  circuit_proof_start
  -- Decompose the per-subcircuit environment facts on `h_env` only. Passing the
  -- subcircuit lemmas to the bracket form of `circuit_proof_start` would also apply
  -- them to the *goal*, making `circuit_norm` evaluate `(ModExp.circuit params4096)`,
  -- which unrolls the entire square-and-multiply loop and overflows the kernel
  -- reduction stack ("(kernel) deep recursion detected"). The goal's subcircuit
  -- `Assumptions`/`Spec` stay folded; they are discharged definitionally below.
  simp only [circuit_norm,
    BytesToBigInt.circuit, BytesToBigInt.Spec, BytesToBigInt.Assumptions,
    PadDigest.circuit, PadDigest.Spec, PadDigest.Assumptions,
    LessThan.circuit, LessThan.elaborated,
    ModExp.circuit, ModExp.Spec, ModExp.Assumptions] at h_env
  -- Unfold the subcircuit interfaces in the *goal* without `ModExp.circuit` (which would
  -- trigger the same kernel deep recursion). `(ModExp.circuit params4096).Assumptions` is
  -- exposed by the `rfl` rewrite `hMEass`, and `modExp4096_output` (a `circuit_norm` lemma
  -- from `ModExpClosed`) rewrites the `ModExp` output to its shallow closed form.
  have hMEass : (ModExp.circuit params4096).Assumptions
      = ModExp.Assumptions params4096.e params4096.bigIntParams.B := rfl
  simp only [circuit_norm, hMEass,
    BytesToBigInt.circuit, BytesToBigInt.Assumptions,
    PadDigest.circuit, PadDigest.Assumptions,
    LessThan.circuit, LessThan.elaborated, LessThan.Assumptions, LessThan.Spec,
    ModExp.Assumptions,
    Equal.circuit, Equal.elaborated, Equal.Assumptions, Equal.Spec]
  -- The honest prover is given the trusted `Assumptions` and `Spec`.
  obtain ⟨h_assum, h_spec⟩ := h_assumptions
  simp only [Assumptions, Spec,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.Assumptions,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.Spec,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.algorithm,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.publicExponent,
    Specs.RSASSAPKCS1v15.Assumptions, Specs.RSASSAPKCS1v15.Spec] at h_assum h_spec
  obtain ⟨hn_oct, hdig_oct, hsig_oct, hn_bits⟩ := h_assum
  -- Subcircuit-output abbreviations (evaluated big integers).
  set nBI := Vector.map (Expression.eval env.toEnvironment) (Bytes.packLimbs
    (Vector.mapRange Bytes.totalBits fun i ↦ var (F := F circomPrime) { index := i₀ + i }))
    with hnBI
  set sigBI := Vector.map (Expression.eval env.toEnvironment) (Bytes.packLimbs
    (Vector.mapRange Bytes.totalBits fun i ↦
      var (F := F circomPrime) { index := i₀ + Bytes.totalBits + i })) with hsigBI
  set hBI := Vector.map (Expression.eval env.toEnvironment) (Bytes.packLimbs (Bytes.emBits
    (Vector.mapRange 256 fun i ↦ var (F := F circomPrime)
      { index := i₀ + Bytes.totalBits + Bytes.totalBits + i }))) with hhBI
  obtain ⟨h_envN, h_envSig, h_envPad, h_envModExp⟩ := h_env
  -- Byte-gadget specs (the prover's inputs are octet strings).
  obtain ⟨hn_norm, hn_val⟩ := h_envN hn_oct
  obtain ⟨hsig_norm, hsig_val⟩ := h_envSig hsig_oct
  obtain ⟨hpad_norm, hpad_lt, EM, hEM_enc, hEM_oct, hpad_val⟩ := h_envPad hdig_oct
  have hB1 : params4096.bigIntParams.B = Bytes.limbBits := rfl
  have hB2 : bigIntParams4096.B = Bytes.limbBits := rfl
  -- Invert the verification predicate: `sig < n` and `sig^65537 % n = os2ip EM`.
  obtain ⟨hlt_os, hpow_os⟩ :=
    MainTheorems.verifySignature_invert (fieldBytesToNat input_modulus)
      (fieldBytesToNat input_signature) (fieldBytesToNat input_digest) EM hEM_enc h_spec
  -- Translate to big-integer values.
  have hsig_lt : BigInt.value Bytes.limbBits sigBI < BigInt.value Bytes.limbBits nBI := by
    rw [hsig_val, hn_val]; exact hlt_os
  have hn_gt1 : 1 < BigInt.value Bytes.limbBits nBI := by
    rw [hn_val]
    set bits := Specs.RSASSAPKCS1v15_SHA256_4096_65537.modulusBytesLen * 8 with hbits
    have h1 : (1 : ℕ) < 2 ^ (bits - 1) := Nat.one_lt_two_pow (by rw [hbits]; norm_num)
    exact lt_of_lt_of_le h1 hn_bits.1
  -- ModExp gives `recovered.value = sig^65537 % n = os2ip EM = h.value`.
  obtain ⟨hrec_norm, hrec_val⟩ := h_envModExp
    ⟨by rw [hB1]; exact hsig_norm, by rw [hB1]; exact hn_norm,
      by rw [hB1]; exact hsig_lt, by rw [hB1]; exact hn_gt1⟩
  rw [hB1, show params4096.e = 65537 from rfl] at hrec_val
  rw [hB1] at hrec_norm
  -- Assemble the goal: octet strings, LessThan (assum + spec), ModExp assum,
  -- Equal (assum + spec).
  refine ⟨hn_oct, hsig_oct, hdig_oct,
    ⟨⟨by rw [hB2]; exact hsig_norm, by rw [hB2]; exact hn_norm⟩, by rw [hB2]; exact hsig_lt⟩,
    ⟨by rw [hB1]; exact hsig_norm, by rw [hB1]; exact hn_norm,
      by rw [hB1]; exact hsig_lt, by rw [hB1]; exact hn_gt1⟩,
    ⟨by rw [hB2]; exact hrec_norm, by rw [hB2]; exact hpad_norm⟩, ?_⟩
  -- Equal.Spec: recovered.value = h.value. `bigIntParams4096.B` is defeq to
  -- `Bytes.limbBits`, so `hrec_val` (stated with `Bytes.limbBits`) closes it.
  show BigInt.value Bytes.limbBits _ = BigInt.value Bytes.limbBits hBI
  rw [hrec_val, hsig_val, hn_val, hpow_os, hpad_val]

section Cost

/-- Compositional `CostIs` certificate for the whole circuit: the three byte/pad
subcircuits, the two `LessThan`/`Equal` assertions, and the `ModExp` subcircuit,
assembled by structural recursion over `main`'s `do`-block. -/
private theorem costIs_main (input : Var Input (F circomPrime)) :
    CostIs (main input) ⟨allocations, constraints⟩ :=
  CostIs.bind (costIs_sub_bytesToBigInt _) fun _ =>
  CostIs.bind (costIs_sub_bytesToBigInt _) fun _ =>
  CostIs.bind (costIs_sub_padDigest _) fun _ =>
  CostIs.bind (costIs_assertion_lessThan bigIntParams4096 _) fun _ =>
  CostIs.bind (costIs_sub_modExp params4096 _) fun _ =>
  CostIs.bind (costIs_assertion_equal bigIntParams4096 _) fun _ =>
  CostIs.pure _

theorem mainCost :
    Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ :=
  costIs_main

/-- Top-level single-row R1CS assembly over `main`'s `do`-block: thread the
affineness of each subcircuit output through the three byte/pad subcircuits, the
two `LessThan`/`Equal` assertions, and the `ModExp` subcircuit. Each is single-row
R1CS once its inputs are affine (the `ModExp`/`MulMod` convolution is R1CS-clean
via the witnessed-product `bigIntMulVars` form). -/
private theorem isR1CS_main_param (input : Var Input (F circomPrime))
    (hmod : AffineW input.modulus) (hsig : AffineW input.signature)
    (hdig : AffineW input.digest) :
    IsR1CSCirc (main input) := by
  unfold main
  refine IsR1CSCirc.bind_out (isR1CS_sub_bytesToBigInt _ hmod) fun nn => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_bytesToBigInt _ hsig) fun nsig => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_padDigest _ hdig) fun nh => ?_
  have hN := affineW_sub_bytesToBigInt input.modulus nn
  have hSig := affineW_sub_bytesToBigInt input.signature nsig
  have hH := affineW_sub_padDigest input.digest nh
  refine IsR1CSCirc.bind (isR1CS_assertion_lessThan bigIntParams4096 _ hSig hN) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_modExp params4096 _ hSig hN) fun nrec => ?_
  exact isR1CS_assertion_equal bigIntParams4096
    { lhs := (subcircuit (ModExp.circuit params4096)
        { base := (subcircuit BytesToBigInt.circuit input.signature).output nsig,
          modulus := (subcircuit BytesToBigInt.circuit input.modulus).output nn }).output nrec,
      rhs := (subcircuit PadDigest.circuit input.digest).output nh }
    (affineW_sub_modExp params4096 _ nrec hSig hN) hH

theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
  (fun input hinput =>
    isR1CS_main_param input (affineW_input_modulus input hinput)
      (affineW_input_signature input hinput) (affineW_input_digest input hinput))
  (fun _ _ => affineOutput_unit _)

end Cost

section ComputableWitness

open Challenge.Utils.ComputableWitnessLemmas

attribute [local irreducible] main BytesToBigInt.circuit PadDigest.circuit
  LessThan.circuit Equal.circuit ModExp.circuit

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := by
  intro n input hinput env env'
  change (main input).operations n |>.forAllFlat n
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  have hstruct :
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
        input env env' n ((main input).operations n) := by
    unfold main
    -- name each subcircuit / assertion and its starting offset
    let modCircuit : Circuit (F circomPrime) (Var (BigInt numLimbs) (F circomPrime)) :=
      subcircuit BytesToBigInt.circuit input.modulus
    let nOut := modCircuit.output n
    let sigOffset := n + modCircuit.localLength n
    let sigCircuit : Circuit (F circomPrime) (Var (BigInt numLimbs) (F circomPrime)) :=
      subcircuit BytesToBigInt.circuit input.signature
    let sigOut := sigCircuit.output sigOffset
    let padOffset := sigOffset + sigCircuit.localLength sigOffset
    let padCircuit : Circuit (F circomPrime) (Var (BigInt numLimbs) (F circomPrime)) :=
      subcircuit PadDigest.circuit input.digest
    let hOut := padCircuit.output padOffset
    let ltOffset := padOffset + padCircuit.localLength padOffset
    let ltCircuit : Circuit (F circomPrime) Unit :=
      LessThan.circuit bigIntParams4096 { lhs := sigOut, rhs := nOut }
    let recOffset := ltOffset + ltCircuit.localLength ltOffset
    let recCircuit : Circuit (F circomPrime) (Var (BigInt numLimbs) (F circomPrime)) :=
      subcircuit (ModExp.circuit params4096) { base := sigOut, modulus := nOut }
    let recOut := recCircuit.output recOffset
    let eqOffset := recOffset + recCircuit.localLength recOffset
    -- ordering facts: each producing block ends before the consumer's offset
    have hn_le_lt : n + Bytes.totalBits ≤ ltOffset := by
      simp only [ltOffset, padOffset, sigOffset, modCircuit, sigCircuit, padCircuit,
        BytesToBigInt.circuit, BytesToBigInt.elaborated,
        PadDigest.circuit, PadDigest.elaborated, circuit_norm]
      omega
    have hsig_le_lt : sigOffset + Bytes.totalBits ≤ ltOffset := by
      simp only [ltOffset, padOffset, sigOffset, modCircuit, sigCircuit, padCircuit,
        BytesToBigInt.circuit, BytesToBigInt.elaborated,
        PadDigest.circuit, PadDigest.elaborated, circuit_norm]
      omega
    have hpad_le_lt : padOffset + 256 ≤ ltOffset := by
      simp only [ltOffset, padCircuit, PadDigest.circuit, PadDigest.elaborated, circuit_norm]
      omega
    have hlt_le_rec : ltOffset ≤ recOffset := Nat.le_add_right _ _
    have hrec_le_eq : recOffset ≤ eqOffset := Nat.le_add_right _ _
    have hn_le_rec : n + Bytes.totalBits ≤ recOffset := le_trans hn_le_lt hlt_le_rec
    have hsig_le_rec : sigOffset + Bytes.totalBits ≤ recOffset := le_trans hsig_le_lt hlt_le_rec
    have hn_le_eq : n + Bytes.totalBits ≤ eqOffset := le_trans hn_le_rec hrec_le_eq
    have hsig_le_eq : sigOffset + Bytes.totalBits ≤ eqOffset := le_trans hsig_le_rec hrec_le_eq
    have hpad_le_eq : padOffset + 256 ≤ eqOffset :=
      le_trans (le_trans hpad_le_lt hlt_le_rec) hrec_le_eq
    simp only [
      Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
      Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff]
    refine ⟨?op1, ?op2, ?op3, ?op4, ?op5, ?op6⟩
    case op1 =>
      refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        BytesToBigInt.circuit input input.modulus n ?_ BytesToBigInt.computableWitnesses env env'
      intro k e1 e2 _ _ h_input_eq
      simpa [circuit_norm] using congrArg (fun x : Input (F circomPrime) => x.modulus) h_input_eq
    case op2 =>
      refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        BytesToBigInt.circuit input input.signature sigOffset ?_ BytesToBigInt.computableWitnesses env env'
      intro k e1 e2 _ _ h_input_eq
      simpa [circuit_norm] using congrArg (fun x : Input (F circomPrime) => x.signature) h_input_eq
    case op3 =>
      refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        PadDigest.circuit input input.digest padOffset ?_ PadDigest.computableWitnesses env env'
      intro k e1 e2 _ _ h_input_eq
      simpa [circuit_norm] using congrArg (fun x : Input (F circomPrime) => x.digest) h_input_eq
    case op4 =>
      refine Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        (LessThan.circuit bigIntParams4096) input { lhs := sigOut, rhs := nOut } ltOffset ?_
        (LessThan.computableWitnesses bigIntParams4096) env env'
      intro k e1 e2 hle h_agree _
      simp only [circuit_norm]
      congr 1
      · simpa only [sigOut, sigCircuit, circuit_norm] using
          BytesToBigInt.eval_circuit_output_of_agreesBelow input.signature
            (ProverEnvironment.agreesBelow_of_le h_agree (le_trans hsig_le_lt hle))
      · simpa only [nOut, modCircuit, circuit_norm] using
          BytesToBigInt.eval_circuit_output_of_agreesBelow input.modulus
            (ProverEnvironment.agreesBelow_of_le h_agree (le_trans hn_le_lt hle))
    case op5 =>
      refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (ModExp.circuit params4096) input { base := sigOut, modulus := nOut } recOffset ?_
        (ModExp.computableWitnesses params4096) env env'
      intro k e1 e2 hle h_agree _
      simp only [circuit_norm]
      congr 1
      · simpa only [sigOut, sigCircuit, circuit_norm] using
          BytesToBigInt.eval_circuit_output_of_agreesBelow input.signature
            (ProverEnvironment.agreesBelow_of_le h_agree (le_trans hsig_le_rec hle))
      · simpa only [nOut, modCircuit, circuit_norm] using
          BytesToBigInt.eval_circuit_output_of_agreesBelow input.modulus
            (ProverEnvironment.agreesBelow_of_le h_agree (le_trans hn_le_rec hle))
    case op6 =>
      refine Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition
        (Equal.circuit bigIntParams4096) input { lhs := recOut, rhs := hOut } eqOffset ?_
        (Equal.computableWitnesses bigIntParams4096) env env'
      intro k e1 e2 hle h_agree _
      have h_me_input : eval e1 ({ base := sigOut, modulus := nOut } : Var (ModExp.Inputs numLimbs) (F circomPrime))
          = eval e2 ({ base := sigOut, modulus := nOut } : Var (ModExp.Inputs numLimbs) (F circomPrime)) := by
        simp only [circuit_norm]
        congr 1
        · simpa only [sigOut, sigCircuit, circuit_norm] using
            BytesToBigInt.eval_circuit_output_of_agreesBelow input.signature
              (ProverEnvironment.agreesBelow_of_le h_agree (le_trans hsig_le_eq hle))
        · simpa only [nOut, modCircuit, circuit_norm] using
            BytesToBigInt.eval_circuit_output_of_agreesBelow input.modulus
              (ProverEnvironment.agreesBelow_of_le h_agree (le_trans hn_le_eq hle))
      simp only [circuit_norm]
      congr 1
      · -- Bound the env agreement using the *generic* subcircuit-localLength lemma,
        -- so the kernel never reduces `ModExp`'s operations.
        have hagree_me : e1.AgreesBelow
            (recOffset + (ModExp.circuit params4096).localLength { base := sigOut, modulus := nOut }) e2 := by
          apply ProverEnvironment.agreesBelow_of_le h_agree
          rw [← subcircuit_localLength_eq (ModExp.circuit params4096)
            { base := sigOut, modulus := nOut } recOffset]
          exact hle
        have hrec := ModExp.eval_circuit_output_of_agreesBelow params4096 { base := sigOut, modulus := nOut }
          h_me_input hagree_me
        have hgoal_eq : recOut
            = (ModExp.circuit params4096).output { base := sigOut, modulus := nOut } recOffset :=
          subcircuit_output_eq (ModExp.circuit params4096) { base := sigOut, modulus := nOut } recOffset
        rw [hgoal_eq]
        simp only [circuit_norm] at hrec ⊢
        exact hrec
      · simpa only [hOut, padCircuit, circuit_norm] using
          PadDigest.eval_circuit_output_of_agreesBelow input.digest
            (ProverEnvironment.agreesBelow_of_le h_agree (le_trans hpad_le_eq hle))
  -- reduce the flattened structural condition to the target `forAllFlat` condition
  have hflat :=
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
      input env env' hstruct
  unfold Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition at hflat
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  let targetCondition : Condition (F circomPrime) :=
    { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
  apply FlatOperation.forAll_implies (F := F circomPrime) n ?_ hflat
  have himplies : ∀ (ops : List (FlatOperation (F circomPrime))) (off : ℕ),
      n ≤ off →
      FlatOperation.forAll off
        (Condition.implies
          (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
            input env env')
          targetCondition).ignoreSubcircuit
        ops := by
    intro ops off hoff
    induction ops generalizing off with
    | nil => simp [FlatOperation.forAll]
    | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          constructor
          · intro hparent hagree
            exact hparent hagree
              (hinput env env' (ProverEnvironment.agreesBelow_of_le hagree hoff))
          · exact ih (m + off) (by omega)
      | assert e =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | lookup l =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | interact i =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
  exact himplies ((main input).operations n).toFlat n (le_refl n)

end ComputableWitness

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
