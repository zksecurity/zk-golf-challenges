import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod

/-!
# RSA modular exponentiation (gadget G6)

This file defines `ModExp` (gadget **G6**), the structural / `e`-branching gadget
of the RSA circuit family: a `FormalCircuit` computing `base ^ e mod n` over
normalized big integers, where the exponent `e : ℕ` is **known at compile time**.

## Strategy

Left-to-right square-and-multiply, unrolled on the bits of `e`. We expand `e`
into a big-endian bit list `eBits e` once at synthesis time and recurse on it
with `modExpLoop`: each bit emits a squaring `MulMod` subcircuit and, when the
bit is set, an additional multiply `MulMod` subcircuit. The `if bit then …`
branch is decided at synthesis time, so set bits literally add a `MulMod`
subcircuit and clear bits do not — this is the `e`-branching.

Soundness and completeness are fully proved here. The structural obligations
(`localLength`, `subcircuitsConsistent`, `channelsLawful`) and the
soundness/completeness invariants are established by induction on the bit list
via the `modExpLoop_*` helper lemmas; the exponent reconstruction `ofBits_eBits`
closes the final `base^e mod n` equation.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace ModExp

/-! ## `ModExp`: exponent-bit helpers and the constant `1` -/

/-- Big-endian (MSB-first) bit list of `e`. `Nat.bits` is LSB-first, so we
reverse it. Computed at compile time; drives the circuit structure. -/
def eBits (e : ℕ) : List Bool := (Nat.bits e).reverse

/-- Big-endian Horner evaluation of a bit list: `[b₀,…,bₖ] ↦ 2^k·b₀ + … + bₖ`. -/
def ofBits (bs : List Bool) : ℕ :=
  bs.foldl (fun a b => 2 * a + (if b then 1 else 0)) 0

/-- Big-endian Horner: prepending a bit shifts the rest up by `2^|rest|`. -/
lemma ofBits_cons (b : Bool) (bs : List Bool) :
    ofBits (b :: bs) = (if b then 1 else 0) * 2 ^ bs.length + ofBits bs := by
  simp only [ofBits, List.foldl_cons, Nat.mul_zero, Nat.zero_add]
  -- generalize the foldl starting accumulator
  suffices h : ∀ (a : ℕ) (l : List Bool),
      l.foldl (fun a b => 2 * a + (if b then 1 else 0)) a
        = a * 2 ^ l.length + l.foldl (fun a b => 2 * a + (if b then 1 else 0)) 0 by
    rw [h (if b then 1 else 0) bs]
  intro a l
  induction l generalizing a with
  | nil => simp
  | cons c t ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (2 * a + (if c then 1 else 0)),
      ih (2 * 0 + (if c then 1 else 0)), List.length_cons]
    ring

/-- LSB-first Horner reconstruction: folding `Nat.bits e` from the right recovers `e`. -/
lemma foldr_bits (e : ℕ) :
    (Nat.bits e).foldr (fun b a => 2 * a + (if b then 1 else 0)) 0 = e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp [Nat.zero_bits]
    · rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- e = 2k, k ≠ 0
        have hk0 : k ≠ 0 := by omega
        have hklt : k < e := by omega
        have hbits : Nat.bits e = false :: Nat.bits k := by
          rw [show e = 2 * k by omega]; exact Nat.bit0_bits k hk0
        rw [hbits]
        simp only [List.foldr_cons, Bool.false_eq_true, if_false, ih k hklt]
        omega
      · -- e = 2k+1
        have hklt : k < e := by omega
        have hbits : Nat.bits e = true :: Nat.bits k := by
          rw [show e = 2 * k + 1 by omega]; exact Nat.bit1_bits k
        rw [hbits]
        simp only [List.foldr_cons, if_true, ih k hklt]
        omega

/-- The big-endian reconstruction of `eBits e` is exactly `e`. -/
lemma ofBits_eBits (e : ℕ) : ofBits (eBits e) = e := by
  rw [ofBits, eBits, List.foldl_reverse, foldr_bits]

/-- A big-endian bit list of length `L` reconstructs to a value `< 2^L`. -/
lemma ofBits_lt (bs : List Bool) : ofBits bs < 2 ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [ofBits]
  | append_singleton t b ih =>
    rw [ofBits, List.foldl_append, List.length_append]
    simp only [List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
    have hfold : t.foldl (fun a b => 2 * a + (if b then 1 else 0)) 0 = ofBits t := rfl
    rw [hfold]
    have hb : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
    rw [show t.length + 1 = t.length + 1 from rfl, pow_succ]
    omega

/-- `eBits e = []` exactly when `e = 0`. -/
lemma eBits_eq_nil_iff (e : ℕ) : eBits e = [] ↔ e = 0 := by
  rw [eBits, List.reverse_eq_nil_iff]
  constructor
  · intro h
    have := foldr_bits e
    rw [h] at this; simpa using this.symm
  · intro h; subst h; exact Nat.zero_bits

/-- The leading (most-significant) bit of a nonzero `e` is `1`: if
`eBits e = b :: tail` then `b = true`. -/
lemma eBits_head_true {e : ℕ} {b : Bool} {tail : List Bool}
    (h : eBits e = b :: tail) : b = true := by
  by_contra hb
  simp only [Bool.not_eq_true] at hb
  subst hb
  -- e = ofBits (false :: tail) = ofBits tail < 2^tail.length
  have he : e = ofBits tail := by
    have := ofBits_eBits e
    rw [h, ofBits_cons] at this
    simpa using this.symm
  -- but e ≠ 0 since eBits e ≠ [], and eBits e has length tail.length + 1
  have hne : e ≠ 0 := by
    intro h0
    have : eBits e = [] := (eBits_eq_nil_iff e).mpr h0
    rw [h] at this
    exact List.cons_ne_nil _ _ this
  -- ofBits tail < 2^tail.length ; and e = ofBits (eBits e) reconstructs with leading
  -- weight 2^tail.length which would be ≤ e, contradiction with e = ofBits tail
  -- Use: 2^tail.length ≤ e because the MSB position contributes that weight.
  -- We derive a contradiction directly: e = ofBits tail < 2^tail.length, but also
  -- e must be ≥ 2^tail.length since eBits e = false :: tail has length tail.length+1
  -- and reconstructs e. The cleanest: ofBits tail < 2^tail.length = the weight that
  -- a true leading bit would add, so a true leading bit gives e ≥ 2^tail.length.
  -- Since here e = ofBits tail, combine with eBits roundtrip to bound the length.
  -- Concretely use the size relation via Nat.bits length.
  have hlt : ofBits tail < 2 ^ tail.length := ofBits_lt tail
  -- length of eBits e equals (Nat.bits e).length = Nat.size e ; for e ≠ 0, 2^(size-1) ≤ e
  have hlen : (eBits e).length = tail.length + 1 := by rw [h]; simp
  have hsize : tail.length + 1 = Nat.size e := by
    rw [← hlen, eBits, List.length_reverse, Nat.size_eq_bits_len]
  have hpos : 0 < e := Nat.pos_of_ne_zero hne
  have hsizepos : 0 < Nat.size e := Nat.size_pos.mpr hpos
  have hge : 2 ^ (Nat.size e - 1) ≤ e := Nat.lt_size.mp (by omega)
  -- 2^(size e - 1) = 2^tail.length, so e ≥ 2^tail.length but e < 2^tail.length: contradiction
  have : 2 ^ tail.length ≤ e := by
    have : Nat.size e - 1 = tail.length := by omega
    rwa [this] at hge
  omega

/-- The big-integer constant `one` (limb 0 = 1, rest 0). -/
def oneVal [Fact (p > 2)] : BigInt m (F p) :=
  Vector.ofFn fun k : Fin m => if k.val = 0 then (1 : F p) else 0

omit [NeZero m] in
/-- `oneVal` is normalized (each limb is `0` or `1`, both `< 2^B` since `1 ≤ B`). -/
lemma oneVal_normalized [Fact (p > 2)] {B : ℕ} (hB1 : 1 ≤ B) :
    (oneVal (m := m) (p := p)).Normalized B := by
  intro i
  have h2 : (1 : ℕ) < 2 ^ B := by
    calc (1 : ℕ) < 2 := by norm_num
      _ ≤ 2 ^ B := by
        rw [show (2 : ℕ) = 2 ^ 1 from rfl]
        exact Nat.pow_le_pow_right (by norm_num) hB1
  simp only [oneVal, BigInt, Fin.getElem_fin, Vector.getElem_ofFn]
  by_cases hi : i.val = 0
  · simp only [hi, if_true]
    have : ((1 : F p)).val = 1 := by
      have : Fact (1 < p) := ⟨lt_trans one_lt_two (Fact.out (p := p > 2))⟩
      simp [ZMod.val_one]
    rw [this]; exact h2
  · simp only [hi, if_false, ZMod.val_zero]; exact Nat.two_pow_pos B

/-- `oneVal` denotes the natural number `1`. -/
lemma value_oneVal [Fact (p > 2)] {B : ℕ} :
    (oneVal (m := m) (p := p)).value B = 1 := by
  rw [BigInt.value_eq_sum]
  have hp1 : Fact (1 < p) := ⟨lt_trans one_lt_two (Fact.out (p := p > 2))⟩
  rw [Finset.sum_eq_single (⟨0, Nat.pos_of_neZero m⟩ : Fin m)]
  · simp only [oneVal, BigInt, Fin.getElem_fin, Vector.getElem_ofFn, if_true]
    rw [ZMod.val_one]; simp
  · intro b _ hb
    have hb0 : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp only [oneVal, BigInt, Fin.getElem_fin, Vector.getElem_ofFn, hb0, if_false,
      ZMod.val_zero, Nat.zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Inputs to the `ModExp` gadget: the `base` and the `modulus`. -/
structure Inputs (m : ℕ) (F : Type) where
  base : BigInt m F
  modulus : BigInt m F
deriving ProvableStruct

/-- Number of `MulMod` subcircuit calls emitted for exponent `e`. We seed the
accumulator with `base` (consuming the most-significant bit, always `1` for
`e ≥ 1`) and loop over the remaining bits: one squaring per remaining bit, plus
one multiply per remaining set bit. For `e = 0` there are no calls. -/
def modExpCount (e : ℕ) : ℕ := match eBits e with
  | [] => 0
  | _ :: tail => tail.length + tail.count true

/-- `localLength` of a single `MulMod` subcircuit (mirrors `MulMod.elaborated`).
Includes the two `witnessedMul` product matrices (`m*m` each). -/
def mulModLen (B W : ℕ) : ℕ :=
  m + m + m * B + m * B + (m * m) + (m * m)
    + ((2 * m - 1) * W + (2 * m - 1)) + (m + m * B + m)

/-- The recursive unrolled square-and-multiply loop. Structural recursion on the
big-endian bit list of `e`; each step squares the accumulator and, if the bit is
set, multiplies in `base` — both modulo `n` via `MulMod` subcircuits. -/
def modExpLoop (P : BigIntParams p m) [Fact (p > 2)]
    (base n : Var (BigInt m) (F p)) :
    List Bool → Var (BigInt m) (F p) → Circuit (F p) (Var (BigInt m) (F p))
  | [], acc => pure acc
  | bit :: rest, acc => do
      let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
      let acc' ← if bit then subcircuit (MulMod.circuit P) { a := sq, b := base, modulus := n }
                 else pure sq
      modExpLoop P base n rest acc'

/-- The `main` circuit of `ModExp`.

Inputs are `base := input.base` and `n := input.modulus`. We branch on the
big-endian bit list of `e`:

* `e = 0` (`eBits e = []`): return the big-integer constant `1`
  (limb 0 = 1, rest 0; no witnesses).
* `e ≥ 1` (`eBits e = _ :: tail`): the leading bit is always `1`, so we seed the
  accumulator with `base` (consuming that bit) and run `modExpLoop` over the
  remaining bits `tail`, returning `base ^ e mod n`. This saves the two wasted
  leading-bit `MulMod`s (`1·1` and `1·base`). -/
def main (P : RSAParams p m) [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) := do
  let base := input.base
  let n := input.modulus
  match eBits P.e with
  | [] => pure (Vector.ofFn fun k : Fin m =>
      if k.val = 0 then (1 : Expression (F p)) else 0)
  | _ :: tail => modExpLoop P.bigIntParams base n tail base

/-- `localLength` of the unrolled loop over a bit list: one `MulMod` per bit
(squaring) plus one extra `MulMod` per set bit (multiply). -/
lemma modExpLoop_localLength (P : BigIntParams p m) [Fact (p > 2)]
    (base n : Var (BigInt m) (F p)) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      (modExpLoop P base n bs acc).localLength offset
        = (bs.length + bs.count true) * mulModLen (m := m) P.B P.W := by
  intro bs
  induction bs with
  | nil => intro acc offset; simp [modExpLoop, circuit_norm]
  | cons bit rest ih =>
    intro acc offset
    have hML : ∀ (x : Var (MulMod.Inputs m) (F p)),
        (MulMod.circuit P).localLength x
          = mulModLen (m := m) P.B P.W := fun _ => rfl
    cases bit
    · simp only [modExpLoop, circuit_norm, ih, List.length_cons, List.count_cons,
        Bool.false_eq_true, if_false, Nat.add_zero, hML, beq_iff_eq]
      generalize mulModLen (m := m) P.B P.W = L
      ring
    · simp only [modExpLoop, circuit_norm, ih, List.length_cons, List.count_cons,
        if_true, beq_self_eq_true, hML]
      generalize mulModLen (m := m) P.B P.W = L
      ring

/-- `subcircuitsConsistent` for the unrolled loop, by induction on the bit list. -/
lemma modExpLoop_subcircuitsConsistent (P : BigIntParams p m) [Fact (p > 2)]
    (base n : Var (BigInt m) (F p)) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      ((modExpLoop P base n bs acc).operations offset).SubcircuitsConsistent offset := by
  intro bs
  induction bs with
  | nil => intro acc offset; simp [modExpLoop, circuit_norm]
  | cons bit rest ih =>
    intro acc offset
    have key : ∀ acc' off, Operations.forAll off { subcircuit := fun off {n} _ => n = off }
        ((modExpLoop P base n rest acc').operations off) := by
      intro acc' off; exact ih acc' off
    cases bit
    · simp only [modExpLoop, circuit_norm, Bool.false_eq_true, if_false]
      ring_nf
      apply key
    · simp only [modExpLoop, circuit_norm, if_true]
      refine ⟨by ac_rfl, ?_⟩
      ring_nf
      apply key

/-- `channelsLawful` for the unrolled loop, by induction on the bit list. -/
lemma modExpLoop_channelsLawful (P : BigIntParams p m) [Fact (p > 2)]
    (base n : Var (BigInt m) (F p)) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      ((modExpLoop P base n bs acc).operations offset).ChannelsLawful [] [] := by
  -- The single-`MulMod`-subcircuit step is channel-lawful (R1CS, no channels).
  have hsub : ∀ (x : Var (MulMod.Inputs m) (F p)) (off : ℕ),
      (((subcircuit (MulMod.circuit P) x)).operations off).ChannelsLawful [] [] := by
    intro x off
    simp only [circuit_norm, MulMod.circuit, MulMod.elaborated]
  intro bs
  induction bs with
  | nil =>
    intro acc offset
    simp only [modExpLoop, Circuit.pure_operations_eq]
    exact Operations.channelsLawful_nil
  | cons bit rest ih =>
    intro acc offset
    cases bit
    · show ((do
          let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
          modExpLoop P base n rest sq).operations offset).ChannelsLawful [] []
      rw [Circuit.bind_operations_eq]
      exact Operations.channelsLawful_append_of_channelsLawful
        (hsub { a := acc, b := acc, modulus := n } offset) (ih _ _)
    · show ((do
          let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
          let acc' ← subcircuit (MulMod.circuit P) { a := sq, b := base, modulus := n }
          modExpLoop P base n rest acc').operations offset).ChannelsLawful [] []
      rw [Circuit.bind_operations_eq, Circuit.bind_operations_eq]
      exact Operations.channelsLawful_append_of_channelsLawful (hsub { a := acc, b := acc, modulus := n } offset)
        (Operations.channelsLawful_append_of_channelsLawful (hsub _ _) (ih _ _))

/-- Evaluate a big-integer variable vector under `env`. -/
private abbrev ev (env : Environment (F p)) (x : Var (BigInt m) (F p)) : BigInt m (F p) :=
  Vector.map (Expression.eval env) x


/-- **Soundness invariant for the unrolled loop.** Processing a big-endian bit
list `bs` starting from an accumulator denoting `base^E % n` yields a value
denoting `base^(E·2^|bs| + ofBits bs) % n`, staying normalized and `< n`. -/
lemma modExpLoop_soundness (P : BigIntParams p m) [Fact (p > 2)]
    (env : Environment (F p)) (base n : Var (BigInt m) (F p))
    (hbase_norm : (ev env base).Normalized P.B) (hn_norm : (ev env n).Normalized P.B)
    (hbase_lt : (ev env base).value P.B < (ev env n).value P.B)
    (hn_pos : 0 < (ev env n).value P.B) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F p)) (offset E : ℕ),
      (ev env acc).Normalized P.B →
      (ev env acc).value P.B < (ev env n).value P.B →
      (ev env acc).value P.B = (ev env base).value P.B ^ E % (ev env n).value P.B →
      Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env e = 0, lookup := fun l ↦ l.Soundness env,
          interact := fun i ↦ i.Guarantees env, subcircuit := fun {_m} s ↦ s.Assumptions env → s.Spec env }
        ((modExpLoop P base n bs acc).operations offset) →
      (ev env (modExpLoop P base n bs acc offset).1).Normalized P.B ∧
      (ev env (modExpLoop P base n bs acc offset).1).value P.B < (ev env n).value P.B ∧
      (ev env (modExpLoop P base n bs acc offset).1).value P.B
        = (ev env base).value P.B ^ (E * 2 ^ bs.length + ofBits bs) % (ev env n).value P.B := by
  intro bs
  induction bs with
  | nil =>
    intro acc offset E hacc_norm hacc_lt hacc_val _
    simp only [modExpLoop, List.length_nil, pow_zero, Nat.mul_one, ofBits, List.foldl_nil,
      Nat.add_zero]
    exact ⟨hacc_norm, hacc_lt, hacc_val⟩
  | cons bit rest ih =>
    intro acc offset E hacc_norm hacc_lt hacc_val h_holds
    -- The square step: a `MulMod` on `(acc, (acc, n))` producing `sq` at offset `offset`.
    -- Its output variable is `varFromOffset (BigInt m) (offset + m)`.
    set sqVar : Var (BigInt m) (F p) :=
      (MulMod.circuit P).output { a := acc, b := acc, modulus := n } offset with hsqVar
    -- MulMod assumptions for the square
    have hsq_as : MulMod.Assumptions P.B ({ a := ev env acc, b := ev env acc, modulus := ev env n } :
        MulMod.Inputs m (F p)) := by
      refine ⟨hacc_norm, hacc_norm, hn_norm, hacc_lt, hacc_lt, hn_pos⟩
    -- expose the square subcircuit at the head of the bind
    rw [show modExpLoop P base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulMod.circuit P) { a := sq, b := base, modulus := n }
                       else pure sq
            modExpLoop P base n rest acc') from rfl] at h_holds ⊢
    rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append] at h_holds
    obtain ⟨h_sq_holds, h_rest_holds⟩ := h_holds
    -- spec of the square step
    simp only [circuit_norm, MulMod.circuit] at h_sq_holds
    obtain ⟨hsq_norm, hsq_val⟩ := h_sq_holds hsq_as
    -- abbreviate the square output value vector
    set sq : Var (BigInt m) (F p) := Vector.mapRange m fun i ↦ var { index := offset + m + i } with hsq_def
    -- sq.value < n.value (it is a `% n` result)
    have hsq_lt : (ev env sq).value P.B < (ev env n).value P.B := by
      rw [hsq_val]; exact Nat.mod_lt _ hn_pos
    -- sq.value = base^(2E) % n
    have hsq_pow : (ev env sq).value P.B = (ev env base).value P.B ^ (2 * E) % (ev env n).value P.B := by
      rw [hsq_val, hacc_val, ← Nat.mul_mod, ← pow_add, two_mul]
    -- The square output variable equals `sq`.
    have hsqVar_eq : sqVar = sq := by
      simp only [hsqVar, hsq_def, circuit_norm, MulMod.circuit, MulMod.elaborated]
    cases bit
    · -- clear bit: acc' = sq, exponent step E ↦ 2E
      simp only [Bool.false_eq_true, if_false] at h_rest_holds ⊢
      simp only [circuit_norm, MulMod.circuit, MulMod.elaborated] at h_rest_holds ⊢
      obtain ⟨h1, h2, h3⟩ := ih sq _ (2 * E) hsq_norm hsq_lt hsq_pow h_rest_holds
      refine ⟨h1, h2, ?_⟩
      rw [h3, ofBits_cons, List.length_cons]
      congr 2
      simp only [Bool.false_eq_true, if_false, Nat.zero_mul]
      rw [pow_succ]
      ring
    · -- set bit: an extra multiply, exponent step E ↦ 2E+1
      simp only [if_true] at h_rest_holds ⊢
      -- the multiply subcircuit's output variable
      set mulVar : Var (BigInt m) (F p) :=
        (MulMod.circuit P).output { a := sqVar, b := base, modulus := n }
          (offset + (MulMod.circuit P).localLength { a := acc, b := acc, modulus := n }) with hmulVar
      -- expose the multiply subcircuit inside the rest
      rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append] at h_rest_holds
      obtain ⟨h_mul_holds, h_rest2_holds⟩ := h_rest_holds
      -- assumptions of the multiply: sq, base, n
      have hmul_as : MulMod.Assumptions P.B ({ a := ev env sq, b := ev env base, modulus := ev env n } :
          MulMod.Inputs m (F p)) :=
        ⟨hsq_norm, hbase_norm, hn_norm, hsq_lt, hbase_lt, hn_pos⟩
      simp only [circuit_norm, MulMod.circuit] at h_mul_holds
      obtain ⟨hmul_norm, hmul_val⟩ := h_mul_holds hmul_as
      set mul : Var (BigInt m) (F p) :=
        Vector.mapRange m fun i ↦
          var { index := offset + (m + m + m * P.B + m * P.B + (m * m) + (m * m) + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m)) + m + i }
        with hmul_def
      -- multiply output invariants
      have hmul_lt : (ev env mul).value P.B < (ev env n).value P.B := by
        rw [hmul_val]; exact Nat.mod_lt _ hn_pos
      have hmul_pow : (ev env mul).value P.B = (ev env base).value P.B ^ (2 * E + 1) % (ev env n).value P.B := by
        rw [hmul_val]
        simp only []
        rw [hsq_pow, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]
      -- reduce the goal's bind output to `modExpLoop rest mul`
      simp only [circuit_norm, MulMod.circuit, MulMod.elaborated] at h_rest2_holds ⊢
      obtain ⟨h1, h2, h3⟩ := ih mul _ (2 * E + 1) hmul_norm hmul_lt hmul_pow h_rest2_holds
      refine ⟨h1, h2, ?_⟩
      rw [h3, ofBits_cons, List.length_cons]
      congr 2
      simp only [if_true, Nat.one_mul]
      rw [pow_succ]
      ring

/-- **Completeness invariant for the unrolled loop.** Given that the prover
environment extends the local witnesses, the per-step `MulMod` assumptions hold
at every step (and the running accumulator stays normalized and `< n`). -/
lemma modExpLoop_completeness (P : BigIntParams p m) [Fact (p > 2)]
    (env : ProverEnvironment (F p)) (base n : Var (BigInt m) (F p))
    (hbase_norm : (ev env.toEnvironment base).Normalized P.B) (hn_norm : (ev env.toEnvironment n).Normalized P.B)
    (hbase_lt : (ev env.toEnvironment base).value P.B < (ev env.toEnvironment n).value P.B)
    (hn_pos : 0 < (ev env.toEnvironment n).value P.B) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F p)) (offset E : ℕ),
      (ev env.toEnvironment acc).Normalized P.B →
      (ev env.toEnvironment acc).value P.B < (ev env.toEnvironment n).value P.B →
      (ev env.toEnvironment acc).value P.B
        = (ev env.toEnvironment base).value P.B ^ E % (ev env.toEnvironment n).value P.B →
      env.UsesLocalWitnessesCompleteness offset
        ((modExpLoop P base n bs acc).operations offset) →
      Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env.toEnvironment e = 0,
          lookup := fun l ↦ l.Completeness env.toEnvironment,
          interact := fun i ↦ i.Guarantees env.toEnvironment, subcircuit := fun {_m} s ↦ s.ProverAssumptions env }
        ((modExpLoop P base n bs acc).operations offset) ∧
      (ev env.toEnvironment (modExpLoop P base n bs acc offset).1).Normalized P.B ∧
      (ev env.toEnvironment (modExpLoop P base n bs acc offset).1).value P.B
        < (ev env.toEnvironment n).value P.B := by
  intro bs
  induction bs with
  | nil =>
    intro acc offset E hacc_norm hacc_lt _ _
    refine ⟨?_, hacc_norm, hacc_lt⟩
    simp only [modExpLoop, Circuit.pure_operations_eq, Operations.forAllNoOffset_empty]
  | cons bit rest ih =>
    intro acc offset E hacc_norm hacc_lt hacc_val h_env
    set sqVar : Var (BigInt m) (F p) :=
      (MulMod.circuit P).output { a := acc, b := acc, modulus := n } offset with hsqVar
    have hsq_as : MulMod.Assumptions P.B ({ a := ev env.toEnvironment acc, b := ev env.toEnvironment acc, modulus := ev env.toEnvironment n } :
        MulMod.Inputs m (F p)) :=
      ⟨hacc_norm, hacc_norm, hn_norm, hacc_lt, hacc_lt, hn_pos⟩
    -- expose the bind: square subcircuit + remainder
    rw [show modExpLoop P base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulMod.circuit P) { a := sq, b := base, modulus := n }
                       else pure sq
            modExpLoop P base n rest acc') from rfl] at h_env ⊢
    rw [Circuit.bind_operations_eq] at h_env ⊢
    rw [Operations.forAllNoOffset_append]
    rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
    obtain ⟨h_sq_env, h_rest_env⟩ := h_env
    -- the square ProverSpec gives (Assumptions → Spec)
    simp only [circuit_norm, MulMod.circuit] at h_sq_env
    obtain ⟨hsq_norm, hsq_val⟩ := h_sq_env hsq_as
    set sq : Var (BigInt m) (F p) := Vector.mapRange m fun i ↦ var { index := offset + m + i } with hsq_def
    have hsq_lt : (ev env.toEnvironment sq).value P.B < (ev env.toEnvironment n).value P.B := by
      rw [hsq_val]; exact Nat.mod_lt _ hn_pos
    have hsq_pow : (ev env.toEnvironment sq).value P.B
        = (ev env.toEnvironment base).value P.B ^ (2 * E) % (ev env.toEnvironment n).value P.B := by
      rw [hsq_val, hacc_val, ← Nat.mul_mod, ← pow_add, two_mul]
    have hsqVar_eq : sqVar = sq := by
      simp only [hsqVar, hsq_def, circuit_norm, MulMod.circuit, MulMod.elaborated]
    -- conjunct 1: the square subcircuit's prover assumptions
    have hsq_pa : Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env.toEnvironment e = 0, lookup := fun l ↦ l.Completeness env.toEnvironment,
          interact := fun i ↦ i.Guarantees env.toEnvironment, subcircuit := fun {_m} s ↦ s.ProverAssumptions env }
        ((subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }).operations offset) := by
      simp only [circuit_norm, MulMod.circuit]
      exact hsq_as
    simp only [circuit_norm, MulMod.circuit, MulMod.elaborated] at hsq_pa
    cases bit
    · -- clear bit: acc' = sq, continue with exponent 2E
      simp only [Bool.false_eq_true, if_false] at h_rest_env ⊢
      simp only [circuit_norm, MulMod.circuit, MulMod.elaborated] at h_rest_env ⊢
      rw [Nat.add_comm] at h_rest_env
      obtain ⟨h_rest_pa, h_rest_norm, h_rest_lt⟩ := ih sq _ (2 * E) hsq_norm hsq_lt hsq_pow h_rest_env
      exact ⟨⟨hsq_pa, h_rest_pa⟩, h_rest_norm, h_rest_lt⟩
    · -- set bit: extra multiply, continue with exponent 2E+1
      simp only [if_true] at h_rest_env ⊢
      simp only [circuit_norm, MulMod.circuit, MulMod.elaborated] at h_rest_env ⊢
      obtain ⟨h_mul_spec, h_rest2_env⟩ := h_rest_env
      have hmul_as : MulMod.Assumptions P.B ({ a := ev env.toEnvironment sq, b := ev env.toEnvironment base, modulus := ev env.toEnvironment n } :
          MulMod.Inputs m (F p)) :=
        ⟨hsq_norm, hbase_norm, hn_norm, hsq_lt, hbase_lt, hn_pos⟩
      obtain ⟨hmul_norm, hmul_val⟩ := h_mul_spec hmul_as
      set mul : Var (BigInt m) (F p) :=
        Vector.mapRange m fun i ↦
          var { index := offset + (m + m + m * P.B + m * P.B + (m * m) + (m * m) + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m)) + m + i }
        with hmul_def
      have hmul_lt : (ev env.toEnvironment mul).value P.B < (ev env.toEnvironment n).value P.B := by
        rw [hmul_val]; exact Nat.mod_lt _ hn_pos
      have hmul_pow : (ev env.toEnvironment mul).value P.B
          = (ev env.toEnvironment base).value P.B ^ (2 * E + 1) % (ev env.toEnvironment n).value P.B := by
        rw [hmul_val]
        simp only []
        rw [hsq_pow, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]
      rw [show m + m + m * P.B + m * P.B + (m * m) + (m * m) + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m) + offset +
          (m + m + m * P.B + m * P.B + (m * m) + (m * m) + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m))
        = offset + (m + m + m * P.B + m * P.B + (m * m) + (m * m) + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m)) +
          (m + m + m * P.B + m * P.B + (m * m) + (m * m) + ((2 * m - 1) * P.W + (2 * m - 1)) + (m + m * P.B + m)) by ring] at h_rest2_env
      obtain ⟨h_rest_pa, h_rest_norm, h_rest_lt⟩ := ih mul _ (2 * E + 1) hmul_norm hmul_lt hmul_pow h_rest2_env
      exact ⟨⟨hsq_pa, hmul_as, h_rest_pa⟩, h_rest_norm, h_rest_lt⟩

/-- The channel-requirement obligations of the loop are trivially satisfied:
every `MulMod` subcircuit has empty channels. -/
lemma modExpLoop_requirements (P : BigIntParams p m) [Fact (p > 2)]
    (env : Environment (F p)) (base n : Var (BigInt m) (F p)) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      Operations.forAllNoOffset
        { interact := fun i ↦ i.Requirements env,
          subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
        ((modExpLoop P base n bs acc).operations offset) := by
  have hsub : ∀ (x : Var (MulMod.Inputs m) (F p)) (off : ℕ),
      Operations.forAllNoOffset
        { interact := fun i ↦ i.Requirements env,
          subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
        ((subcircuit (MulMod.circuit P) x).operations off) := by
    intro x off
    simp only [circuit_norm, MulMod.circuit, MulMod.elaborated]
  intro bs
  induction bs with
  | nil =>
    intro acc offset
    simp only [modExpLoop, Circuit.pure_operations_eq, Operations.forAllNoOffset_empty]
  | cons bit rest ih =>
    intro acc offset
    cases bit
    · show Operations.forAllNoOffset _ ((do
          let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
          modExpLoop P base n rest sq).operations offset)
      rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append]
      exact ⟨hsub { a := acc, b := acc, modulus := n } offset, ih _ _⟩
    · show Operations.forAllNoOffset _ ((do
          let sq ← subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }
          let acc' ← subcircuit (MulMod.circuit P) { a := sq, b := base, modulus := n }
          modExpLoop P base n rest acc').operations offset)
      rw [Circuit.bind_operations_eq, Circuit.bind_operations_eq,
        Operations.forAllNoOffset_append, Operations.forAllNoOffset_append]
      exact ⟨hsub { a := acc, b := acc, modulus := n } offset, hsub _ _, ih _ _⟩

instance elaborated (P : RSAParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P) where
  localLength _ := modExpCount P.e * mulModLen (m := m) P.bigIntParams.B P.bigIntParams.W
  localLength_eq := by
    intro input offset
    simp only [main, modExpCount]
    cases h : eBits P.e with
    | nil => simp [circuit_norm]
    | cons headBit tail =>
      exact modExpLoop_localLength P.bigIntParams _ _ tail _ offset
  subcircuitsConsistent := by
    intro input offset
    simp only [main]
    cases h : eBits P.e with
    | nil => simp [circuit_norm]
    | cons headBit tail =>
      exact modExpLoop_subcircuitsConsistent P.bigIntParams _ _ tail _ offset
  channelsLawful := by
    intro input offset
    simp only [main]
    cases h : eBits P.e with
    | nil =>
      simp only [Circuit.pure_operations_eq]
      exact Operations.channelsLawful_nil
    | cons headBit tail =>
      exact modExpLoop_channelsLawful P.bigIntParams _ _ tail _ offset

/-- Preconditions: `base` and `n` are normalized, `base < n`, and `1 < n`
(`1 < n` gives the positivity `MulMod` needs). -/
def Assumptions (_e B : ℕ)
    (input : Inputs m (F p)) : Prop :=
  let base := input.base
  let n := input.modulus
  base.Normalized B ∧ n.Normalized B ∧ base.value B < n.value B ∧
    1 < n.value B

/-- Postcondition: the output is normalized and denotes `base ^ e mod n`. -/
def Spec (e B : ℕ)
    (input : Inputs m (F p))
    (out : BigInt m (F p)) : Prop :=
  let base := input.base
  let n := input.modulus
  out.Normalized B ∧ out.value B = (base.value B) ^ e % (n.value B)

/-- The `ModExp` formal circuit: `base ^ e mod n` over normalized big integers,
parametric in the compile-time exponent `e`. -/
def circuit (P : RSAParams p m) [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P
    Assumptions := Assumptions P.e P.bigIntParams.B
    Spec := Spec P.e P.bigIntParams.B
    soundness := by
      circuit_proof_start
      obtain ⟨hbase_norm, hn_norm, hbase_lt, hn_gt1⟩ := h_assumptions
      -- rewrite assumptions in terms of evaluated inputs
      rw [← h_input] at hbase_norm hn_norm hbase_lt hn_gt1 ⊢
      simp only at hbase_norm hn_norm hbase_lt hn_gt1 ⊢
      have hn_pos : 0 < (ev env input_var.modulus).value P.bigIntParams.B :=
        lt_trans Nat.zero_lt_one hn_gt1
      -- branch on the bit list of `e`: `[]` is `e = 0` (return `1`), cons seeds `base`.
      cases h : eBits P.e with
      | nil =>
        -- `e = 0`: the circuit returns the constant `1`, and the spec is `base^0 % n = 1 % n`.
        have he0 : P.e = 0 := (eBits_eq_nil_iff P.e).mp h
        rw [h] at h_holds
        simp only at h_holds ⊢
        -- the constant `1` evaluates to `oneVal`
        have hone_eq : ev env (Vector.ofFn fun k : Fin m => if (k : ℕ) = 0 then (1 : Expression (F p)) else 0)
            = oneVal := by
          simp only [ev, oneVal, BigInt]
          ext i hi
          simp only [Vector.getElem_map, Vector.getElem_ofFn]
          by_cases h0 : i = 0 <;> simp [h0, Expression.eval]
        have hn_ne1 : (ev env input_var.modulus).value P.bigIntParams.B ≠ 1 := by
          show BigInt.value P.bigIntParams.B (Vector.map (Expression.eval env) input_var.modulus) ≠ 1
          omega
        refine ⟨⟨?_, ?_⟩, by trivial⟩
        · show (ev env (Vector.ofFn fun k : Fin m =>
            if (k : ℕ) = 0 then (1 : Expression (F p)) else 0)).Normalized P.bigIntParams.B
          rw [hone_eq]; exact oneVal_normalized P.bigIntParams.hB1
        · show (ev env (Vector.ofFn fun k : Fin m =>
            if (k : ℕ) = 0 then (1 : Expression (F p)) else 0)).value P.bigIntParams.B
            = (ev env input_var.base).value P.bigIntParams.B ^ P.e % (ev env input_var.modulus).value P.bigIntParams.B
          rw [hone_eq, value_oneVal, he0, pow_zero, Nat.one_mod_eq_one.mpr hn_ne1]
      | cons headBit tail =>
        -- `e ≥ 1`: seed the accumulator with `base` (consuming the leading `1` bit).
        have hhead : headBit = true := eBits_head_true h
        rw [h] at h_holds
        simp only at h_holds ⊢
        -- seed invariant: base.value = base.value ^ 1 % n.value
        have hbase_val : (ev env input_var.base).value P.bigIntParams.B
            = (ev env input_var.base).value P.bigIntParams.B ^ 1 % (ev env input_var.modulus).value P.bigIntParams.B := by
          rw [pow_one, Nat.mod_eq_of_lt hbase_lt]
        refine ⟨?_, modExpLoop_requirements P.bigIntParams env _ _ tail _ _⟩
        obtain ⟨hout_norm, _, hout_val⟩ :=
          modExpLoop_soundness P.bigIntParams env input_var.base input_var.modulus
            hbase_norm hn_norm hbase_lt hn_pos tail _ i₀ 1
            hbase_norm hbase_lt hbase_val h_holds
        refine ⟨hout_norm, ?_⟩
        rw [hout_val]
        -- reconstruct the exponent: 1·2^|tail| + ofBits tail = ofBits (true :: tail) = e
        have hexp : 1 * 2 ^ tail.length + ofBits tail = P.e := by
          have := ofBits_eBits P.e
          rw [h, hhead, ofBits_cons] at this
          simpa using this
        rw [hexp]
    completeness := by
      circuit_proof_start
      obtain ⟨hbase_norm, hn_norm, hbase_lt, hn_gt1⟩ := h_assumptions
      rw [← h_input] at hbase_norm hn_norm hbase_lt hn_gt1
      simp only at hbase_norm hn_norm hbase_lt hn_gt1
      have hn_pos : 0 < (ev env.toEnvironment input_var.modulus).value P.bigIntParams.B :=
        lt_trans Nat.zero_lt_one hn_gt1
      -- branch on the bit list of `e`: `[]` is `e = 0` (no subcircuits), cons seeds `base`.
      cases h : eBits P.e with
      | nil =>
        -- `e = 0`: the circuit is just the constant `1`, no operations to discharge.
        simp only [Operations.forAllNoOffset_empty]
      | cons headBit tail =>
        -- `e ≥ 1`: seed the accumulator with `base`.
        rw [h] at h_env
        simp only at h_env ⊢
        -- seed invariant: base.value = base.value ^ 1 % n.value
        have hbase_val : (ev env.toEnvironment input_var.base).value P.bigIntParams.B
            = (ev env.toEnvironment input_var.base).value P.bigIntParams.B ^ 1
              % (ev env.toEnvironment input_var.modulus).value P.bigIntParams.B := by
          rw [pow_one, Nat.mod_eq_of_lt hbase_lt]
        exact (modExpLoop_completeness P.bigIntParams env input_var.base input_var.modulus
          hbase_norm hn_norm hbase_lt hn_pos tail _ i₀ 1
          hbase_norm hbase_lt hbase_val h_env).1

/-! ## Computable witnesses -/

open Challenge.Utils.ComputableWitnessLemmas in
/-- **Structural computable-witness fact for the unrolled loop.** By induction on
the bit list: every witness of `modExpLoop` lives inside a `MulMod` subcircuit, so
its determinism follows from `MulMod.computableWitnesses`, provided the subcircuit
inputs agree. The threaded accumulator agreement (`hacc`) is propagated across
iterations using `MulMod.eval_output_of_agreesBelow`. -/
lemma modExpLoop_structuralComputableWitnesses (P : BigIntParams p m) [Fact (p > 2)]
    (parentInput : Var (Inputs m) (F p)) (base n : Var (BigInt m) (F p))
    (hbase : ∀ (e e' : ProverEnvironment (F p)),
      eval e parentInput = eval e' parentInput → eval e base = eval e' base)
    (hn : ∀ (e e' : ProverEnvironment (F p)),
      eval e parentInput = eval e' parentInput → eval e n = eval e' n)
    (bs : List Bool) :
    ∀ (acc : Var (BigInt m) (F p)) (offset : ℕ) (env env' : ProverEnvironment (F p)),
      (∀ (k : ℕ) (e e' : ProverEnvironment (F p)), offset ≤ k → e.AgreesBelow k e' →
        eval e parentInput = eval e' parentInput → eval e acc = eval e' acc) →
      FormalCircuitBase.Operations.StructuralComputableWitnesses
        parentInput env env' offset ((modExpLoop P base n bs acc).operations offset) := by
  induction bs with
  | nil =>
    intro acc offset env env' hacc
    simp only [modExpLoop, Circuit.pure_structuralComputableWitnesses_iff]
  | cons bit rest ih =>
    intro acc offset env env' hacc
    -- length/output normal forms for a `MulMod` subcircuit
    have hsublen : ∀ (X : Var (MulMod.Inputs m) (F p)) (off : ℕ),
        (subcircuit (MulMod.circuit P) X).localLength off = mulModLen (m := m) P.B P.W :=
      fun _ _ => rfl
    have hsubout : ∀ (X : Var (MulMod.Inputs m) (F p)) (off : ℕ),
        (subcircuit (MulMod.circuit P) X).output off
          = (Vector.mapRange m fun i => var (F := F p) { index := off + m + i }) := by
      intro X off; simp only [circuit_norm, MulMod.circuit, MulMod.elaborated]
    -- a `MulMod` output block agrees under any env agreement covering it
    have hblock_agree : ∀ (off k : ℕ) (e e' : ProverEnvironment (F p)),
        off + m + m ≤ k → e.AgreesBelow k e' →
        eval e (Vector.mapRange m fun i => var (F := F p) { index := off + m + i })
          = eval e' (Vector.mapRange m fun i => var (F := F p) { index := off + m + i }) := by
      intro off k e e' hk hag
      simp only [circuit_norm]
      exact MulMod.map_eval_varFromOffset_agree (off := off + m) hag (by omega)
    -- discharge one `MulMod` subcircuit given input agreement
    have discharge_sub : ∀ (X : Var (MulMod.Inputs m) (F p)) (off : ℕ),
        (∀ (k : ℕ) (e e' : ProverEnvironment (F p)), off ≤ k → e.AgreesBelow k e' →
          eval e parentInput = eval e' parentInput → eval e X = eval e' X) →
        FormalCircuitBase.Operations.StructuralComputableWitnesses parentInput env env' off
          ((subcircuit (MulMod.circuit P) X).operations off) := by
      intro X off hX
      rw [FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
      exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
        (MulMod.circuit P) parentInput X off hX (MulMod.computableWitnesses P) env env'
    cases bit
    · simp only [modExpLoop, Bool.false_eq_true, if_false,
        Circuit.bind_structuralComputableWitnesses_iff,
        Circuit.pure_structuralComputableWitnesses_iff, Circuit.pure_localLength_eq,
        Circuit.pure_output_eq, Nat.add_zero, true_and, hsublen]
      refine ⟨discharge_sub _ offset ?_, ?_⟩
      · intro k e e' hk hag hin
        have ha := hacc k e e' hk hag hin
        have hnn := hn e e' hin
        simp only [circuit_norm] at ha hnn ⊢
        simp only [ha, hnn]
      · refine ih _ _ env env' ?_
        intro k e e' hk hag _
        rw [hsubout _ offset]
        exact hblock_agree offset k e e' (by simp only [mulModLen] at hk ⊢; omega) hag
    · simp only [modExpLoop, if_true,
        Circuit.bind_structuralComputableWitnesses_iff, hsublen]
      refine ⟨discharge_sub _ offset ?_, discharge_sub _ (offset + mulModLen (m := m) P.B P.W) ?_, ?_⟩
      · intro k e e' hk hag hin
        have ha := hacc k e e' hk hag hin
        have hnn := hn e e' hin
        simp only [circuit_norm] at ha hnn ⊢
        simp only [ha, hnn]
      · intro k e e' hk hag hin
        have hbb := hbase e e' hin
        have hnn := hn e e' hin
        have hsq : eval e ((subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }).output offset)
            = eval e' ((subcircuit (MulMod.circuit P) { a := acc, b := acc, modulus := n }).output offset) := by
          rw [hsubout _ offset]
          exact hblock_agree offset k e e' (by simp only [mulModLen] at hk ⊢; omega) hag
        simp only [circuit_norm] at hbb hnn hsq ⊢
        simp only [hsq, hbb, hnn]
      · refine ih _ _ env env' ?_
        intro k e e' hk hag _
        rw [hsubout _ (offset + mulModLen (m := m) P.B P.W)]
        exact hblock_agree (offset + mulModLen (m := m) P.B P.W) k e e'
          (by simp only [mulModLen] at hk ⊢; omega) hag

/-- **Output agreement for the unrolled loop.** The final accumulator is either
the seed `acc` (empty list) or a `MulMod` output block; in both cases it agrees
across environments that coincide on the seed and below the whole loop. -/
lemma modExpLoop_eval_output_of_agreesBelow (P : BigIntParams p m) [Fact (p > 2)]
    (base n : Var (BigInt m) (F p)) (bs : List Bool) :
    ∀ (acc : Var (BigInt m) (F p)) (offset : ℕ) (env env' : ProverEnvironment (F p)),
      eval env acc = eval env' acc →
      env.AgreesBelow (offset + (bs.length + bs.count true) * mulModLen (m := m) P.B P.W) env' →
      eval env ((modExpLoop P base n bs acc).output offset)
        = eval env' ((modExpLoop P base n bs acc).output offset) := by
  induction bs with
  | nil =>
    intro acc offset env env' hacc _
    simp only [modExpLoop, Circuit.pure_output_eq]
    exact hacc
  | cons bit rest ih =>
    intro acc offset env env' hacc hag
    have h2mL : 2 * m ≤ mulModLen (m := m) P.B P.W := by simp only [mulModLen]; omega
    have hsublen : ∀ (X : Var (MulMod.Inputs m) (F p)) (off : ℕ),
        (subcircuit (MulMod.circuit P) X).localLength off = mulModLen (m := m) P.B P.W :=
      fun _ _ => rfl
    have hsubout : ∀ (X : Var (MulMod.Inputs m) (F p)) (off : ℕ),
        (subcircuit (MulMod.circuit P) X).output off
          = (Vector.mapRange m fun i => var (F := F p) { index := off + m + i }) := by
      intro X off; simp only [circuit_norm, MulMod.circuit, MulMod.elaborated]
    have hblock : ∀ (off : ℕ),
        off + m + m ≤ offset + ((bit :: rest).length + (bit :: rest).count true) * mulModLen (m := m) P.B P.W →
        eval env (Vector.mapRange m fun i => var (F := F p) { index := off + m + i })
          = eval env' (Vector.mapRange m fun i => var (F := F p) { index := off + m + i }) := by
      intro off hoff
      simp only [circuit_norm]
      exact MulMod.map_eval_varFromOffset_agree (off := off + m)
        (ProverEnvironment.agreesBelow_of_le hag hoff) (by omega)
    cases bit
    · simp only [modExpLoop, Bool.false_eq_true, if_false, Circuit.bind_output_eq,
        Circuit.pure_output_eq, Circuit.pure_localLength_eq, Nat.add_zero, hsublen]
      refine ih _ _ env env' ?_ ?_
      · rw [hsubout _ offset]
        refine hblock offset ?_
        have hpos : 0 < (false :: rest).length + (false :: rest).count true := by
          simp only [List.length_cons]; omega
        have hml : m + m ≤ ((false :: rest).length + (false :: rest).count true)
            * mulModLen (m := m) P.B P.W :=
          le_trans (by omega) (Nat.le_mul_of_pos_left _ hpos)
        omega
      · refine ProverEnvironment.agreesBelow_of_le hag (le_of_eq ?_)
        simp only [List.length_cons, List.count_cons, Bool.false_eq_true, if_false, Nat.add_zero,
          beq_iff_eq]
        ring
    · simp only [modExpLoop, if_true, Circuit.bind_output_eq, hsublen]
      refine ih _ _ env env' ?_ ?_
      · rw [hsubout _ (offset + mulModLen (m := m) P.B P.W)]
        refine hblock (offset + mulModLen (m := m) P.B P.W) ?_
        have hc2 : 2 ≤ (true :: rest).length + (true :: rest).count true := by
          simp only [List.length_cons, List.count_cons, beq_self_eq_true, if_true]; omega
        have h2L : 2 * mulModLen (m := m) P.B P.W
            ≤ ((true :: rest).length + (true :: rest).count true) * mulModLen (m := m) P.B P.W :=
          Nat.mul_le_mul hc2 (le_refl _)
        omega
      · refine ProverEnvironment.agreesBelow_of_le hag (le_of_eq ?_)
        simp only [List.length_cons, List.count_cons, beq_self_eq_true, if_true]
        ring

/-- **Output agreement for `ModExp`.** Mirrors `MulMod.eval_output_of_agreesBelow`;
used by `Main`. The output is the loop's final accumulator (a `MulMod` block or,
for a trivial exponent, the seed / the constant `1`), which agrees under input
agreement and env agreement covering the whole circuit. -/
lemma eval_output_of_agreesBelow {offset : ℕ} {env env' : ProverEnvironment (F p)}
    (P : RSAParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p))
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow (offset + (circuit P).localLength input) env') :
    eval env ((main P input).output offset) = eval env' ((main P input).output offset) := by
  have hbin : eval env input.base = eval env' input.base := by
    have hm := congrArg (fun s : Inputs m (F p) => s.base) h_input
    simp only [circuit_norm] at hm ⊢; exact hm
  have hlen : (circuit P).localLength input
      = modExpCount P.e * mulModLen (m := m) P.bigIntParams.B P.bigIntParams.W := rfl
  rw [hlen] at h_agree
  unfold main
  cases h : eBits P.e with
  | nil =>
    simp only [circuit_norm]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    split <;> rfl
  | cons headBit tail =>
    simp only [modExpCount, h] at h_agree
    exact modExpLoop_eval_output_of_agreesBelow P.bigIntParams input.base input.modulus tail
      input.base offset env env' hbin h_agree

/-- Circuit-level (subcircuit) output agreement, bridging `eval_output_of_agreesBelow`
through `elaborated.output_eq`. Mirrors `CompressBlock.eval_circuit_output_of_agreesBelow`;
used by `Main`. -/
lemma eval_circuit_output_of_agreesBelow {offset : ℕ} {env env' : ProverEnvironment (F p)}
    (P : RSAParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p))
    (h_input : eval env input = eval env' input)
    (h_agree : env.AgreesBelow (offset + (circuit P).localLength input) env') :
    eval env ((circuit P).output input offset)
      = eval env' ((circuit P).output input offset) := by
  change eval env (ElaboratedCircuit.output (main P) input offset) =
    eval env' (ElaboratedCircuit.output (main P) input offset)
  rw [← (elaborated P).output_eq input offset]
  exact eval_output_of_agreesBelow P input h_input h_agree

open Challenge.Utils.ComputableWitnessLemmas in
/-- **Computable witnesses for `ModExp`.** All witnesses live inside `MulMod`
subcircuits; the seed accumulator `base = input.base` and the modulus
`n = input.modulus` agree via the parent input, so the loop lemma discharges the
structural obligation. -/
theorem computableWitnesses (P : RSAParams p m) [Fact (p > 2)] :
    (circuit P).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main P input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  have hbase : ∀ (e e' : ProverEnvironment (F p)),
      eval e input = eval e' input → eval e input.base = eval e' input.base := by
    intro e e' hin
    have hm := congrArg (fun s : Inputs m (F p) => s.base) hin
    simp only [circuit_norm] at hm ⊢; exact hm
  have hn : ∀ (e e' : ProverEnvironment (F p)),
      eval e input = eval e' input → eval e input.modulus = eval e' input.modulus := by
    intro e e' hin
    have hm := congrArg (fun s : Inputs m (F p) => s.modulus) hin
    simp only [circuit_norm] at hm ⊢; exact hm
  unfold main
  cases h : eBits P.e with
  | nil =>
    simp only [Circuit.pure_structuralComputableWitnesses_iff]
  | cons headBit tail =>
    exact modExpLoop_structuralComputableWitnesses P.bigIntParams input input.base input.modulus
      hbase hn tail input.base offset env env'
      (fun k e e' _ _ hin => hbase e e' hin)

end ModExp

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
