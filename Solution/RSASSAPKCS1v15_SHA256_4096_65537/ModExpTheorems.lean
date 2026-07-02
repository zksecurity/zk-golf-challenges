import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExp

/-!
# A shallow closed form for the `ModExp` output variable

`circuit_proof_start` on the top-level RSA circuit embeds
`(ModExp.circuit P).output …` in the resulting goal. By default this is
`(ModExp.main P input).output offset`, whose normal form runs the entire
unrolled square-and-multiply loop — a term so deep the kernel/elaborator hits
its recursion limit when the goal is touched.

Here we give that output a shallow `varFromOffset` closed form and register it
with `circuit_norm`, so the offset machinery in `circuit_proof_start` rewrites it
to a small term and the soundness proof stays tractable.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace ModExp

open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-- The output variable of the unrolled loop is a `varFromOffset` placed after
all the `MulMod` witnesses: for a **non-empty** bit list it sits `m` slots into
the last (of `count`) `MulMod` blocks, i.e. at `offset + (count − 1)·mulModLen + m`.
We phrase the offset as `offset + count·mulModLen + m − mulModLen` to keep the
arithmetic linear (`count ≥ 1`, so no truncated subtraction surprises). -/
lemma modExpLoop_output (P : BigIntParams p m) [Fact (p > 2)]
    (base n : Var (BigInt m) (F p)) (bit : Bool) :
    ∀ (rest : List Bool) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      (modExpLoop P base n (bit :: rest) acc).output offset
        = varFromOffset (BigInt m)
            (offset + ((bit :: rest).length + (bit :: rest).count true) * mulModLen (m := m) P.B P.W
              + m - mulModLen (m := m) P.B P.W) := by
  have hML : ∀ (x : Var (MulMod.Inputs m) (F p)),
      (MulMod.circuit P).localLength x = mulModLen (m := m) P.B P.W := fun _ => rfl
  have hstep : ∀ (bs : List Bool) (acc' : Var (BigInt m) (F p)) (o : ℕ),
      (modExpLoop P base n bs acc' o).1 = (modExpLoop P base n bs acc').output o := fun _ _ _ => rfl
  -- We need the general loop output for arbitrary head + tail, by induction on the
  -- whole `bit :: rest`; restate as induction on a generic non-empty list.
  suffices H : ∀ (bs : List Bool) (acc : Var (BigInt m) (F p)) (offset : ℕ), bs ≠ [] →
      (modExpLoop P base n bs acc).output offset
        = varFromOffset (BigInt m)
            (offset + (bs.length + bs.count true) * mulModLen (m := m) P.B P.W
              + m - mulModLen (m := m) P.B P.W) by
    intro rest acc offset
    exact H (bit :: rest) acc offset (by simp)
  intro bs
  induction bs with
  | nil => intro acc offset hne; exact absurd rfl hne
  | cons b rest ih =>
    intro acc offset _
    set L := mulModLen (m := m) P.B P.W with hL
    have hLpos : 1 ≤ (b :: rest).length + (b :: rest).count true := by
      simp only [List.length_cons]; omega
    cases b
    · -- clear bit: 1 square, then loop on `rest`
      show (modExpLoop P base n rest
          (Vector.mapRange m fun i => var { index := offset + m + i })
          (offset + (MulMod.circuit P).localLength { a := acc, b := acc, modulus := n })).1 = _
      rw [hML, hstep]
      cases rest with
      | nil =>
        rw [show (modExpLoop P base n [] (Vector.mapRange m fun i => var { index := offset + m + i })).output
              (offset + L) = (Vector.mapRange m fun i => var { index := offset + m + i }) from rfl,
            ProvableType.varFromOffset_fields]
        simp only [List.length_cons, List.count_cons, List.length_nil, List.count_nil,
          Nat.zero_add]
        have hif : (if (false == true) = true then (1:ℕ) else 0) = 0 := by simp
        apply Vector.ext
        intro i hi
        simp only [Vector.getElem_mapRange, hif, Nat.add_zero, Nat.one_mul]
        congr 2
        omega
      | cons b2 r2 =>
        rw [ih _ _ (by simp)]
        congr 1
        simp only [List.length_cons, List.count_cons]
        -- the two index expressions differ by `c·L + L = (c+1)·L`
        have hif : (if (false == true) = true then (1:ℕ) else 0) = 0 := by simp
        rw [hif, Nat.add_zero]
        simp only [Nat.add_zero]
        generalize (if (b2 == true) = true then (1:ℕ) else 0) = e2
        have hkey : (r2.length + 1 + (List.count true r2 + e2)) * L + L
            = (r2.length + 1 + 1 + (List.count true r2 + e2)) * L := by
          rw [← Nat.add_one_mul]
          congr 1
          omega
        omega
    · -- set bit: square + multiply, then loop on `rest`
      show (modExpLoop P base n rest
          ((MulMod.circuit P).output
            { a := (MulMod.circuit P).output { a := acc, b := acc, modulus := n } offset,
              b := base, modulus := n }
            (offset + (MulMod.circuit P).localLength { a := acc, b := acc, modulus := n }))
          (offset + (MulMod.circuit P).localLength { a := acc, b := acc, modulus := n } +
            (MulMod.circuit P).localLength
              { a := (MulMod.circuit P).output { a := acc, b := acc, modulus := n } offset,
                b := base, modulus := n })).1 = _
      rw [hML, hML, hstep]
      cases rest with
      | nil =>
        show (varFromOffset (BigInt m) (offset + L + m) : (BigInt m) (Expression (F p)))
            = varFromOffset (BigInt m) _
        congr 1
        simp only [List.length_cons, List.count_cons, List.length_nil, List.count_nil, if_true,
          beq_self_eq_true, Nat.zero_add]
        rw [show (1 + 1) * L = L + L from by ring]
        omega
      | cons b2 r2 =>
        rw [ih _ _ (by simp)]
        congr 1
        simp only [List.length_cons, List.count_cons]
        have hif : (if (true == true) = true then (1:ℕ) else 0) = 1 := by simp
        rw [hif]
        have hkey : (r2.length + 1 + (List.count true r2 + (if (b2 == true) = true then 1 else 0))) * L
              + L + L
            = (r2.length + 1 + 1
                + ((List.count true r2 + (if (b2 == true) = true then 1 else 0)) + 1)) * L := by
          rw [show (r2.length + 1 + 1
                + ((List.count true r2 + (if (b2 == true) = true then 1 else 0)) + 1))
              = (r2.length + 1 + (List.count true r2 + (if (b2 == true) = true then 1 else 0))) + 1 + 1
              from by omega]
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
          ring
        omega

/-- Shallow closed form for the top-level `ModExp.main` output **when the tail of
`eBits P.e` is non-empty** (the case for every `e ≥ 2`, in particular
`e = 65537`). Registered with `circuit_norm` so it fires inside
`circuit_proof_start`, keeping the resulting goal small. -/
@[circuit_norm]
lemma main_output_of_tail (P : RSAParams p m) [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) (offset : ℕ)
    (headBit : Bool) (b2 : Bool) (r2 : List Bool)
    (h : eBits P.e = headBit :: b2 :: r2) :
    (main P input).output offset
      = varFromOffset (BigInt m)
          (offset + ((b2 :: r2).length + (b2 :: r2).count true)
              * mulModLen (m := m) P.bigIntParams.B P.bigIntParams.W
            + m - mulModLen (m := m) P.bigIntParams.B P.bigIntParams.W) := by
  simp only [main, h]
  show (modExpLoop P.bigIntParams input.base input.modulus (b2 :: r2) input.base).output offset = _
  exact modExpLoop_output P.bigIntParams input.base input.modulus b2 r2 input.base offset

end

end ModExp
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
