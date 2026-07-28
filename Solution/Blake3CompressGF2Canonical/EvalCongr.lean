import Challenge.Instances.Blake3CompressGF2Canonical.Interface
import Challenge.Utils.ComputableWitnessLemmas

/-!
# `eval`-agreement toolkit for `fields N` variables

Every gadget in this instance takes flat `fields N` bit vectors (or structs of
them), so the `computableWitness` obligations all reduce to: two prover
environments that evaluate a vector's entries alike evaluate any derived vector
alike. This file gives the pointwise view of `eval` agreement, plus the
`AgreesBelow` bridges for freshly witnessed (`varFromOffset`) blocks.
-/

namespace Solution.Blake3CompressGF2Canonical

open Challenge.Instances.Blake3CompressGF2Canonical.Interface
open Challenge.F2Bits

variable {N : ℕ} {u : Var (fields N) (F p2)} {env env' : ProverEnvironment (F p2)}

/-- `eval` agreement on a `fields N` variable is entrywise agreement. -/
theorem eval_fields_iff (u : Var (fields N) (F p2)) (env env' : ProverEnvironment (F p2)) :
    eval env u = eval env' u ↔
      ∀ (k : ℕ) (hk : k < N),
        Expression.eval env.toEnvironment (u[k]'hk)
          = Expression.eval env'.toEnvironment (u[k]'hk) := by
  rw [CircuitType.eval_var_fields_prover, CircuitType.eval_var_fields_prover]
  constructor
  · intro h k hk
    have h2 := Vector.ext_iff.mp h k hk
    rwa [Vector.getElem_map, Vector.getElem_map] at h2
  · intro h
    refine Vector.ext fun k hk => ?_
    rw [Vector.getElem_map, Vector.getElem_map]
    exact h k hk

theorem eval_getElem_congr (h : eval env u = eval env' u) (k : ℕ) (hk : k < N) :
    Expression.eval env.toEnvironment (u[k]'hk)
      = Expression.eval env'.toEnvironment (u[k]'hk) :=
  (eval_fields_iff u env env').mp h k hk

theorem eval_fields_of_getElem
    (h : ∀ (k : ℕ) (hk : k < N),
      Expression.eval env.toEnvironment (u[k]'hk)
        = Expression.eval env'.toEnvironment (u[k]'hk)) :
    eval env u = eval env' u :=
  (eval_fields_iff u env env').mpr h

/-- A freshly witnessed block evaluates alike under environments agreeing below its top. -/
theorem eval_varFromOffset_of_agreesBelow {m offset k : ℕ}
    (h_agree : env.AgreesBelow k env') (hk : offset + m ≤ k) :
    eval env (varFromOffset (fields m) offset : Var (fields m) (F p2))
      = eval env' (varFromOffset (fields m) offset : Var (fields m) (F p2)) := by
  refine eval_fields_of_getElem fun i hi => ?_
  rw [ProvableType.varFromOffset_fields]
  simp only [circuit_norm]
  exact h_agree (offset + i) (by omega)

end Solution.Blake3CompressGF2Canonical
