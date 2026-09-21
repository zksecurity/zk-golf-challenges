import Lean.Elab.Tactic.Simp

/-!
# The `nval_norm` simp set

`Solution/SHA256/WitgenU64.lean` populates this set; it rewrites a u64-sorted witness
program's `nval` down to `ℕ` arithmetic. Registering a simp attribute has to happen in
a module of its own, so this file holds nothing else.
-/

register_simp_attr nval_norm
