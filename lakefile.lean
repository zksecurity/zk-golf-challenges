import Lake
open Lake DSL

package Circuits where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Challenge where
  globs := #[.submodules `Challenge]

lean_lib Tests where
  globs := #[.submodules `Tests]

lean_lib Solution where
  globs := #[.submodules `Solution]

require clean from git "https://github.com/Verified-zkEVM/clean" @ "main"
