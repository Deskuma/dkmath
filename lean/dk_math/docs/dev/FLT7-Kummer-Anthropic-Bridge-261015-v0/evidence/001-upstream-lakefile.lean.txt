import Lake
open Lake DSL

package flt_e2e where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`maxHeartbeats, (4000000 : Nat)⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩,
    ⟨`backward.isDefEq.respectTransparency.types, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

lean_lib P2M where
  globs := #[.submodules `P2M]

lean_lib Definitions where
  globs := #[.submodules `Definitions]

lean_lib Theorems where
  globs := #[.submodules `Theorems]

@[default_target]
lean_lib FinalCheck where
  roots := #[`FinalCheck]
