import Lake

open Lake DSL

package GAC where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- Boundedness and persistence (`GAC.Persistence`), global convergence under detailed balance, and the declarations used in the paper.
Source and license of `GAC/Persistence/` are recorded in `docs/SOURCE_MAP.md`. -/
@[default_target]
lean_lib GAC where
  globs := #[.andSubmodules `GAC]
