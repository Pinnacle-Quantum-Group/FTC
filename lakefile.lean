import Lake
open Lake DSL

package «ftcFormalProofs» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.5.0"

@[default_target]
lean_lib «FTC» where
  srcDir := "formal_proofs"
  globs := #[.submodules `FTC]
