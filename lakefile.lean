import Lake
open Lake DSL

package «lean-agm» where
  description := "Representation-based algebraic adversaries and adaptive oracle interaction."
  license := "Apache-2.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @
  "f5119c64ebb055d69c143704e12eba6df7dc386c"

@[default_target]
lean_lib AlgebraicGroupModel

lean_lib AGMTest where
  globs := #[.submodules `AGMTest]
  allowNonModules := true
