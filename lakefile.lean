import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Clean where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.25.2"
require lspec from git "https://github.com/argumentcomputer/lspec.git"@"fdf848d6cda9f080a09e49e760e2d6f70878800b"
