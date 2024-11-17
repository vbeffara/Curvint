import Lake
open Lake DSL

package «curvint» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "e7301b9"

@[default_target]
lean_lib «Curvint» where
  -- add any library configuration options here
