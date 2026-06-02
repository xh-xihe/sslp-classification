import Lake
open Lake DSL

package ss where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib SS where

@[default_target]
lean_lib Examples where

-- Formalization of `dyadic_lifts.tex` / `dyadic_theorem_lean.tex`:
-- the nonadditive dyadic Bell ladder for two-sector SS--LP codes.
@[default_target]
lean_lib DyadicLifts where
