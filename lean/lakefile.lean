import Lake
open Lake DSL

package «dyadic-lifts-kernel» where
  version := v!"0.2.0"
  -- The seed's Knill--Laflamme checks enumerate `Finset.univ` over `BitString 9`
  -- by structural recursion, which overflows the default 8 MB thread stack.
  -- Two gigabytes is ample; the value is reserved address space, not committed
  -- memory.
  moreLeanArgs := #["-s", "2000000"]
  moreGlobalServerArgs := #["-s", "2000000"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

/-- Bitstrings, bare Pauli strings, and the exact fields `ℚ(√2,√3,√5,i)` and
`ℤ[√2,√3,√5,i]` in which the seed's amplitudes live.  These modules are shared
with the SSLP development, which keeps its own copy; nothing specific to that
project is carried here. -/
@[default_target]
lean_lib SS where
  globs := #[.submodules `SS]

/-- Formalization of `dyadic_lifts.tex`: the nonadditive dyadic Bell ladder for
two-sector SS--LP codes, together with the explicit `((7,2,3))` seed under
`DyadicLifts.Seed`.

Every result the paper states is proved here by the Lean kernel alone --- the
tactic `native_decide` is used nowhere, so neither the Lean compiler nor its
runtime is trusted.  Two guards run in this default target and fail the build if
that ever stops being true: `DyadicLifts.AxiomCheck` for the abstract ladder and
`DyadicLifts.Seed.Audit` for the seed and the unconditional family. -/
@[default_target]
lean_lib DyadicLifts where
  globs := #[.andSubmodules `DyadicLifts]
