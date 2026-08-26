import Lake
open Lake DSL

package «six-qubit-nogo» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

/-- Shared bitstring / Pauli / Knill--Laflamme infrastructure, copied unchanged
from the SSLP development so that this package is self-contained. -/
@[default_target]
lean_lib SS where
  globs := #[.submodules `SS]

/-- Kernel-only no-go certifications for the six-qubit distance-three
classification of `six_qubit_sslp.tex`. -/
@[default_target]
lean_lib SixQubit where
  globs := #[.andSubmodules `SixQubit]
