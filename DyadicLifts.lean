/-
# Lean formalization of `dyadic_lifts.tex` / `Lean/dyadic_theorem_lean.tex`

The nonadditive dyadic Bell ladder for two-sector SS--LP quantum codes.

Module map (bottom-up dependency order):

* `DyadicLifts.BitStringAux`  — bitstrings, weight, distance, integer subset sum,
                                append/split identities.
* `DyadicLifts.Hilbert`       — the computational Hilbert space `ℋ_n`, inner product,
                                tensor split, inner-product factorization.
* `DyadicLifts.PauliCoord`    — bare Pauli strings via coordinate action, transition
                                support, matrix-element tensor factorization.
* `DyadicLifts.KL`            — the Knill–Laflamme predicates `KLmat`, `KL`.
* `DyadicLifts.SSResidue`     — SS residue blocks, disjointness, the transversal
                                diagonal `U_m(a)` and the induced logical diagonal.
* `DyadicLifts.Bell`          — Bell parity flags and the full Bell-pair Pauli table.
* `DyadicLifts.CyclicOrder`   — `D_m`, `R_m`, cyclic orders, binary-dihedral relations.
* `DyadicLifts.Lift`          — the dyadic Bell lift: definition, Bell normal form,
                                linearity, isometry.
* `DyadicLifts.Combinatorics` — two-value subset sums, strong-seed hypotheses.
* `DyadicLifts.LiftDiagonal`  — the SS-residue / diagonal action of the lift
                                (phase doubling).
* `DyadicLifts.SelfComplement`— self-complementarity and its preservation under the lift.
* `DyadicLifts.Ladder`        — iterated dyadic ladder data and iterated diagonal action.
* `DyadicLifts.DistanceTheorem`— the two-anchor distance-`3` ladder theorem (statement
                                and propagation scaffold).
-/

import DyadicLifts.BitStringAux
import DyadicLifts.Hilbert
import DyadicLifts.PauliCoord
import DyadicLifts.KL
import DyadicLifts.SSResidue
import DyadicLifts.Bell
import DyadicLifts.CyclicOrder
import DyadicLifts.Lift
import DyadicLifts.BellLift
import DyadicLifts.PauliHerm
import DyadicLifts.Combinatorics
import DyadicLifts.LiftDiagonal
import DyadicLifts.CarryTag
import DyadicLifts.SelfComplement
import DyadicLifts.Ladder
import DyadicLifts.AnchorRecursion
import DyadicLifts.NoSmallWeight
import DyadicLifts.AnchorCoeff
import DyadicLifts.BellEnum
import DyadicLifts.KLStep
import DyadicLifts.AnchorEq
import DyadicLifts.Buddy
import DyadicLifts.AnchorLeakage
import DyadicLifts.DistanceTheorem
import DyadicLifts.LogicalGroup
import DyadicLifts.Bridge
import DyadicLifts.AxiomCheck
