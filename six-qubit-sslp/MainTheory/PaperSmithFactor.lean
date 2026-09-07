import MainTheory.DeterminantalFactor
import MainTheory.FiniteLift
import MainTheory.D3FreshSparseAssembly

/-!
# `q | d_r(C)` in the paper's own notation

`lem:denominator-clearing` and `thm:d3-bound` both end on the divisibility

  `q | d_r(C)`,

with `d_r(C)` the last invariant factor of the pivot matrix.  This repository
proved the divisibility against `SharpClearing.inverseDenominator` and then
stalled: `sharp_pivot_divisibility_smith` converts the conclusion into the
paper's `d_s(C)` "for a pivot that carries a witness", and at that point
nothing carried one, because a `SmithWitness` asks for unimodular `U` and `V`
with `U C V` diagonal *and* the divisibility chain, which Mathlib does not
build.

`DeterminantalFactor` removes the need for a witness by identifying
`inverseDenominator` with the last invariant factor through the determinantal
divisors instead of through a Smith form.  This file states the two paper
divisibilities against that number.  `SmithExistence` later supplied the
witness as well, so `PivotSmithNormalForm` states the same divisibilities
against an actual normal form; the two agree, since `lastFactor` is
witness-independent.

Both pivots are covered, exactly as `results` records them: the coloured one
of `lem:denominator-clearing`, and the sparse one that `thm:d3-bound`'s fresh
phase produces.
-/

namespace MainTheory.PaperSmithFactor

open MainTheory
open MainTheory.DeterminantalFactor

/-- **`lem:denominator-clearing` with `d_r(C)`.**

The coloured pivot's physical order divides the last invariant factor of its
own pivot matrix. -/
theorem colouredPivot_order_dvd_lastInvariantFactor
    {n t : ℕ} {theta : Fin n → ℝ} {D : PhaseSectorFull.SectorDecomposition n t theta}
    {s : Type*} [Fintype s] [DecidableEq s] [Nonempty s]
    (P : FiniteLift.PivotData D s)
    (hdet : P.matrix.det ≠ 0) (hZ : PhaseSectorFull.ZDetects D) :
    (P.rationalLift hdet hZ).order ∣ lastInvariantFactor P.matrix :=
  dvd_lastInvariantFactor hdet (FiniteLift.sharp_pivot_divisibility P hdet hZ)

/-- **`thm:d3-bound` with `d_r(C)`.**

The sparse pivot's physical order divides the last invariant factor of its own
binary minor.  This is the `q | d_r(C)` clause of the theorem, at the pivot the
distance-three route actually builds. -/
theorem sparsePivot_order_dvd_lastInvariantFactor
    {n : ℕ} {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : D3FreshSparseAssembly.FreshSparsePhase c d theta)
    [Nonempty (Fin F.basis.rank)] :
    F.data.order ∣ lastInvariantFactor F.data.minor :=
  dvd_lastInvariantFactor F.data.minor_nonsingular
    F.order_dvd_inverseDenominator

/-- The same, with the nonemptiness supplied by the pivot's own positive
rank rather than assumed. -/
theorem sparsePivot_order_dvd_lastInvariantFactor' {n : ℕ}
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : D3FreshSparseAssembly.FreshSparsePhase c d theta)
    (hpos : 0 < F.basis.rank) :
    F.data.order ∣ lastInvariantFactor F.data.minor := by
  haveI : Nonempty (Fin F.basis.rank) := Fin.pos_iff_nonempty.1 hpos
  exact sparsePivot_order_dvd_lastInvariantFactor F

end MainTheory.PaperSmithFactor
