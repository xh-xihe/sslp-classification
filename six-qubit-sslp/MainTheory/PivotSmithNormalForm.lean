import MainTheory.SmithNormalFormExistence
import MainTheory.SortedPivot
import MainTheory.SixQubitSemanticEntrance

/-!
# `q | d_r(C)` against an actual Smith normal form

`lem:denominator-clearing` and `thm:d3-bound` end on `q | d_r(C)`, with
`d_r(C)` the last invariant factor of the pivot matrix.  Two earlier files
route around the Smith form rather than through it, and each says so in its
header: `PaperSmithFactor` reaches the same number through determinantal
divisors, and `SupportAffineRank` records the clause as open because "nothing
in the repository or in Mathlib can build" a `SharpClearing.SmithWitness`.

That is no longer true.  `SmithExistence.exists_normalized_smith` builds one
for any nonsingular integer matrix, by minimising a measure over actual
positive diagonal reductions, and every pivot in the pipeline carries
`nonsingular : matrix.det != 0` as a field.  So the paper's statement can be
made in the paper's own terms, with no supplied witness and no detour.

Two things are proved here, and the pair is what makes the statement complete:

* every witness for a pivot has `q` dividing its last factor -- a `forall`,
  not an existential, so no choice of normal form is being smuggled in; and
* a witness exists.

The `forall` is not weaker than it looks.  `lastFactor` is witness-independent
by `inverseDenominator_eq_smithLastFactor`, so "the" last invariant factor is
well defined and the two statements together say exactly `q | d_r(C)`.  The
explicit displays below unfold `SmithWitness` into the manuscript's `U C V =
diag(d)` with `|det U| = |det V| = 1` and the divisibility chain, so a reader
checking the paper never has to open the structure.
-/

namespace MainTheory.PivotSmithNormalForm

open MainTheory
open MainTheory.SharpClearing

/-! ## `lem:denominator-clearing` against `d_s(C)` -/

section Clearing

/-- **`lem:denominator-clearing`, `eq:clear-denom`.**

If `C z = h` with `h` integral, then `d_s(C) z` is integral, and the least
common denominator of `z` divides `d_s(C)`.

The manuscript reads `d_s(C)` off the Smith form `eq:snf`; the repository
proves both clauses against `inverseDenominator` and identifies the two
numbers.  Stating them on a supplied witness makes the conclusion the
manuscript's, and `nonempty_smithWitness_of_det` says such a witness always
exists, so no hypothesis has been added. -/
theorem clearing_smithLastFactor {s : Type*} [Fintype s] [DecidableEq s]
    [LinearOrder s] [Nonempty s]
    (C : Matrix s s ℤ) (hdet : C.det ≠ 0)
    (h : s → ℤ) (z : s → ℚ)
    (hz : (ratMatrix C).mulVec z = fun i => (h i : ℚ))
    (w : SmithWitness C) :
    (∃ k : s → ℤ, ∀ i, (w.lastFactor : ℚ) * z i = (k i : ℚ)) ∧
      Denominator.lcmDen z ∣ w.lastFactor := by
  rw [← inverseDenominator_eq_smithLastFactor w]
  exact ⟨exists_sharply_cleared_solution C h z hdet hz,
    solution_lcmDen_dvd_inverseDenominator C h z hdet hz⟩

/-- A witness always exists, so `clearing_smithLastFactor` is unconditional. -/
theorem nonempty_smithWitness_of_det {s : Type*} [Fintype s] [DecidableEq s]
    [LinearOrder s] [LocallyFiniteOrderBot s]
    (C : Matrix s s ℤ) (hdet : C.det ≠ 0) :
    Nonempty (SmithWitness C) :=
  SmithExistence.exists_normalized_smith C hdet

end Clearing

/-! ## The sorted-normal-form pivot -/

section Sorted

open MainTheory.SortedForm
open MainTheory.SortedPivot

variable {C : CodeSpec.ExactCode 6 2 3}

/-- A pivot has positive rank, so its index type is nonempty; needed for
`lastIndex` to appear in a statement rather than only inside a proof. -/
instance instNeZeroRank {S : SortedNormalForm C} (P : Pivot S) : NeZero P.rank :=
  ⟨by have := P.rank_pos; omega⟩

/-- The pivot matrix is nonsingular, so it has a Smith normal form. -/
theorem nonempty_smithWitness {S : SortedNormalForm C} (P : Pivot S) :
    Nonempty (SmithWitness P.matrix) := by
  exact SmithExistence.exists_normalized_smith P.matrix P.nonsingular

/-- **`q | d_r(C)`, for every Smith normal form of the pivot matrix.**

Stated for an arbitrary witness rather than a constructed one: the last
invariant factor does not depend on which reduction is used
(`inverseDenominator_eq_smithLastFactor`), so this is the paper's number. -/
theorem q_dvd_smithLastFactor {S : SortedNormalForm C} (P : Pivot S)
    (w : SmithWitness P.matrix) : S.q ∣ w.lastFactor := by
  rw [← inverseDenominator_eq_smithLastFactor w]
  exact P.q_dvd_inverseDenominator

/-- **The manuscript's display.**

Unimodular `U`, `V` over the integers, a positive divisibility chain `d`, the
reduction `U C V = diag(d)`, and `q` dividing the last entry. -/
theorem exists_smithNormalForm_q_dvd_last {S : SortedNormalForm C} (P : Pivot S) :
    ∃ (U V : Matrix (Fin P.rank) (Fin P.rank) ℤ) (dd : Fin P.rank → ℕ),
      U.det.natAbs = 1 ∧ V.det.natAbs = 1 ∧
      (∀ i, 0 < dd i) ∧ (∀ ⦃i j⦄, i ≤ j → dd i ∣ dd j) ∧
      U * P.matrix * V = Matrix.diagonal (fun i => (dd i : ℤ)) ∧
      S.q ∣ dd (lastIndex (s := Fin P.rank)) := by
  obtain ⟨w⟩ := nonempty_smithWitness P
  exact ⟨w.U, w.V, w.factor,
    Int.natAbs_of_isUnit (Matrix.isUnit_det_of_right_inverse w.U_mul_Uinv),
    Int.natAbs_of_isUnit (Matrix.isUnit_det_of_right_inverse w.V_mul_Vinv),
    w.factor_pos, w.factor_chain, w.reduction, q_dvd_smithLastFactor P w⟩

end Sorted

/-! ## The binary simplex pivot of `thm:d3-bound` -/

section Simplex

open MainTheory.SixQubitSemanticEntrance

variable {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
  {G : RankTwoGlobal.FiniteGeneratorResolution C q}
  {T : RankTwoGlobal.TwoFiberCertificate G}

instance instNeZeroRankSimplex (P : BinarySimplexPivot G T) : NeZero P.rank :=
  ⟨by have := P.rank_pos; omega⟩

theorem nonempty_smithWitness_simplex (P : BinarySimplexPivot G T) :
    Nonempty (SmithWitness P.matrix) := by
  exact SmithExistence.exists_normalized_smith P.matrix P.nonsingular

/-- **`q | d_r(C)` for the sparse pivot**, for every Smith normal form of it. -/
theorem q_dvd_smithLastFactor_simplex (P : BinarySimplexPivot G T)
    (hprimitive : Gate.Primitive q (normalizedFiniteAngle G T))
    (w : SmithWitness P.matrix) : q ∣ w.lastFactor := by
  rw [← inverseDenominator_eq_smithLastFactor w]
  exact BinarySimplexPivot.q_dvd_inverseDenominator P hprimitive

/-- The manuscript's display for the sparse pivot. -/
theorem exists_smithNormalForm_q_dvd_last_simplex (P : BinarySimplexPivot G T)
    (hprimitive : Gate.Primitive q (normalizedFiniteAngle G T)) :
    ∃ (U V : Matrix (Fin P.rank) (Fin P.rank) ℤ) (dd : Fin P.rank → ℕ),
      U.det.natAbs = 1 ∧ V.det.natAbs = 1 ∧
      (∀ i, 0 < dd i) ∧ (∀ ⦃i j⦄, i ≤ j → dd i ∣ dd j) ∧
      U * P.matrix * V = Matrix.diagonal (fun i => (dd i : ℤ)) ∧
      q ∣ dd (lastIndex (s := Fin P.rank)) := by
  obtain ⟨w⟩ := nonempty_smithWitness_simplex P
  exact ⟨w.U, w.V, w.factor,
    Int.natAbs_of_isUnit (Matrix.isUnit_det_of_right_inverse w.U_mul_Uinv),
    Int.natAbs_of_isUnit (Matrix.isUnit_det_of_right_inverse w.V_mul_Vinv),
    w.factor_pos, w.factor_chain, w.reduction,
    q_dvd_smithLastFactor_simplex P hprimitive w⟩

end Simplex

end MainTheory.PivotSmithNormalForm
