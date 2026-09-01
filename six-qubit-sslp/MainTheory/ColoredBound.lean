import MainTheory.BinaryPivot

/-!
# `thm:colored-finite-lift`: the quantitative bound

`MainTheory.FiniteLift` already proves every clause of `thm:colored-finite-lift`
for a *supplied* pivot, and `MainTheory.PivotSize` produces a pivot for every
sector decomposition, with `s = rank R <= n + t - 1` (`eq:qualitative-pivot-size`).
What was missing was the last step: turning the pivot's inverse denominator
into the constant `beta_{n+t-1}`.

Two things stood in the way, and neither was the one the documentation named.

* The pivot chain was stated against a `SharpClearing.SmithWitness`, which
  Mathlib cannot produce.  It never needed one: the witness was used only for
  nonsingularity, and `BinaryBeta.BetaBound` is stated with
  `inverseDenominator`, not with a Smith factor.  That chain now asks only for
  `det <> 0`, which `PivotSize` supplies.
* The coloured pivot has entries in `{-1, 0, 1}` while `beta_N` is a maximum
  over `{0,1}` matrices.  `MainTheory.BinaryPivot` removes the discrepancy: the
  signed pivot is its zero--one partner times a `+-1` diagonal, which changes
  no denominator.  That is the paper's local-`X` normalization, done on the
  matrix.

The degenerate `rank = 0` case is not excluded by hand: a pivot of size zero
has inverse denominator one, so the lift order would divide one, contradicting
`2 <= order`.
-/

namespace MainTheory.ColoredBound

open MainTheory.FiniteLift
open MainTheory.PhaseSectorFull
open MainTheory.SharpClearing
open MainTheory.BinaryPivot

variable {n t : ℕ} {theta : Fin n → ℝ}

/-- The rational pivot of `PivotSize` is the rational cast of the integer
pivot, so their nonsingularity statements agree. -/
theorem ratPivot_eq {s : Type*} [Fintype s] [DecidableEq s]
    {D : SectorDecomposition n t theta} (P : PivotData D s) :
    PivotSize.ratPivot P = ratMatrix P.matrix := by
  ext i j
  rw [P.matrix_cast]
  rfl

theorem det_ne_zero_of_ratPivot {s : Type*} [Fintype s] [DecidableEq s]
    {D : SectorDecomposition n t theta} (P : PivotData D s)
    (h : (PivotSize.ratPivot P).det ≠ 0) : P.matrix.det ≠ 0 := by
  intro h0
  apply h
  rw [ratPivot_eq P]
  have hm : (ratMatrix P.matrix).det = (P.matrix.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det P.matrix).symm
  rw [hm, h0]
  norm_num

/-- A pivot of size zero clears everything: its inverse denominator is one. -/
theorem inverseDenominator_of_isEmpty {s : Type*} [Fintype s] [DecidableEq s]
    [IsEmpty s] (A : Matrix s s ℤ) : inverseDenominator A = 1 := by
  unfold inverseDenominator Denominator.lcmDen
  rw [show (Finset.univ : Finset (s × s)) = ∅ from
    Finset.univ_eq_empty]
  simp

/-- **The pivot bound.**  A nonsingular pivot of size between one and
`n + t - 1` bounds the lift order by `beta_{n+t-1}`. -/
theorem pivot_order_le {B m : ℕ}
    (beta : BinaryBeta.BetaBound (n + t - 1) B)
    {D : SectorDecomposition n t theta} (hZ : ZDetects D)
    (P : PivotData D (Fin m)) (hdet : P.matrix.det ≠ 0)
    (hm : 1 ≤ m) (hmle : m ≤ n + t - 1) :
    (P.rationalLift hdet hZ).order ≤ B := by
  have hbin : inverseDenominator (binMatrix P) ≤ B :=
    beta m hm hmle (binMatrix P) (binMatrix_isZeroOne P)
      (binMatrix_det_ne_zero P hdet)
  have heq : inverseDenominator P.matrix = inverseDenominator (binMatrix P) :=
    inverseDenominator_eq P
  have hdvd := sharp_pivot_divisibility P hdet hZ
  refine le_trans (Nat.le_of_dvd ?_ hdvd) ?_
  · exact inverseDenominator_pos P.matrix
  · rw [heq]; exact hbin

/-! ## The canonical pivot lift -/

/-- The pivot supplied by `PivotSize`, named once so that the lift built from
it can be referred to by later modules. -/
noncomputable def canonicalPivot (D : SectorDecomposition n t theta) :
    PivotData D (Fin (coloredMatrix D).rank) :=
  Classical.choose (PivotSize.exists_pivotData D)

theorem canonicalPivot_det (D : SectorDecomposition n t theta) :
    (canonicalPivot D).matrix.det ≠ 0 :=
  det_ne_zero_of_ratPivot _ (Classical.choose_spec (PivotSize.exists_pivotData D))

/-- **The pivot lift.**  Any rational coloured lift proves the qualitative
statements; this one also carries the `beta` bound, because it is built by
solving the pivot system rather than chosen arbitrarily. -/
noncomputable def pivotLift (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) : RationalColoredLift D :=
  (canonicalPivot D).rationalLift (canonicalPivot_det D) hZ

/-- The rank of the coloured matrix is positive once there are two sectors: a
pivot of size zero would force the lift order to divide one. -/
theorem rank_pos (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (ht : 2 ≤ t) : 1 ≤ (coloredMatrix D).rank := by
  rcases Nat.eq_zero_or_pos (coloredMatrix D).rank with h0 | hpos
  · exfalso
    have hempty : IsEmpty (Fin (coloredMatrix D).rank) := by
      rw [h0]; exact Fin.isEmpty'
    have hone : inverseDenominator (canonicalPivot D).matrix = 1 :=
      @inverseDenominator_of_isEmpty _ _ _ hempty _
    have hdvd := sharp_pivot_divisibility (canonicalPivot D)
      (canonicalPivot_det D) hZ
    rw [hone] at hdvd
    have h1 : (pivotLift D hZ).order = 1 := Nat.dvd_one.mp hdvd
    have h2 : 2 ≤ (pivotLift D hZ).order := (pivotLift D hZ).two_le_order ht
    omega
  · exact hpos

/-- **The pivot lift obeys the `beta` bound.** -/
theorem pivotLift_order_le {B : ℕ}
    (beta : BinaryBeta.BetaBound (n + t - 1) B)
    (D : SectorDecomposition n t theta) (hZ : ZDetects D) (ht : 2 ≤ t) :
    (pivotLift D hZ).order ≤ B := by
  obtain ⟨P, hratdet, _, hrankle⟩ := PivotSize.exists_pivot_card_eq_rank_le D
  exact pivot_order_le beta hZ (canonicalPivot D) (canonicalPivot_det D)
    (rank_pos D hZ ht) hrankle

/-- **`thm:colored-finite-lift`.**

Every projectively nontrivial sector decomposition of an exact code detecting
all `Z_j` has a primitive rational lift inducing the same projective action,
with modulus at most `beta_{n+t-1}`. -/
theorem quantitative_colored_finite_lift {B : ℕ}
    (beta : BinaryBeta.BetaBound (n + t - 1) B)
    (D : SectorDecomposition n t theta) (hZ : ZDetects D) (ht : 2 ≤ t) :
    ∃ L : RationalColoredLift D,
      2 ≤ L.order ∧
      SameProjectiveSectorAction D (fun j => (L.physical j : ℝ)) ∧
      (∀ j, (L.order : ℚ) * L.physical j = (L.numerator j : ℚ)) ∧
      (∀ e : ℕ, e ∣ L.order → (∀ j, (e : ℤ) ∣ L.numerator j) → e = 1) ∧
      (∀ alpha, ∃ b : ℤ,
        (L.order : ℝ) * (D.phase alpha - D.phase (baseSector D)) = (b : ℝ)) ∧
      L.order ≤ B := by
  refine ⟨pivotLift D hZ, (pivotLift D hZ).two_le_order ht,
    (pivotLift D hZ).same_projective_sector_action,
    (pivotLift D hZ).numerator_spec, (pivotLift D hZ).primitive,
    (pivotLift D hZ).relative_phase_cleared,
    pivotLift_order_le beta D hZ ht⟩

end MainTheory.ColoredBound
