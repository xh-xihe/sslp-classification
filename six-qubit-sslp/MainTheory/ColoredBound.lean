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
  obtain ⟨P, hratdet, _, hrankle⟩ := PivotSize.exists_pivot_card_eq_rank_le D
  have hdet : P.matrix.det ≠ 0 := det_ne_zero_of_ratPivot P hratdet
  set L := P.rationalLift hdet hZ with hL
  have h2 : 2 ≤ L.order := L.two_le_order ht
  have hrank : 1 ≤ (coloredMatrix D).rank := by
    rcases Nat.eq_zero_or_pos (coloredMatrix D).rank with h0 | hpos
    · exfalso
      have hempty : IsEmpty (Fin (coloredMatrix D).rank) := by
        rw [h0]; exact Fin.isEmpty'
      have hone : inverseDenominator P.matrix = 1 :=
        @inverseDenominator_of_isEmpty _ _ _ hempty P.matrix
      have hdvd := sharp_pivot_divisibility P hdet hZ
      rw [hone, ← hL] at hdvd
      have : L.order = 1 := Nat.dvd_one.mp hdvd
      omega
    · exact hpos
  exact ⟨L, h2, L.same_projective_sector_action, L.numerator_spec,
    L.primitive, L.relative_phase_cleared,
    pivot_order_le beta hZ P hdet hrank hrankle⟩

end MainTheory.ColoredBound
