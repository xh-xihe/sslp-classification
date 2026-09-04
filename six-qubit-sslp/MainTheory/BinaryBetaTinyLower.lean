import MainTheory.BinaryDetCircuit
import MainTheory.ThresholdBoundsSmall

/-!
# Attainment in sizes one, two and three

`ThresholdBoundsSmall` proves the three small upper bounds `BetaBound 1 1`,
`BetaBound 2 1` and `BetaBound 3 2`, which is all the coarse filter consumes.
The paper asserts more: `six:eq:betasix` is a chain of *equalities*
`(beta_1, ..., beta_6) = (1, 1, 2, 3, 5, 9)`, and the sizes four, five and six
already have their attaining matrices (`BinaryBetaSmallLower`,
`BinaryBetaSixLower`).  The three small sizes had none, so those three entries
were bounds wearing an equality's clothes.

This file supplies them, in the same shape as the larger sizes: an explicit
zero--one matrix, an exact determinant, and one rational inverse entry forcing
the sharp inverse denominator from below.

The consequence is not cosmetic.  The paper defines
`r_min(q) = min {r : beta_r >= q}`, so justifying the entry `r_min(2) = 3` of
`six:eq:rmin` needs `beta_3 >= 2` -- that is, exactly the attainment below.
Without it the `r_min` table is asserted rather than derived.
-/

namespace MainTheory.BinaryBetaTinyLower

open MainTheory.BinaryBeta
open MainTheory.SharpClearing

/-! ## Size one -/

namespace One

abbrev F1 := Fin 1

/-- The one-by-one identity. -/
def attainingMatrix : Matrix F1 F1 ℤ := !![1]

theorem attainingMatrix_isZeroOne : IsZeroOne attainingMatrix := by
  intro i j
  fin_cases i
  fin_cases j
  simp [attainingMatrix]

theorem attainingMatrix_det : attainingMatrix.det = 1 := by
  decide

theorem attainingMatrix_det_ne_zero : attainingMatrix.det ≠ 0 := by
  rw [attainingMatrix_det]
  norm_num

/-- The inverse is integral, so the sharp denominator divides one. -/
theorem inverseDenominator_eq_one :
    inverseDenominator attainingMatrix = 1 := by
  have h := inverseDenominator_dvd_detNatAbs
    attainingMatrix attainingMatrix_det_ne_zero
  rw [attainingMatrix_det] at h
  norm_num at h
  exact h

theorem betaOneAttained : BetaAttained 1 1 :=
  ⟨1, by norm_num, by norm_num, attainingMatrix,
    attainingMatrix_isZeroOne, attainingMatrix_det_ne_zero,
    inverseDenominator_eq_one⟩

/-- Size two is attained by the same one-by-one witness: `BetaAttained` asks
only for a size at most `N`. -/
theorem betaTwoAttained : BetaAttained 2 1 :=
  ⟨1, by norm_num, by norm_num, attainingMatrix,
    attainingMatrix_isZeroOne, attainingMatrix_det_ne_zero,
    inverseDenominator_eq_one⟩

end One

/-! ## Size three -/

namespace Three

abbrev F3 := Fin 3

/-- `J - I` in size three: determinant two, and a half in every inverse
entry. -/
def attainingMatrix : Matrix F3 F3 ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 1, 0]

theorem attainingMatrix_isZeroOne : IsZeroOne attainingMatrix := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [attainingMatrix]

theorem attainingMatrix_det : attainingMatrix.det = 2 := by
  decide

theorem attainingMatrix_det_ne_zero : attainingMatrix.det ≠ 0 := by
  rw [attainingMatrix_det]
  norm_num

def rightHandSide : F3 → ℤ := ![1, 0, 0]

/-- The first column of the rational inverse. -/
def solution : F3 → ℚ := ![(-1 / 2), (1 / 2), (1 / 2)]

theorem solution_valid :
    (ratMatrix attainingMatrix).mulVec solution =
      fun i ↦ (rightHandSide i : ℚ) := by
  funext i
  fin_cases i <;>
    norm_num [ratMatrix, attainingMatrix, solution, rightHandSide,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem inverse_entry_zero_zero :
    (ratMatrix attainingMatrix)⁻¹ (0 : F3) (0 : F3) = (-1 / 2 : ℚ) := by
  have h := congrFun
    (solution_eq_inv_mulVec attainingMatrix rightHandSide solution
      attainingMatrix_det_ne_zero solution_valid) (0 : F3)
  simpa [solution, rightHandSide, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] using h.symm

theorem two_dvd_inverseDenominator :
    2 ∣ inverseDenominator attainingMatrix := by
  have h := inverse_entry_den_dvd attainingMatrix (0 : F3) (0 : F3)
  rw [inverse_entry_zero_zero] at h
  norm_num at h
  exact h

theorem inverseDenominator_dvd_two :
    inverseDenominator attainingMatrix ∣ 2 := by
  have h := inverseDenominator_dvd_detNatAbs
    attainingMatrix attainingMatrix_det_ne_zero
  rw [attainingMatrix_det] at h
  norm_num at h
  exact h

theorem inverseDenominator_eq_two :
    inverseDenominator attainingMatrix = 2 :=
  Nat.dvd_antisymm inverseDenominator_dvd_two two_dvd_inverseDenominator

theorem betaThreeAttained : BetaAttained 3 2 :=
  ⟨3, by norm_num, by norm_num, attainingMatrix,
    attainingMatrix_isZeroOne, attainingMatrix_det_ne_zero,
    inverseDenominator_eq_two⟩

end Three

/-! ## The three exact values -/

/-- `beta_1 = 1`, both halves. -/
theorem betaExact_one : BetaExact 1 1 where
  upper := MainTheory.ThresholdBoundsSmall.betaBound_one
  attained := One.betaOneAttained

/-- `beta_2 = 1`, both halves. -/
theorem betaExact_two : BetaExact 2 1 where
  upper := MainTheory.ThresholdBoundsSmall.betaBound_two
  attained := One.betaTwoAttained

/-- `beta_3 = 2`, both halves. -/
theorem betaExact_three : BetaExact 3 2 where
  upper := MainTheory.ThresholdBoundsSmall.betaBound_three
  attained := Three.betaThreeAttained

/-! ## The entry of `six:eq:rmin` these attainments justify -/

/-- **`r_min(2) = 3`.**

The paper's `r_min(q) := min {r : beta_r >= q}`.  For `q = 2` the value is
three, and both halves are now theorems: no zero--one system in one or two
variables can force a denominator as large as two, and an explicit
three-variable one does.

`CoarseFilter.rMin` hard-codes this table and its only lemma uses the upper
bounds alone, so before the attainment below the entry was an assertion. -/
theorem rMin_two_eq_three :
    (∀ s : ℕ, 1 ≤ s → s ≤ 2 → ∀ C : Matrix (Fin s) (Fin s) ℤ,
        IsZeroOne C → C.det ≠ 0 → inverseDenominator C < 2) ∧
      ∃ C : Matrix (Fin 3) (Fin 3) ℤ,
        IsZeroOne C ∧ C.det ≠ 0 ∧ 2 ≤ inverseDenominator C := by
  constructor
  · intro s hs1 hs2 C hzo hdet
    have := MainTheory.ThresholdBoundsSmall.betaBound_two s hs1 hs2 C hzo hdet
    omega
  · exact ⟨Three.attainingMatrix, Three.attainingMatrix_isZeroOne,
      Three.attainingMatrix_det_ne_zero,
      le_of_eq Three.inverseDenominator_eq_two.symm⟩

end MainTheory.BinaryBetaTinyLower
