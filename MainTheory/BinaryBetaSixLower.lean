import MainTheory.BinaryDetCircuit

/-!
# A kernel certificate that the six-variable binary denominator reaches nine

This file proves only the lower/attainment half of `β₆ = 9`.  The matrix is
explicit, its determinant and zero--one entries are checked in Lean, and an
explicit solution of a standard-basis system exhibits an inverse entry with
reduced denominator nine.  The opposite divisibility follows from determinant
clearing, so no Smith-factor lookup or externally asserted rank is used.

The universal upper bound `BetaBound 6 9` is deliberately not claimed here.
-/

namespace MainTheory.BinaryBetaSixLower

open MainTheory.BinaryBeta
open MainTheory.SharpClearing

abbrev F3 := Fin 3
abbrev F6 := Fin 6

/-- The top three rows of a maximal-determinant binary `6 × 6` matrix. -/
def attainingTop : Matrix F3 F6 ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 1]

/-- The bottom three rows of the same matrix. -/
def attainingBottom : Matrix F3 F6 ℤ :=
  !![1, 0, 1, 1, 1, 0;
     1, 1, 1, 1, 0, 1;
     0, 1, 1, 0, 1, 0]

/-- The explicit binary matrix attaining sharp inverse denominator nine. -/
def attainingMatrix : Matrix F6 F6 ℤ :=
  MainTheory.BinaryDetCircuit.stack3x3 attainingTop attainingBottom

theorem attainingMatrix_isZeroOne : IsZeroOne attainingMatrix := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [attainingMatrix, attainingTop, attainingBottom,
      MainTheory.BinaryDetCircuit.stack3x3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The grouped `3+3` Laplace circuit checks the determinant without expanding
one unstructured 720-term Leibniz sum. -/
theorem attainingMatrix_det : attainingMatrix.det = 9 := by
  change (MainTheory.BinaryDetCircuit.stack3x3
    attainingTop attainingBottom).det = 9
  rw [← MainTheory.BinaryDetCircuit.laplace33Grouped_eq_det]
  simp [MainTheory.BinaryDetCircuit.laplace33Grouped,
    MainTheory.BinaryDetCircuit.minor3Poly,
    MainTheory.BinaryDetCircuit.minor3, Matrix.det_fin_three,
    attainingTop, attainingBottom]

theorem attainingMatrix_det_ne_zero : attainingMatrix.det ≠ 0 := by
  rw [attainingMatrix_det]
  norm_num

/-- The fourth standard basis vector, using zero-based index `3`. -/
def rightHandSide : F6 → ℤ := ![0, 0, 0, 1, 0, 0]

/-- An exact rational solution of `attainingMatrix * x = e₃`. -/
def solution : F6 → ℚ :=
  ![(4 / 9), (-1 / 3), (2 / 9), (2 / 9), (1 / 9), (-5 / 9)]

theorem solution_valid :
    (ratMatrix attainingMatrix).mulVec solution =
      fun i => (rightHandSide i : ℚ) := by
  funext i
  fin_cases i <;>
    norm_num [ratMatrix, attainingMatrix, attainingTop, attainingBottom,
      MainTheory.BinaryDetCircuit.stack3x3, solution, rightHandSide,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The displayed solution is the inverse applied to `e₃`; its fifth
coordinate therefore identifies one actual inverse-matrix entry. -/
theorem inverse_entry_four_three :
    (ratMatrix attainingMatrix)⁻¹ (4 : F6) (3 : F6) = (1 / 9 : ℚ) := by
  have h := congrFun
    (solution_eq_inv_mulVec attainingMatrix rightHandSide solution
      attainingMatrix_det_ne_zero solution_valid) (4 : F6)
  simpa [solution, rightHandSide, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] using h.symm

/-- A genuine inverse entry of reduced denominator nine forces nine to divide
the sharp common inverse denominator. -/
theorem nine_dvd_inverseDenominator :
    9 ∣ inverseDenominator attainingMatrix := by
  have h := inverse_entry_den_dvd attainingMatrix (4 : F6) (3 : F6)
  rw [inverse_entry_four_three] at h
  norm_num at h
  exact h

/-- Determinant clearing gives the reverse divisibility. -/
theorem inverseDenominator_dvd_nine :
    inverseDenominator attainingMatrix ∣ 9 := by
  have h := inverseDenominator_dvd_detNatAbs
    attainingMatrix attainingMatrix_det_ne_zero
  rw [attainingMatrix_det] at h
  norm_num at h
  exact h

theorem inverseDenominator_eq_nine :
    inverseDenominator attainingMatrix = 9 := by
  exact Nat.dvd_antisymm inverseDenominator_dvd_nine
    nine_dvd_inverseDenominator

/-- Fully kernel-facing attainment half of `β₆ = 9`. -/
theorem betaSixAttained : BetaAttained 6 9 := by
  refine ⟨6, by norm_num, by norm_num, attainingMatrix,
    attainingMatrix_isZeroOne, attainingMatrix_det_ne_zero, ?_⟩
  exact inverseDenominator_eq_nine

end MainTheory.BinaryBetaSixLower
