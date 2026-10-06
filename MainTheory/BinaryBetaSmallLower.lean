import MainTheory.BinaryDetCircuit

/-!
# Explicit sharp binary denominator witnesses in sizes four and five

The universal upper bounds are kept in separate finite-certificate modules.
This file supplies only the two attainment halves.  In each size an explicit
zero--one matrix, an exact determinant computation, and one rational inverse
entry force the sharp inverse denominator to be the claimed prime.
-/

namespace MainTheory.BinaryBetaSmallLower

open MainTheory.BinaryBeta
open MainTheory.SharpClearing

/-! ## Size four -/

namespace Four

abbrev F4 := Fin 4

/-- The zero-diagonal, one-off-diagonal matrix `J - I`. -/
def attainingMatrix : Matrix F4 F4 ℤ :=
  !![0, 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 0]

theorem attainingMatrix_isZeroOne : IsZeroOne attainingMatrix := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [attainingMatrix]

theorem attainingMatrix_det : attainingMatrix.det = -3 := by
  decide

theorem attainingMatrix_det_ne_zero : attainingMatrix.det ≠ 0 := by
  rw [attainingMatrix_det]
  norm_num

def rightHandSide : F4 → ℤ := ![1, 0, 0, 0]

/-- The first column of the rational inverse. -/
def solution : F4 → ℚ := ![(-2 / 3), (1 / 3), (1 / 3), (1 / 3)]

theorem solution_valid :
    (ratMatrix attainingMatrix).mulVec solution =
      fun i ↦ (rightHandSide i : ℚ) := by
  funext i
  fin_cases i <;>
    norm_num [ratMatrix, attainingMatrix, solution, rightHandSide,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem inverse_entry_one_zero :
    (ratMatrix attainingMatrix)⁻¹ (1 : F4) (0 : F4) = (1 / 3 : ℚ) := by
  have h := congrFun
    (solution_eq_inv_mulVec attainingMatrix rightHandSide solution
      attainingMatrix_det_ne_zero solution_valid) (1 : F4)
  simpa [solution, rightHandSide, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] using h.symm

theorem three_dvd_inverseDenominator :
    3 ∣ inverseDenominator attainingMatrix := by
  have h := inverse_entry_den_dvd attainingMatrix (1 : F4) (0 : F4)
  rw [inverse_entry_one_zero] at h
  norm_num at h
  exact h

theorem inverseDenominator_dvd_three :
    inverseDenominator attainingMatrix ∣ 3 := by
  have h := inverseDenominator_dvd_detNatAbs
    attainingMatrix attainingMatrix_det_ne_zero
  rw [attainingMatrix_det] at h
  norm_num at h
  exact h

theorem inverseDenominator_eq_three :
    inverseDenominator attainingMatrix = 3 :=
  Nat.dvd_antisymm inverseDenominator_dvd_three
    three_dvd_inverseDenominator

theorem betaFourAttained : BetaAttained 4 3 := by
  refine ⟨4, by norm_num, by norm_num, attainingMatrix,
    attainingMatrix_isZeroOne, attainingMatrix_det_ne_zero, ?_⟩
  exact inverseDenominator_eq_three

end Four

/-! ## Size five -/

namespace Five

abbrev F5 := Fin 5

/-- A maximal-determinant binary matrix of order five. -/
def attainingMatrix : Matrix F5 F5 ℤ :=
  !![1, 0, 1, 0, 0;
     1, 1, 0, 1, 0;
     0, 1, 1, 0, 1;
     0, 0, 1, 1, 0;
     1, 0, 0, 1, 1]

theorem attainingMatrix_isZeroOne : IsZeroOne attainingMatrix := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [attainingMatrix]

set_option maxRecDepth 5000 in
theorem attainingMatrix_det : attainingMatrix.det = 5 := by
  decide

theorem attainingMatrix_det_ne_zero : attainingMatrix.det ≠ 0 := by
  rw [attainingMatrix_det]
  norm_num

def rightHandSide : F5 → ℤ := ![1, 0, 0, 0, 0]

/-- The first column of the rational inverse. -/
def solution : F5 → ℚ :=
  ![(3 / 5), (-1 / 5), (2 / 5), (-2 / 5), (-1 / 5)]

theorem solution_valid :
    (ratMatrix attainingMatrix).mulVec solution =
      fun i ↦ (rightHandSide i : ℚ) := by
  funext i
  fin_cases i <;>
    norm_num [ratMatrix, attainingMatrix, solution, rightHandSide,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem inverse_entry_one_zero :
    (ratMatrix attainingMatrix)⁻¹ (1 : F5) (0 : F5) = (-1 / 5 : ℚ) := by
  have h := congrFun
    (solution_eq_inv_mulVec attainingMatrix rightHandSide solution
      attainingMatrix_det_ne_zero solution_valid) (1 : F5)
  simpa [solution, rightHandSide, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] using h.symm

theorem five_dvd_inverseDenominator :
    5 ∣ inverseDenominator attainingMatrix := by
  have h := inverse_entry_den_dvd attainingMatrix (1 : F5) (0 : F5)
  rw [inverse_entry_one_zero] at h
  norm_num at h
  exact h

theorem inverseDenominator_dvd_five :
    inverseDenominator attainingMatrix ∣ 5 := by
  have h := inverseDenominator_dvd_detNatAbs
    attainingMatrix attainingMatrix_det_ne_zero
  rw [attainingMatrix_det] at h
  norm_num at h
  exact h

theorem inverseDenominator_eq_five :
    inverseDenominator attainingMatrix = 5 :=
  Nat.dvd_antisymm inverseDenominator_dvd_five
    five_dvd_inverseDenominator

theorem betaFiveAttained : BetaAttained 5 5 := by
  refine ⟨5, by norm_num, by norm_num, attainingMatrix,
    attainingMatrix_isZeroOne, attainingMatrix_det_ne_zero, ?_⟩
  exact inverseDenominator_eq_five

end Five

end MainTheory.BinaryBetaSmallLower
