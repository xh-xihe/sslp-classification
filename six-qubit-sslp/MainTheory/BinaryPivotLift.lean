import MainTheory.ColoredBound
import MainTheory.PivotSmithNormalForm

/-! # One binary pivot, its actual solution, and the lift's Smith divisor

The signed pivot and its binary partner select the same rows and columns.
Solving the binary system and undoing the column signs gives the very solution
used to construct the physical lift, not merely a matrix with a suitable bound.
-/

namespace MainTheory.BinaryPivotLift

open FiniteLift PhaseSectorFull SharpClearing BinaryPivot

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}
variable {s : Type*} [Fintype s] [DecidableEq s]
variable {D : SectorDecomposition n t theta} (P : PivotData D s)

def binarySolution : s → ℚ :=
  (ratMatrix (binMatrix P))⁻¹.mulVec (fun i => (P.rhs i : ℚ))

theorem binary_det_ne_zero (hdet : P.matrix.det ≠ 0) :
    (ratMatrix (binMatrix P)).det ≠ 0 := by
  rw [show (ratMatrix (binMatrix P)).det = ((binMatrix P).det : ℚ) from
    ((Int.castRingHom ℚ).map_det (binMatrix P)).symm]
  exact_mod_cast binMatrix_det_ne_zero P hdet

theorem binarySolution_solves (hdet : P.matrix.det ≠ 0) :
    (ratMatrix (binMatrix P)).mulVec (binarySolution P) = fun i => (P.rhs i : ℚ) := by
  rw [binarySolution, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (binary_det_ne_zero P hdet)),
    Matrix.one_mulVec]

theorem sign_selectedSolution_eq_binarySolution (hdet : P.matrix.det ≠ 0) :
    (fun i => (signColumn D (P.column i) : ℚ) * P.selectedSolution i) =
      binarySolution P := by
  have hsolve : (ratMatrix (binMatrix P)).mulVec
      (fun i => (signColumn D (P.column i) : ℚ) * P.selectedSolution i) =
      fun i => (P.rhs i : ℚ) := by
    rw [← P.selectedSolution_solves hdet]
    funext i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have hij := congrFun (congrFun (matrix_eq P) i) j
    simp only [Matrix.mul_diagonal] at hij
    change (binMatrix P i j : ℚ) * ((signColumn D (P.column j) : ℚ) * P.selectedSolution j) =
      (P.matrix i j : ℚ) * P.selectedSolution j
    rw [hij, Int.cast_mul]
    ring
  have h := congrArg ((ratMatrix (binMatrix P))⁻¹.mulVec) hsolve
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (binary_det_ne_zero P hdet)),
    Matrix.one_mulVec] at h
  exact h

theorem selectedSolution_eq_sign_binarySolution (hdet : P.matrix.det ≠ 0) :
    P.selectedSolution = fun i => (signColumn D (P.column i) : ℚ) * binarySolution P i := by
  funext i
  have hi := congrFun (sign_selectedSolution_eq_binarySolution P hdet) i
  have hh := congrArg (fun x : ℚ => (signColumn D (P.column i) : ℚ) * x) hi
  rcases isSign_signColumn D (P.column i) with h | h <;> simpa [h] using hh

/-- The augmented lift is obtained by solving this binary matrix, undoing the
column signs, and inserting zero at every nonselected coordinate. -/
theorem rationalLift_augmented_eq_binarySolution (hdet : P.matrix.det ≠ 0)
    (hZ : ZDetects D) :
    (P.rationalLift hdet hZ).augmented = extendByZero P.column
      (fun i => (signColumn D (P.column i) : ℚ) * binarySolution P i) := by
  change extendByZero P.column P.selectedSolution = _
  rw [selectedSolution_eq_sign_binarySolution P hdet]

variable [LinearOrder s] [Nonempty s]

/-- Every actual Smith reduction of the same binary matrix gives the claimed
divisor for the same physical lift. -/
theorem rationalLift_order_dvd_smithLastFactor (hdet : P.matrix.det ≠ 0)
    (hZ : ZDetects D) (W : SmithWitness (binMatrix P)) :
    (P.rationalLift hdet hZ).order ∣ W.lastFactor := by
  rw [← inverseDenominator_eq_smithLastFactor W, ← inverseDenominator_eq P]
  exact sharp_pivot_divisibility P hdet hZ

end

end MainTheory.BinaryPivotLift
