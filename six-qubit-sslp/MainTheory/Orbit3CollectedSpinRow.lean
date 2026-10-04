import MainTheory.Orbit3CollectedRowEvaluation
import MainTheory.Orbit3RowCoordinateExpressions

/-! Checked collection of the 64 spin terms binds a primitive certificate row
to the actual encoder, including its factor 64. -/
namespace MainTheory.Orbit3CollectedSpinRow

open MainTheory.DyadicCoefficientTree MainTheory.Orbit3CoefficientCollection
open MainTheory.Orbit3CollectedRowEvaluation MainTheory.Orbit3RowCoordinateExpressions
open MainTheory.Orbit3CoordinateRealization MainTheory.Orbit3SamplingRows
open MainTheory.Orbit3ScalarCategoryRealization SixQubit.Generated

theorem primitive_row_zero (W : Encoder) (i : Fin 211)
    (collected : MainTheory.Orbit3SpinMomentInterpretation.coefficients (spinIndex i) =
      Orbit3CollectedRows.Data.row i)
    (hc : ∀ j : Fin 269, (lookup (Orbit3CollectedRows.Data.row i) j.val : ℚ) =
      (Orbit3RowMetadata.rowDivisor i : ℚ) * Orbit3SexticIdentity.rows i j) :
    Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) (coordinates W) = 0 := by
  have ht := MainTheory.Orbit3SpinMomentInterpretation.coefficients_evaluation
    (spinIndex i) (coordinates W)
  rw [collected] at ht
  have he := tree_evaluation i (coordinates W) hc
  have hz : MainTheory.Orbit3SpinMomentInterpretation.rawEvaluation (spinIndex i)
      (coordinates W) = 0 := by
    rw [spin_coordinates, spin_zero, mul_zero]
  have hd : (Orbit3RowMetadata.rowDivisor i : ℝ) ≠ 0 := by
    exact_mod_cast Orbit3RowMetadata.divisor_nonzero i
  have hm : (Orbit3RowMetadata.rowDivisor i : ℝ) *
      Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) (coordinates W) = 0 :=
    he.symm.trans (ht.trans hz)
  exact (mul_eq_zero.mp hm).resolve_left hd

end MainTheory.Orbit3CollectedSpinRow
