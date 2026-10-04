import MainTheory.Orbit3CollectedRowEvaluation
import MainTheory.Orbit3CoefficientTrace
import MainTheory.Orbit3RowCoordinateExpressions

/-! # Checked Pauli coefficient traces imply actual primitive KL row zeros

All supplied hypotheses are finite equalities of explicit integer data. The
physical zero follows from the encoder's proved KL constraints.
-/

namespace MainTheory.Orbit3CollectedPauliRow

open MainTheory.DyadicCoefficientTree MainTheory.Orbit3CoefficientCollection
open MainTheory.Orbit3CoefficientTrace MainTheory.Orbit3CollectedRowEvaluation
open MainTheory.Orbit3RowCoordinateExpressions MainTheory.Orbit3CoordinateRealization
open MainTheory.Orbit3PauliMomentInterpretation MainTheory.Orbit3SamplingRows
open MainTheory.Orbit3ScalarCategoryRealization
open SixQubit.Generated

theorem primitive_row_zero (W : Encoder) (i : Fin 211) (hi : Orbit3PauliConstraints.kind i = 0)
    (states : ℕ → Tree 9) (initial : states 0 = zero 9)
    (steps : ∀ a : Fin 64, accumulate (states a.val)
      (rowTerms (Orbit3RowMetadata.pauli i) a) = states (a.val + 1))
    (final : states 64 = Orbit3CollectedRows.Data.row i)
    (hc : ∀ j : Fin 269, (lookup (Orbit3CollectedRows.Data.row i) j.val : ℚ) =
      (Orbit3RowMetadata.rowDivisor i : ℚ) * Orbit3SexticIdentity.rows i j) :
    Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) (coordinates W) = 0 := by
  have ht := pauli_trace_evaluation (Orbit3RowMetadata.pauli i) states initial steps (coordinates W)
  rw [final] at ht
  have he := tree_evaluation i (coordinates W) hc
  have hz : rawEvaluation (Orbit3RowMetadata.pauli i) (coordinates W) = 0 := by
    rw [pauli_coordinates]
    exact kl_zero W i hi
  have hd : (Orbit3RowMetadata.rowDivisor i : ℝ) ≠ 0 := by
    exact_mod_cast Orbit3RowMetadata.divisor_nonzero i
  have hm : (Orbit3RowMetadata.rowDivisor i : ℝ) *
      Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) (coordinates W) = 0 :=
    he.symm.trans (ht.trans hz)
  exact (mul_eq_zero.mp hm).resolve_left hd

end MainTheory.Orbit3CollectedPauliRow
