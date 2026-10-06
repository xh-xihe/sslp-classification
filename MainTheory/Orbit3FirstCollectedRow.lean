import SixQubit.Generated.Orbit3CollectedRows.Trace000Checks
import MainTheory.Orbit3CollectedRowEvaluation
import MainTheory.Orbit3RowCoordinateExpressions

/-! # A complete primitive certificate row vanishes on actual orbit-3 encoders

All 4096 ordered bit pairs are covered by 64 kernel-checked transitions.
The integer result is checked against the primitive rational row, and the
physical Pauli zero is derived from the actual encoder conditions.
-/

namespace MainTheory.Orbit3FirstCollectedRow

open MainTheory.DyadicCoefficientTree MainTheory.Orbit3CoefficientCollection
open MainTheory.Orbit3CoefficientTrace MainTheory.Orbit3CollectedRowEvaluation
open MainTheory.Orbit3RowCoordinateExpressions MainTheory.Orbit3CoordinateRealization
open MainTheory.Orbit3PauliMomentInterpretation MainTheory.Orbit3SamplingRows
open MainTheory.Orbit3ScalarCategoryRealization
open SixQubit.Generated

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

theorem primitive_coefficients : ∀ j : Fin 269,
    (lookup Orbit3CollectedRows.Data.row000 j.val : ℚ) =
      (Orbit3RowMetadata.rowDivisor 0 : ℚ) * Orbit3SexticIdentity.rows 0 j := by
  decide +kernel

theorem primitive_row_zero (W : Encoder) :
    Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows 0) (coordinates W) = 0 := by
  have ht := pauli_trace_evaluation (Orbit3RowMetadata.pauli 0)
    Orbit3CollectedRows.Trace000.states Orbit3CollectedRows.Trace000.Checks.initial
      Orbit3CollectedRows.Trace000.Checks.steps (coordinates W)
  rw [Orbit3CollectedRows.Trace000.Checks.final] at ht
  have he := tree_evaluation 0 (coordinates W) primitive_coefficients
  have hd : Orbit3RowMetadata.rowDivisor 0 = 1 := by decide +kernel
  rw [hd, Int.cast_one, one_mul] at he
  calc
    _ = evaluate Orbit3CollectedRows.Data.row000 (padded (coordinates W)) := he.symm
    _ = rawEvaluation (Orbit3RowMetadata.pauli 0) (coordinates W) := ht
    _ = kl W 0 := pauli_coordinates W 0
    _ = 0 := kl_zero W 0 (by decide +kernel)

end MainTheory.Orbit3FirstCollectedRow
