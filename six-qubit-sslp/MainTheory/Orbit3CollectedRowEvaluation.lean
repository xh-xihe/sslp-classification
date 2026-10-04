import SixQubit.Generated.Orbit3CollectedRows.Data
import SixQubit.Generated.Orbit3RowMetadata
import SixQubit.Generated.Orbit3SexticIdentity
import MainTheory.Orbit3CoefficientCollection

/-! # Integer collected trees evaluate to the primitive rational rows

The only finite hypothesis is coefficient equality with the existing rational
certificate. The padding coordinates contribute zero for every input vector.
-/

namespace MainTheory.Orbit3CollectedRowEvaluation

open MainTheory.Orbit3CoefficientCollection MainTheory.DyadicCoefficientTree
open SixQubit.Generated
open scoped BigOperators

theorem tree_evaluation (i : Fin 211) (y : Fin 269 → ℝ)
    (hc : ∀ j : Fin 269, (lookup (Orbit3CollectedRows.Data.row i) j.val : ℚ) =
      (Orbit3RowMetadata.rowDivisor i : ℚ) * Orbit3SexticIdentity.rows i j) :
    evaluate (Orbit3CollectedRows.Data.row i) (padded y) =
      (Orbit3RowMetadata.rowDivisor i : ℝ) * Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) y := by
  have hr (j : Fin 269) : (lookup (Orbit3CollectedRows.Data.row i) j.val : ℝ) =
      (Orbit3RowMetadata.rowDivisor i : ℝ) * (Orbit3SexticIdentity.rows i j : ℝ) := by
    exact_mod_cast hc j
  unfold evaluate
  change (∑ j : Fin (269 + 243), (lookup (Orbit3CollectedRows.Data.row i) j.val : ℝ) * padded y j) = _
  rw [Fin.sum_univ_add]
  have hl (j : Fin 269) : padded y (Fin.castAdd 243 j) = y j := by
    simp only [padded, Fin.val_castAdd, j.isLt, ↓reduceDIte]
  have hh (j : Fin 243) : padded y (Fin.natAdd 269 j) = 0 := by
    have hn : ¬(Fin.natAdd 269 j).val < 269 := by simp only [Fin.val_natAdd]; omega
    simp only [padded, hn, ↓reduceDIte]
  simp only [hl, hh, mul_zero, Finset.sum_const_zero, add_zero, Fin.val_castAdd, hr]
  simp only [Orbit3SexticIdentity.evaluate, Finset.mul_sum, mul_assoc]

end MainTheory.Orbit3CollectedRowEvaluation
