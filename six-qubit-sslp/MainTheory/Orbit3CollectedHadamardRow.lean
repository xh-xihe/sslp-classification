import MainTheory.Orbit3CollectedRowEvaluation
import MainTheory.Orbit3CoefficientTrace
import MainTheory.Orbit3RowCoordinateExpressions

/-! Checked integer accumulation binds the Hadamard difference to an actual
primitive row. The physical identity is the proved sampler Ward identity. -/
namespace MainTheory.Orbit3CollectedHadamardRow

open MainTheory.DyadicCoefficientTree MainTheory.Orbit3CoefficientCollection
open MainTheory.Orbit3CoefficientTrace MainTheory.Orbit3CollectedRowEvaluation
open MainTheory.Orbit3RowCoordinateExpressions MainTheory.Orbit3CoordinateRealization
open MainTheory.Orbit3PauliMomentInterpretation MainTheory.Orbit3SamplingRows
open MainTheory.Orbit3ScalarCategoryRealization SixQubit.Generated
open scoped BigOperators

def scaleTerms (k : ℤ) (terms : List (Fin (2 ^ 9) × ℤ)) : List (Fin (2 ^ 9) × ℤ) :=
  terms.map fun e => (e.1, k * e.2)

theorem scaleTerms_evaluation (k : ℤ) (terms : List (Fin (2 ^ 9) × ℤ))
    (y : Fin (2 ^ 9) → ℝ) :
    ((scaleTerms k terms).map fun e => (e.2 : ℝ) * y e.1).sum =
      (k : ℝ) * (terms.map fun e => (e.2 : ℝ) * y e.1).sum := by
  induction terms with
  | nil => simp [scaleTerms]
  | cons e terms ih =>
    simp only [scaleTerms, List.map_cons, List.sum_cons, Int.cast_mul] at *
    rw [ih]
    ring

def hRowTerms (i : Fin 211) (a : Fin 64) : List (Fin (2 ^ 9) × ℤ) :=
  rowTerms (Orbit3RowMetadata.pauli i) a ++
    scaleTerms (-Orbit3HadamardConstraints.sign i) (rowTerms (hPauli i) a)

theorem h_trace_evaluation (i : Fin 211) (states : ℕ → Tree 9)
    (initial : states 0 = zero 9)
    (steps : ∀ a : Fin 64, accumulate (states a.val) (hRowTerms i a) = states (a.val + 1))
    (y : Fin 269 → ℝ) : evaluate (states 64) (padded y) =
      rawEvaluation (Orbit3RowMetadata.pauli i) y -
        (Orbit3HadamardConstraints.sign i : ℝ) * rawEvaluation (hPauli i) y := by
  rw [trace_evaluation states (hRowTerms i) steps, initial, evaluate_zero, zero_add]
  simp only [hRowTerms, List.map_append, List.sum_append, scaleTerms_evaluation,
    rowTerms_evaluation, Int.cast_neg, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold rawEvaluation
  ring

theorem primitive_row_zero (W : Encoder) (i : Fin 211)
    (hi : Orbit3PauliConstraints.kind i = 2) (states : ℕ → Tree 9)
    (initial : states 0 = zero 9)
    (steps : ∀ a : Fin 64, accumulate (states a.val) (hRowTerms i a) = states (a.val + 1))
    (final : states 64 = Orbit3CollectedRows.Data.row i)
    (hc : ∀ j : Fin 269, (lookup (Orbit3CollectedRows.Data.row i) j.val : ℚ) =
      (Orbit3RowMetadata.rowDivisor i : ℚ) * Orbit3SexticIdentity.rows i j) :
    Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) (coordinates W) = 0 := by
  have ht := h_trace_evaluation i states initial steps (coordinates W)
  rw [final] at ht
  have he := tree_evaluation i (coordinates W) hc
  have hz : rawEvaluation (Orbit3RowMetadata.pauli i) (coordinates W) -
      (Orbit3HadamardConstraints.sign i : ℝ) * rawEvaluation (hPauli i) (coordinates W) = 0 := by
    rw [pauli_coordinates, h_coordinates]
    have hp := hadamard_zero W i hi
    simpa only [hadamard, kl, Finset.sum_sub_distrib, Finset.mul_sum] using hp
  have hd : (Orbit3RowMetadata.rowDivisor i : ℝ) ≠ 0 := by
    exact_mod_cast Orbit3RowMetadata.divisor_nonzero i
  have hm : (Orbit3RowMetadata.rowDivisor i : ℝ) *
      Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) (coordinates W) = 0 :=
    he.symm.trans (ht.trans hz)
  exact (mul_eq_zero.mp hm).resolve_left hd

end MainTheory.Orbit3CollectedHadamardRow
