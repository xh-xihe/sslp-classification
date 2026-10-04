import MainTheory.KernelAxiomAudit
import MainTheory.Orbit3FirstCollectedRow

/-! Trusted declarations for the actual polynomial-to-coefficient bridge. -/

#certification_axioms [
  MainTheory.DyadicCoefficientTree.lookup_addAt,
  MainTheory.DyadicCoefficientTree.evaluate_accumulate,
  MainTheory.Orbit3PauliCubicExpansion.complex_expansion,
  MainTheory.Orbit3PauliCubicExpansion.product_expansion,
  MainTheory.Orbit3PauliTranslationReduction.triple_sum_reduction,
  MainTheory.Orbit3PauliMomentInterpretation.sampled_product_coordinates,
  MainTheory.Orbit3CoefficientCollection.coefficients_evaluation,
  MainTheory.Orbit3SpinMomentInterpretation.multiplier_expansion,
  MainTheory.Orbit3SpinMomentInterpretation.sampled_spin_coordinates,
  MainTheory.Orbit3SpinMomentInterpretation.coefficients_evaluation,
  MainTheory.Orbit3RowCoordinateExpressions.actual_row_interpretation,
  MainTheory.Orbit3RowCoordinateExpressions.all_raw_rows_zero,
  MainTheory.Orbit3CoefficientTrace.trace_evaluation,
  MainTheory.Orbit3CoefficientTrace.pauli_trace_evaluation,
  MainTheory.Orbit3CollectedRowEvaluation.tree_evaluation,
  SixQubit.Generated.Orbit3CollectedRows.Trace000.Checks.steps,
  SixQubit.Generated.Orbit3CollectedRows.Trace000.Checks.final,
  MainTheory.Orbit3FirstCollectedRow.primitive_coefficients,
  MainTheory.Orbit3FirstCollectedRow.primitive_row_zero
]
