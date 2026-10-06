import MainTheory.Orbit3SpinMomentInterpretation
import MainTheory.Orbit3SamplingRows
import SixQubit.Generated.Orbit3RowMetadata

/-! # The complete raw coordinate rows vanish on actual encoders

Pauli, spin and Hadamard expressions are interpreted uniformly. The spin
rows include their factor 64. Primitive finite coefficient rows are not
assumed here; their equality with these raw expressions is checked separately.
-/

namespace MainTheory.Orbit3RowCoordinateExpressions

open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3CoordinateRealization MainTheory.Orbit3PauliCubicExpansion
open MainTheory.Orbit3PauliMomentInterpretation MainTheory.Orbit3SamplingRows
open MainTheory.Orbit3CliffordAverage
open SixQubit.Generated
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

def hPauli (i : Fin 211) (k : Fin 3) : SS.PauliString 6 :=
  MainTheory.Orbit3PauliZeros.decode (Orbit3HadamardConstraints.labels i k)

theorem h_xor_zero_x : ∀ i : Fin 211, ∀ j : Fin 6,
    SS.bxor (hPauli i 0).x (hPauli i 1).x j = (hPauli i 2).x j := by decide +kernel

theorem h_xor_zero_z : ∀ i : Fin 211, ∀ j : Fin 6,
    SS.bxor (hPauli i 0).z (hPauli i 1).z j = (hPauli i 2).z j := by decide +kernel

theorem h_conjugation_even : ∀ i : Fin 211, totalY (hPauli i) % 2 = 0 := by decide +kernel

def spinIndex (i : Fin 211) : Fin 715 :=
  Orbit3CubicTriples.pairIndex (Orbit3SpinConstraints.triples i).1 (Orbit3SpinConstraints.triples i).2.1

theorem spin_physical : ∀ i : Fin 211,
    Orbit3CubicTriples.physical (spinIndex i) = Orbit3SpinConstraints.physical i := by decide +kernel

def rawRow (i : Fin 211) (y : Fin 269 → ℝ) : ℝ :=
  if Orbit3PauliConstraints.kind i = 0 then rawEvaluation (Orbit3RowMetadata.pauli i) y else
    if Orbit3PauliConstraints.kind i = 1 then MainTheory.Orbit3SpinMomentInterpretation.rawEvaluation (spinIndex i) y else
      rawEvaluation (Orbit3RowMetadata.pauli i) y -
        (Orbit3HadamardConstraints.sign i : ℝ) * rawEvaluation (hPauli i) y

def rowScale (i : Fin 211) : ℝ := if Orbit3PauliConstraints.kind i = 1 then 64 else 1

theorem pauli_coordinates (W : Encoder) (i : Fin 211) :
    rawEvaluation (Orbit3RowMetadata.pauli i) (coordinates W) = kl W i := by
  symm
  exact sampled_product_coordinates W _ (funext (Orbit3RowMetadata.xor_zero_x i))
    (funext (Orbit3RowMetadata.xor_zero_z i)) (Orbit3RowMetadata.conjugation_even i)

theorem h_coordinates (W : Encoder) (i : Fin 211) :
    rawEvaluation (hPauli i) (coordinates W) = ∑ g : Index, product (hPauli i) (wave W g) := by
  symm
  exact sampled_product_coordinates W _ (funext (h_xor_zero_x i)) (funext (h_xor_zero_z i)) (h_conjugation_even i)

theorem spin_coordinates (W : Encoder) (i : Fin 211) :
    MainTheory.Orbit3SpinMomentInterpretation.rawEvaluation (spinIndex i) (coordinates W) = 64 * spin W i := by
  rw [← MainTheory.Orbit3SpinMomentInterpretation.sampled_spin_coordinates]
  unfold MainTheory.Orbit3SpinMomentInterpretation.multiplier MainTheory.CubicTripleCanonical.monomial
  simp_rw [spin_physical]
  rfl

theorem actual_row_interpretation (W : Encoder) (i : Fin 211) :
    rawRow i (coordinates W) = rowScale i * physicalRow W i := by
  unfold rawRow rowScale physicalRow
  by_cases h0 : Orbit3PauliConstraints.kind i = 0
  · rw [if_pos h0, if_pos h0, pauli_coordinates]
    have h1 : Orbit3PauliConstraints.kind i ≠ 1 := by rw [h0]; decide
    rw [if_neg h1, one_mul]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : Orbit3PauliConstraints.kind i = 1
    · rw [if_pos h1, if_pos h1, if_pos h1, spin_coordinates]
    · rw [if_neg h1, if_neg h1, if_neg h1, one_mul, pauli_coordinates, h_coordinates]
      unfold hadamard kl
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      rfl

theorem all_raw_rows_zero (W : Encoder) (i : Fin 211) : rawRow i (coordinates W) = 0 := by
  rw [actual_row_interpretation, all_physical_rows_zero, mul_zero]

end
end MainTheory.Orbit3RowCoordinateExpressions
