import MainTheory.Orbit3SamplingHadamard
import SixQubit.Generated.Orbit3SpinConstraints

/-! # All 211 physical certificate row expressions vanish on actual samples

This uses the actual encoder-preserving sampler, not supplied row equations.
The remaining obligation is equality of these expressions with evaluation
of the reduced rational coefficient rows on the 269 moment coordinates.
-/

namespace MainTheory.Orbit3SamplingRows

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3ActualSampling
open MainTheory.Orbit3CliffordAverage MainTheory.Orbit3HadamardBridge
open MainTheory.Orbit3SamplingHadamard MainTheory.Orbit3PauliZeros
open SixQubit.Generated SixQubit.ParityLogicalState
open scoped BigOperators

noncomputable section

def kl (W : Encoder) (i : Fin 211) : ℝ :=
  ∑ g : Index, product (fun k => decode (Orbit3PauliConstraints.labels i k)) (wave W g)

def spin (W : Encoder) (i : Fin 211) : ℝ :=
  ∑ g : Index, (star (wave W g (Orbit3SpinConstraints.physical i).1 *
    wave W g (Orbit3SpinConstraints.physical i).2.1 *
    wave W g (Orbit3SpinConstraints.physical i).2.2) *
      MainTheory.Orbit3SpinForm.spin (wave W g) * wave W g (SixQubit.Realize.nbit 63)).re

def hadamard (W : Encoder) (i : Fin 211) : ℝ :=
  ∑ g : Index, (product (fun k => decode (Orbit3PauliConstraints.labels i k)) (wave W g) -
    (Orbit3HadamardConstraints.sign i : ℝ) *
      product (fun k => decode (Orbit3HadamardConstraints.labels i k)) (wave W g))

theorem kl_zero (W : Encoder) (i : Fin 211) (hi : Orbit3PauliConstraints.kind i = 0) :
    kl W i = 0 := kl_product_sum_zero W i hi

theorem spin_zero (W : Encoder) (i : Fin 211) : spin W i = 0 :=
  spin_multiplier_sum_zero W (Orbit3SpinConstraints.physical i) (SixQubit.Realize.nbit 63)

theorem hadamard_zero (W : Encoder) (i : Fin 211) (hi : Orbit3PauliConstraints.kind i = 2) :
    hadamard W i = 0 := by
  have h := sampling_H_Ward (fun k => decode (Orbit3PauliConstraints.labels i k)) W
  simp_rw [Orbit3HadamardConstraints.transformed_paulis i hi,
    Orbit3HadamardConstraints.product_sign i hi] at h
  exact h

def physicalRow (W : Encoder) (i : Fin 211) : ℝ :=
  if Orbit3PauliConstraints.kind i = 0 then kl W i else
    if Orbit3PauliConstraints.kind i = 1 then spin W i else hadamard W i

theorem all_physical_rows_zero (W : Encoder) (i : Fin 211) : physicalRow W i = 0 := by
  unfold physicalRow
  by_cases h0 : Orbit3PauliConstraints.kind i = 0
  · rw [if_pos h0]
    exact kl_zero W i h0
  · rw [if_neg h0]
    by_cases h1 : Orbit3PauliConstraints.kind i = 1
    · rw [if_pos h1]
      exact spin_zero W i
    · rw [if_neg h1]
      have h2 : Orbit3PauliConstraints.kind i = 2 := by
        have hi := (Orbit3PauliConstraints.kind i).isLt
        apply Fin.ext
        have hn0 : (Orbit3PauliConstraints.kind i).val ≠ 0 := fun h => h0 (Fin.ext h)
        have hn1 : (Orbit3PauliConstraints.kind i).val ≠ 1 := fun h => h1 (Fin.ext h)
        omega
      exact hadamard_zero W i h2

end
end MainTheory.Orbit3SamplingRows
