import Mathlib

namespace MainTheory.FirstMomentSpanCounterexample

open scoped BigOperators

noncomputable section

def diagonalPoints : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![1, 1]]
def antiDiagonalPoints : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

theorem common_probability_mean :
    (∑ i : Fin 2, (1 / 2 : ℝ) • diagonalPoints i) = ![1 / 2, 1 / 2] ∧
    (∑ i : Fin 2, (1 / 2 : ℝ) • antiDiagonalPoints i) = ![1 / 2, 1 / 2] ∧
    (∑ _ : Fin 2, (1 / 2 : ℝ)) = 1 ∧ (0 : ℝ) < 1 / 2 := by
  refine ⟨?_, ?_, by norm_num [Fin.sum_univ_two], by norm_num⟩
  · funext j
    fin_cases j <;> norm_num [Fin.sum_univ_two, diagonalPoints]
  · funext j
    fin_cases j <;> norm_num [Fin.sum_univ_two, antiDiagonalPoints]

def equalCoordinates : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v | v 0 = v 1}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by change x 0 + y 0 = x 1 + y 1; rw [hx, hy]
  smul_mem' c x hx := by change c * _ = c * _; rw [hx]

theorem different_affine_spans :
    affineSpan ℝ (Set.range diagonalPoints) ≠ affineSpan ℝ (Set.range antiDiagonalPoints) := by
  have hle : affineSpan ℝ (Set.range diagonalPoints) ≤ equalCoordinates.toAffineSubspace := by
    apply affineSpan_le.mpr
    rintro x ⟨i, rfl⟩
    change diagonalPoints i 0 = diagonalPoints i 1
    fin_cases i <;> rfl
  intro he
  have hm : antiDiagonalPoints 0 ∈ affineSpan ℝ (Set.range antiDiagonalPoints) :=
    subset_affineSpan ℝ _ (Set.mem_range_self 0)
  rw [← he] at hm
  have hc := hle hm
  change antiDiagonalPoints 0 0 = antiDiagonalPoints 0 1 at hc
  norm_num [antiDiagonalPoints] at hc

/-- Equal normalized first moments do not force equal affine support spaces.
These are probability distributions, with no assertion that they satisfy KL. -/
theorem first_moments_do_not_determine_affine_span :
    (∑ i : Fin 2, (1 / 2 : ℝ) • diagonalPoints i) =
      (∑ i : Fin 2, (1 / 2 : ℝ) • antiDiagonalPoints i) ∧
    affineSpan ℝ (Set.range diagonalPoints) ≠ affineSpan ℝ (Set.range antiDiagonalPoints) :=
  ⟨common_probability_mean.1.trans common_probability_mean.2.1.symm, different_affine_spans⟩

end

end MainTheory.FirstMomentSpanCounterexample
