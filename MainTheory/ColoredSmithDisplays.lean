import MainTheory.FiniteLift
import MainTheory.BinaryPivot
import MainTheory.BetaExists

namespace MainTheory.ColoredSmithDisplays

open MainTheory.FiniteLift MainTheory.PhaseSectorFull MainTheory.SharpClearing

variable {n t : ℕ} {theta : Fin n → ℝ} {s : Type*}
  [Fintype s] [DecidableEq s] [Nonempty s] [LinearOrder s]

theorem fullSolution_smith_integral {D : SectorDecomposition n t theta}
    (P : PivotData D s) (W : SmithWitness P.matrix) :
    ∀ c, ∃ z : ℤ, (W.lastFactor : ℚ) * P.fullSolution c = (z : ℚ) := by
  classical
  intro c
  obtain ⟨z, hz⟩ := W.lastFactor_universallyClears P.rhs
  by_cases hc : ∃ i, P.column i = c
  · obtain ⟨i, rfl⟩ := hc
    refine ⟨z i, ?_⟩
    rw [PivotData.fullSolution, extendByZero_apply_column]
    exact hz i
  · refine ⟨0, ?_⟩
    have he : P.fullSolution c = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [show P.column i ≠ c from fun h => hc ⟨i, h⟩, ↓reduceIte]
    rw [he, mul_zero, Int.cast_zero]

omit [Fintype s] [DecidableEq s] [Nonempty s] [LinearOrder s] in
theorem smithLastFactor_le_betaOf {r : ℕ} [NeZero r] {D : SectorDecomposition n t theta}
    (P : PivotData D (Fin r)) (W : SmithWitness P.matrix) :
    W.lastFactor ≤ MainTheory.BetaExists.betaOf r := by
  rw [← inverseDenominator_eq_smithLastFactor W, MainTheory.BinaryPivot.inverseDenominator_eq]
  exact MainTheory.BetaExists.le_betaAt
    (MainTheory.BinaryPivot.binMatrix_isZeroOne P) |>.trans
      (Finset.le_sup (f := MainTheory.BetaExists.betaAt)
        (Finset.mem_range.mpr (by omega)))

end MainTheory.ColoredSmithDisplays
