import MainTheory.CoarseFilter
import MainTheory.Generated.BinaryBetaSmall.Size4.Certificate
import MainTheory.Generated.BinaryBetaFiveFast.Certificate
import MainTheory.Generated.BinaryBetaSixKernel.Certificate

/-!
# `CoarseFilter.ThresholdBounds` is inhabited

`ThresholdBounds` demands `BetaBound r (threshold r)` for every `r <= 6`.  The
repository proved the three that are hard -- `BetaBound 4 3`, `BetaBound 5 5`,
`BetaBound 6 9`, each a generated kernel enumeration -- and none of the three
that are easy.  So the structure had **no inhabitant**, and with it
`CoarseFilter.fullFiberCriterion_of_realization` and
`Directory.Valid.realization_retained` could not be applied to anything: their
soundness was real but unusable.

The missing three are `beta_1 = beta_2 = 1` and `beta_3 = 2`.  They need no
enumeration machinery: `BinaryBeta.betaBound_of_fixedSize_detNatAbs_bound`
reduces a `BetaBound` at a fixed size to an absolute-determinant bound on
zero--one matrices of that size, and at sizes one, two and three the
determinant is a short explicit polynomial in entries that are each `0` or
`1`.
-/

namespace MainTheory.ThresholdBoundsSmall

open MainTheory.BinaryBeta
open MainTheory.CoarseFilter

set_option maxHeartbeats 2000000

/-- A `1 x 1` zero--one determinant is `0` or `1`. -/
theorem detNatAbs_le_one_of_fin_one (C : Matrix (Fin 1) (Fin 1) ℤ)
    (h : IsZeroOne C) : C.det.natAbs ≤ 1 := by
  rw [Matrix.det_fin_one]
  rcases h 0 0 with h00 | h00 <;> simp only [h00] <;> decide

/-- A `2 x 2` zero--one determinant is `0` or `±1`. -/
theorem detNatAbs_le_one_of_fin_two (C : Matrix (Fin 2) (Fin 2) ℤ)
    (h : IsZeroOne C) : C.det.natAbs ≤ 1 := by
  rw [Matrix.det_fin_two]
  rcases h 0 0 with h00 | h00 <;> rcases h 0 1 with h01 | h01 <;>
    rcases h 1 0 with h10 | h10 <;> rcases h 1 1 with h11 | h11 <;>
    simp only [h00, h01, h10, h11] <;> decide

/-- A `3 x 3` zero--one determinant is at most two in absolute value. -/
theorem detNatAbs_le_two_of_fin_three (C : Matrix (Fin 3) (Fin 3) ℤ)
    (h : IsZeroOne C) : C.det.natAbs ≤ 2 := by
  rw [Matrix.det_fin_three]
  rcases h 0 0 with h00 | h00 <;> rcases h 0 1 with h01 | h01 <;>
    rcases h 0 2 with h02 | h02 <;> rcases h 1 0 with h10 | h10 <;>
    rcases h 1 1 with h11 | h11 <;> rcases h 1 2 with h12 | h12 <;>
    rcases h 2 0 with h20 | h20 <;> rcases h 2 1 with h21 | h21 <;>
    rcases h 2 2 with h22 | h22 <;>
    simp only [h00, h01, h02, h10, h11, h12, h20, h21, h22] <;> decide

theorem betaBound_one : BetaBound 1 1 :=
  betaBound_of_fixedSize_detNatAbs_bound
    fun C hC _ => detNatAbs_le_one_of_fin_one C hC

theorem betaBound_two : BetaBound 2 1 :=
  betaBound_of_fixedSize_detNatAbs_bound
    fun C hC _ => detNatAbs_le_one_of_fin_two C hC

theorem betaBound_three : BetaBound 3 2 :=
  betaBound_of_fixedSize_detNatAbs_bound
    fun C hC _ => detNatAbs_le_two_of_fin_three C hC

/-- **The paper's threshold table, as universal theorems.**

`(beta_1, ..., beta_6) = (1, 1, 2, 3, 5, 9)` is `six:eq:betasix`; the first
three are proved just above, the last three are the generated enumerations. -/
theorem thresholdBounds : ThresholdBounds where
  upper r hr1 hr6 := by
    interval_cases r
    · exact betaBound_one
    · exact betaBound_two
    · exact betaBound_three
    · exact MainTheory.Generated.BinaryBetaSmall.Size4.Certificate.upper
    · exact MainTheory.Generated.BinaryBetaFiveFast.Certificate.upper
    · exact MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper

end MainTheory.ThresholdBoundsSmall
