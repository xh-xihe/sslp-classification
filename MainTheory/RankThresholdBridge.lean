import MainTheory.CoarseFilter
import MainTheory.FiniteRankPipeline

/-!
# The two cutoff tables are one table

The coarse filter states its arithmetic side through `CoarseFilter.threshold`
and the rank filter through `FiniteRankPipeline.beta`.  Both are the paper's
`(beta_1, ..., beta_6) = (1, 1, 2, 3, 5, 9)` with a zero convention outside the
proved range, but they are separate definitions, so nothing yet let a bound
proved against one be used against the other.

A code's pivot produces `q <= threshold P.rank`; the rank filter asks for
`q <= beta (min rank0 rank1)`.  This file supplies the identification and the
monotonicity that carry the first to the second.
-/

namespace MainTheory.RankThresholdBridge

open MainTheory

/-- The rank filter's table and the coarse filter's table agree everywhere,
including on the out-of-range convention. -/
theorem beta_eq_threshold (r : ℕ) :
    FiniteRankPipeline.beta r = CoarseFilter.threshold r := by
  match r with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | (n + 7) =>
      rw [FiniteRankPipeline.beta_eq_zero_of_out_of_range (by omega)]
      rfl

/-- The cutoff is monotone on the proved range. -/
theorem threshold_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 6) :
    CoarseFilter.threshold a ≤ CoarseFilter.threshold b := by
  have ha : a ≤ 6 := hab.trans hb
  interval_cases a <;> interval_cases b <;> simp_all [CoarseFilter.threshold]

/-- The form the rank-filter entry consumes: a denominator bound proved at one
rank transports up to any larger rank in range, and across to `beta`. -/
theorem q_le_beta_of_le_threshold {q a b : ℕ}
    (hq : q ≤ CoarseFilter.threshold a) (hab : a ≤ b) (hb : b ≤ 6) :
    q ≤ FiniteRankPipeline.beta b := by
  rw [beta_eq_threshold]
  exact hq.trans (threshold_mono hab hb)

end MainTheory.RankThresholdBridge
