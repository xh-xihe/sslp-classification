import MainTheory.Generated.FiniteRankData

/-!
# The `(q, m)` table of the active-rank reduction

`main.tex` displays, for the four labelled sectors that survive the moment
programme with `q > m`, a table

  `(q, m)`                  | (6,2) (6,3) (8,2) (9,3)
  moment-feasible pairs     |  52    33    38     4
  rank-compatible pairs     |  30    21     0     0

together with the sentence "Every `(8,2)` moment solution has active rank `4`,
and every `(9,3)` moment solution has active rank `5`", which is what makes the
two zeros in the second row happen.

Only the row totals were theorems here: `PaperReductionChain.moment_lp_reduction`
(291) and `active_rank_reduction` (215).  `Generated.FiniteOrbitDistribution`
slices the surviving inputs by `.m` alone, and its own docstring warns that
counting `.q` "checks a different statement and is a false-green hazard" -- so
nothing in the package looked at the pair `(q, m)` at all.

Everything below reads the generated `rankRows` directly, the same array the
compatibility flag and `PaperReductionChain` are proved against.
-/

namespace MainTheory.RankStageDistribution

open MainTheory.Generated.FiniteRankData

/-! ## Moment-feasible pairs, by `(q, m)` -/

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
theorem feasible_six_two :
    (rankRows.toList.filter (fun r => r.pair.q = 6 && r.pair.m = 2)).length = 52 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
theorem feasible_six_three :
    (rankRows.toList.filter (fun r => r.pair.q = 6 && r.pair.m = 3)).length = 33 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
theorem feasible_eight_two :
    (rankRows.toList.filter (fun r => r.pair.q = 8 && r.pair.m = 2)).length = 38 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
theorem feasible_nine_three :
    (rankRows.toList.filter (fun r => r.pair.q = 9 && r.pair.m = 3)).length = 4 := by
  decide

/-! ## Rank-compatible pairs, by `(q, m)` -/

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
theorem compatible_six_two :
    (rankRows.toList.filter
      (fun r => r.pair.q = 6 && r.pair.m = 2 && r.compatible)).length = 30 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
theorem compatible_six_three :
    (rankRows.toList.filter
      (fun r => r.pair.q = 6 && r.pair.m = 3 && r.compatible)).length = 21 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
/-- **The first of the two zeros.**  No `(8,2)` pair survives the active-rank
cutoff. -/
theorem compatible_eight_two :
    (rankRows.toList.filter
      (fun r => r.pair.q = 8 && r.pair.m = 2 && r.compatible)).length = 0 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
/-- **The second zero.** -/
theorem compatible_nine_three :
    (rankRows.toList.filter
      (fun r => r.pair.q = 9 && r.pair.m = 3 && r.compatible)).length = 0 := by
  decide

/-! ## Why the two zeros happen -/

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
/-- **"Every `(8,2)` moment solution has active rank `4`".**

With `beta_4 = 3 < 8` the compatibility condition fails on every such row, which
is the reason the `(8,2)` column collapses. -/
theorem eight_two_rank_four :
    (rankRows.toList.filter (fun r => r.pair.q = 8 && r.pair.m = 2)).all
      (fun r => r.rank0.rank = 4 && r.rank1.rank = 4) = true := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
/-- **"Every `(9,3)` moment solution has active rank `5`".**

With `beta_5 = 5 < 9` the same happens in the `(9,3)` column. -/
theorem nine_three_rank_five :
    (rankRows.toList.filter (fun r => r.pair.q = 9 && r.pair.m = 3)).all
      (fun r => r.rank0.rank = 5 && r.rank1.rank = 5) = true := by
  decide

/-- **The displayed table, as one statement.** -/
theorem table :
    (rankRows.toList.filter (fun r => r.pair.q = 6 && r.pair.m = 2)).length = 52 ∧
    (rankRows.toList.filter (fun r => r.pair.q = 6 && r.pair.m = 3)).length = 33 ∧
    (rankRows.toList.filter (fun r => r.pair.q = 8 && r.pair.m = 2)).length = 38 ∧
    (rankRows.toList.filter (fun r => r.pair.q = 9 && r.pair.m = 3)).length = 4 ∧
    (rankRows.toList.filter
      (fun r => r.pair.q = 6 && r.pair.m = 2 && r.compatible)).length = 30 ∧
    (rankRows.toList.filter
      (fun r => r.pair.q = 6 && r.pair.m = 3 && r.compatible)).length = 21 ∧
    (rankRows.toList.filter
      (fun r => r.pair.q = 8 && r.pair.m = 2 && r.compatible)).length = 0 ∧
    (rankRows.toList.filter
      (fun r => r.pair.q = 9 && r.pair.m = 3 && r.compatible)).length = 0 :=
  ⟨feasible_six_two, feasible_six_three, feasible_eight_two, feasible_nine_three,
    compatible_six_two, compatible_six_three, compatible_eight_two,
    compatible_nine_three⟩

end MainTheory.RankStageDistribution
