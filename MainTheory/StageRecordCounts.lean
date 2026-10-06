import MainTheory.Generated.FinitePairRecordData
import MainTheory.Generated.FinitePairData
import MainTheory.Generated.FiniteMomentData
import MainTheory.ActiveRankRecordCount

/-!
# The record-level counts of the six-qubit reduction

Three of the reduction lemmas state their result twice: once as a number of
deduplicated *labelled fibre pairs*, and once as a number of *sorted primitive
angle records* representing them.  The pair-level halves are
`PaperReductionChain.affine_smith_reduction` (508),
`PaperReductionChain.moment_lp_reduction` (291) and
`PaperReductionChain.active_rank_reduction` (215).

Only one of the three record-level halves was proved --
`ActiveRankRecordCount.compatible_record_count`, the 216 of
`lem:six-active-rank-reduction`.  The other two say

* "reduces the 11,422 labeled pairs to 508 labeled pairs, represented by 510
  sorted primitive angle records" (`lem:six-affine-smith-reduction`), and
* "291 distinct labeled fiber pairs, represented by 292 angle records"
  (`lem:six-moment-lp-reduction`),

and neither number occurred anywhere in this package.  The counts are not
re-derived here: they are taken through `FinitePairRecordData.recordPairId`,
the provenanced record-to-pair map whose exactness `FinitePairProvenance`
proves in both directions, so they are statements about the map the pipeline
itself uses.

Two mechanical points.  `Array.contains` does not reduce inside a `List.filter`
in the kernel -- it goes through `Array.anyM` -- while `Array.toList.contains`
does, so the coarse membership test is written on the list.  And the cost is
`12,768` records against the length of the id list, which for the `508` stage is
more than twice the `215` one that already takes about ten minutes; the counts
are therefore reduced in shards, `take`/`drop` slices of the record range whose
lengths add by `List.filter_append`.
-/

namespace MainTheory.StageRecordCounts

open MainTheory.Generated

/-- Membership of a record's pair in the affine--Smith survivors. -/
def coarseP (i : Fin 12768) : Bool :=
  FinitePairData.coarsePairIds.toList.contains
    (FinitePairRecordData.recordPairId i).val

/-- Membership of a record's pair in the moment-feasible survivors. -/
def feasibleP (i : Fin 12768) : Bool :=
  FiniteMomentData.feasiblePairIds.contains
    (FinitePairRecordData.recordPairId i).val

/-- Splitting the record range at any point splits the count. -/
theorem length_filter_split (p : Fin 12768 → Bool) (l : List (Fin 12768)) (k : ℕ) :
    (l.filter p).length
      = ((l.take k).filter p).length + ((l.drop k).filter p).length := by
  conv_lhs => rw [← List.take_append_drop k l]
  rw [List.filter_append, List.length_append]

/-! ## The affine--Smith stage: `508` pairs, `510` records -/

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 400000000 in
theorem coarse_shard0 :
    (((List.finRange 12768).take 3192).filter coarseP).length = 436 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 400000000 in
theorem coarse_shard1 :
    ((((List.finRange 12768).drop 3192).take 3192).filter coarseP).length = 52 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 400000000 in
theorem coarse_shard2 :
    (((((List.finRange 12768).drop 3192).drop 3192).take 3192).filter
      coarseP).length = 16 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 400000000 in
theorem coarse_shard3 :
    (((((List.finRange 12768).drop 3192).drop 3192).drop 3192).filter
      coarseP).length = 6 := by
  decide

/-- **The `508` affine--Smith pairs are represented by exactly `510` primitive
angle records** (`lem:six-affine-smith-reduction`). -/
theorem coarse_record_count :
    ((List.finRange 12768).filter coarseP).length = 510 := by
  rw [length_filter_split coarseP (List.finRange 12768) 3192,
    length_filter_split coarseP ((List.finRange 12768).drop 3192) 3192,
    length_filter_split coarseP
      (((List.finRange 12768).drop 3192).drop 3192) 3192,
    coarse_shard0, coarse_shard1, coarse_shard2, coarse_shard3]

/-- Two of the coarse pairs carry two records apiece; the remaining `506` carry
one. -/
theorem coarse_two_more_records_than_pairs :
    ((List.finRange 12768).filter coarseP).length
      = FinitePairData.coarsePairIds.size + 2 := by
  rw [coarse_record_count, FinitePairData.coarsePairIds_size]

/-! ## The moment stage: `291` pairs, `292` records -/

set_option maxRecDepth 40000 in
theorem feasiblePairIds_length :
    FiniteMomentData.feasiblePairIds.length = 291 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 400000000 in
theorem feasible_shard0 :
    (((List.finRange 12768).take 6384).filter feasibleP).length = 274 := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 400000000 in
theorem feasible_shard1 :
    (((List.finRange 12768).drop 6384).filter feasibleP).length = 18 := by
  decide

/-- **The `291` moment-feasible pairs are represented by exactly `292` angle
records** (`lem:six-moment-lp-reduction`). -/
theorem feasible_record_count :
    ((List.finRange 12768).filter feasibleP).length = 292 := by
  rw [length_filter_split feasibleP (List.finRange 12768) 6384,
    feasible_shard0, feasible_shard1]

/-- Exactly one duplicate survives the moment programme, which is the paper's
own reading of `292` against `291`. -/
theorem feasible_one_more_record_than_pair :
    ((List.finRange 12768).filter feasibleP).length
      = FiniteMomentData.feasiblePairIds.length + 1 := by
  rw [feasible_record_count, feasiblePairIds_length]

/-- **The three record-level counts together.**

`510 -> 292 -> 216` is the record-level shadow of the pair-level chain
`508 -> 291 -> 215`, so the number of merged duplicates falls from two to one
to one along the reduction. -/
theorem record_level_chain :
    ((List.finRange 12768).filter coarseP).length = 510 ∧
      ((List.finRange 12768).filter feasibleP).length = 292 ∧
      ((List.finRange 12768).filter
        (fun i => FinitePairData.compatiblePairIds.toList.contains
          (FinitePairRecordData.recordPairId i).val)).length = 216 :=
  ⟨coarse_record_count, feasible_record_count,
    MainTheory.ActiveRankRecordCount.compatible_record_count⟩

end MainTheory.StageRecordCounts
