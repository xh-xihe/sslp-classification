import MainTheory.Generated.FinitePairRecordData
import MainTheory.Generated.FinitePairData

/-!
# The `216` of `lem:six-active-rank-reduction`

The lemma's statement has two halves.  The pair-level half -- that the active
rank criterion takes the `291` moment-feasible pairs to `215` rank-compatible
ones -- is `PaperReductionChain.active_rank_reduction`.  The other half says
those `215` pairs are *represented by `216` primitive angle records*, and until
now no theorem here mentioned `216` at all: the reduction works at the level of
deduplicated fibre pairs, and the count only reappears when one projects back
onto the `12,768` records that the hashing merged.

That projection is exactly `FinitePairRecordData.recordPairId`, the
provenanced record-to-pair map whose exactness `FinitePairProvenance` already
proves in both directions.  So the count below is a statement about the same
map the pipeline uses, not about a re-derived one.

The one wrinkle is mechanical.  `Array.contains` does not reduce inside a
`List.filter` in the kernel -- it goes through `Array.anyM` -- while
`Array.toList.contains` does; hence the membership test is written on the
list.  `Array.toList` of a literal array is the literal list, so nothing about
the certificate changes.  The reduction takes about ten minutes.
-/

namespace MainTheory.ActiveRankRecordCount

open MainTheory.Generated

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 100000000 in
/-- **The `215` rank-compatible pairs are represented by exactly `216`
primitive angle records.**

One compatible pair therefore carries two records and the remaining `214`
carry one apiece; the hashing of `lem:six-fiber-hashing` merged exactly one
pair of records inside the surviving set. -/
theorem compatible_record_count :
    ((List.finRange 12768).filter
      (fun i => FinitePairData.compatiblePairIds.toList.contains
        (FinitePairRecordData.recordPairId i).val)).length = 216 := by
  decide

/-- The complementary reading: `216` records for `215` pairs, so exactly one
duplicate among the compatible rows. -/
theorem one_more_record_than_pair :
    ((List.finRange 12768).filter
        (fun i => FinitePairData.compatiblePairIds.toList.contains
          (FinitePairRecordData.recordPairId i).val)).length
      = FinitePairData.compatiblePairIds.size + 1 := by
  rw [compatible_record_count, FinitePairData.compatiblePairIds_size]

end MainTheory.ActiveRankRecordCount
