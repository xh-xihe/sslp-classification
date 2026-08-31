import MainTheory.Generated.FiniteMomentRankContinuity
import MainTheory.Generated.FiniteOrbitBase
import MainTheory.Generated.FiniteRankData

/-!
# Exact continuity from the 215 compatible rank rows to the orbit inputs

`FiniteOrbitRankBridge` checks the input labels.  This companion leaf checks
the stronger invariant: at every position, that label is still attached to
the same actual `FiberPair` on which the rank certificate was proved.
-/


namespace MainTheory.Generated.FiniteRankOrbitContinuity

open MainTheory.FinitePipeline
open MainTheory.FiniteRankPipeline

abbrev PairEntry :=
  MainTheory.Generated.FiniteMomentRankContinuity.PairEntry

def ofOrbitInput (entry : Nat × FiberPair) : PairEntry where
  pairId := entry.1
  pair := entry.2

/-- The 215 orbit inputs with the paper-table label and actual pair kept
together.  `List.zip` is itself checked by the equality theorem below, so a
length mismatch cannot be hidden by truncation. -/
def orbitInputEntries : Array PairEntry :=
  ((MainTheory.Generated.FiniteOrbitBase.inputPairIds.zip
      (List.ofFn MainTheory.Generated.FiniteOrbitBase.inputAt)).map
        ofOrbitInput).toArray

/-- The compatible rank rows, retaining both fields rather than projecting
only their numeric labels. -/
def compatibleRankEntries : Array PairEntry :=
  ((MainTheory.Generated.FiniteRankData.compatibleRows.map
      MainTheory.Generated.FiniteMomentRankContinuity.ofRankRow).toArray)

/-- The orbit directory is built from exactly the actual pairs accepted by
the rank cutoff.  A substituted pair with an unchanged id makes this theorem
fail kernel reduction. -/
theorem orbitInputEntries_eq_compatibleRankEntries :
    orbitInputEntries = compatibleRankEntries := by
  decide

end MainTheory.Generated.FiniteRankOrbitContinuity
