import MainTheory.Generated.FiniteMomentData
import MainTheory.Generated.FiniteRankData

/-!
# Exact continuity from the 291 feasible moment rows to the rank rows

The original rank summary compared only the sequence of numeric pair labels.
That did not prevent a rank certificate from carrying a different `FiberPair`
under the right label.  Here each label is kept together with its actual pair,
and the complete 291-entry arrays are compared by ordinary kernel reduction.
-/


namespace MainTheory.Generated.FiniteMomentRankContinuity

set_option maxRecDepth 1000000

open MainTheory.FinitePipeline
open MainTheory.FiniteRankPipeline

/-- A pair label inseparably coupled to the fibre pair it denotes. -/
structure PairEntry where
  pairId : Nat
  pair : FiberPair
  deriving DecidableEq, Repr

def ofMomentRow (row : CertifiedMomentRow) : PairEntry where
  pairId := row.pairId
  pair := row.pair

def ofRankRow (row : RankRow) : PairEntry where
  pairId := row.pairId
  pair := row.pair

/-- The feasible sublist selected from the exact 508 moment rows. -/
def feasibleMomentEntries : Array PairEntry :=
  (((MainTheory.Generated.FiniteMomentData.certifiedRows.filter
      (fun row => row.result.isFeasible)).map ofMomentRow).toArray)

/-- The source labels and actual pairs on which the 291 rank certificates
were checked. -/
def rankEntries : Array PairEntry :=
  ((MainTheory.Generated.FiniteRankData.certifiedRows.map
      (fun cert => ofRankRow cert.row)).toArray)

/-- Every rank row is bound to the corresponding feasible moment row by both
its label and its actual `FiberPair`; equality of labels alone is not used. -/
theorem rankEntries_eq_feasibleMomentEntries :
    rankEntries = feasibleMomentEntries := by
  decide

end MainTheory.Generated.FiniteMomentRankContinuity
