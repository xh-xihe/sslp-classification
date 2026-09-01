import MainTheory.Generated.FiniteCoarseMomentBridge
import MainTheory.Generated.FiniteMomentData

/-!
# Exact continuity from the 508 coarse outputs to the moment rows

The coarse directory and the legacy moment summary were generated through
different module trees.  Equality of their pair-id lists would not be enough:
the same labels could be attached to different fibre pairs.  This leaf module
therefore compares, in order, the complete kernel-relevant entry

`(pair id, actual FiberPair, feasible/infeasible flag)`.

The proof uses ordinary kernel reduction (`decide`), not `native_decide`.
-/


namespace MainTheory.Generated.FiniteCoarseMomentContinuity

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

open MainTheory.FinitePipeline

/-- The data which must remain attached while the 508 coarse outputs are
handed to the moment-feasibility stage. -/
structure MomentEntry where
  pairId : Nat
  pair : FiberPair
  feasible : Bool
  deriving DecidableEq, Repr

def ofRow (row : CertifiedMomentRow) : MomentEntry where
  pairId := row.pairId
  pair := row.pair
  feasible := row.result.isFeasible

/-- Entries indexed by the exact, provenanced 508-output coarse directory. -/
def coarseEntries : Array MomentEntry :=
  (List.ofFn fun j =>
    ofRow (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j)).toArray

/-- Entries used by the independently generated 508-row moment summary. -/
def certifiedEntries : Array MomentEntry :=
  (MainTheory.Generated.FiniteMomentData.certifiedRows.map ofRow).toArray

/-- The two 508-row stages agree on the actual fibre pair and feasibility flag,
not merely on a same-numbered label. -/
theorem coarseEntries_eq_certifiedEntries :
    coarseEntries = certifiedEntries := by
  decide

/-- Consequently the exact coarse outputs contain precisely 291 rows carrying
feasible moment certificates. -/
theorem coarse_feasible_count :
    (coarseEntries.toList.filter (fun entry => entry.feasible)).length = 291 := by
  decide

end MainTheory.Generated.FiniteCoarseMomentContinuity
