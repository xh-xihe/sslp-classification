import MainTheory.Generated.FiniteCoarseDirectory
import MainTheory.Generated.ExtraMomentData

/-!
# The coarse filter never discards a code

`CoarseFilter.Directory.Valid.realization_retained` already says the coarse
filter keeps every genuine realization -- but only against
`PrimitiveLiftRealization`, whose rank field wants the paper's `q <= beta_r`
at the **affine** rank of the support.  That bound does not follow from the
linear-rank one this development proves (`results/coarse-filter-audit.md`), so
that route into the filter is not available.

This file takes the other route, which needs no unproved input and changes no
number the paper reports.  Each discarded row carries one of two witnesses.

* A row rejected by the **left** witness fails the `S_0` clause outright, and
  `MaskRankBridge` plus `CoarseFilterEntry` prove that clause holds for a
  code.  So a code's row is never left-rejected.
* A row rejected by the **right** witness admits no common moment point at
  all: all 422 of them are certified in `Generated.ExtraMomentData`.  A code
  supplies its own common moment point, so a code's row is never
  right-rejected either.

Hence a code's row is kept, whatever the status of the clause that the right
witness certifies.

`keepAt_of_s0_of_feasible` is that argument.  It carries one hypothesis,
`henum`, saying the row's pair is among the 422 certified ones whenever the
row is right-rejected.  That is a decidable, purely combinatorial fact about
the generated directory -- true by construction, since the 422 were read off
the directory's own source -- and discharging it needs a per-row enumeration
over all 11,422 rows, which is generated data this file deliberately does not
inline.
-/

namespace MainTheory.CoarseFilterSound

open MainTheory.CoarseFilter
open MainTheory.FinitePipeline
open MainTheory.Generated.FinitePairMappingBase

/-- The constructor tag of a decision witness, as a Boolean. -/
def isRejectRight {p : FiberPair} : DecisionWitness p → Bool
  | .rejectRight _ => true
  | _ => false

/-- The `S_0` half of the coarse criterion, as a predicate on a pair. -/
def S0Clause (p : FiberPair) : Prop :=
  rMin p.q ≤ AffineRankCertificate.maskAffineRank p.mask0

/-- **A left-rejected row fails the `S_0` clause.**

This is sharper than `RejectLeftWitness.not_fullFiberCriterion`, which only
denies the conjunction; the left witness is an upper certificate for `mask0`
alone, so it denies the left conjunct by itself. -/
theorem not_s0Clause_of_rejectLeft {p : FiberPair} (w : RejectLeftWitness p) :
    ¬ S0Clause p := by
  intro h
  exact (Nat.not_lt_of_ge
    (h.trans (AffineRankCertificate.maskAffineRank_le_rank_of_upperListInverse
      w.upper))) w.below

/-- **The coarse filter keeps every row that a code could occupy.**

`h0` is what a code supplies through `CoarseFilterEntry`, and `hf` is the
code's own pair of distributions.  `henum` is the combinatorial bookkeeping
described in the module docstring. -/
theorem keepAt_of_s0_of_feasible
    (i : PairId)
    (henum : isRejectRight
        (MainTheory.Generated.FiniteCoarseDirectory.directory.decisionAt i)
        = true →
      MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i ∈
        MainTheory.Generated.ExtraMoment.rejectRightPairs)
    (h0 : S0Clause
      (MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i))
    (hf : ∃ p0 p1, Feasible
      (MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i) p0 p1) :
    MainTheory.Generated.FiniteCoarseDirectory.directory.keepAt i = true := by
  unfold MainTheory.CoarseFilter.Directory.keepAt
  cases hd : MainTheory.Generated.FiniteCoarseDirectory.directory.decisionAt i
      with
  | keep w => rfl
  | rejectLeft w => exact absurd h0 (not_s0Clause_of_rejectLeft w)
  | rejectRight w =>
      exact absurd hf
        (MainTheory.Generated.ExtraMoment.rejectRightPairs_infeasible _
          (henum (by rw [hd]; rfl)))

/-- The same conclusion phrased through the intrinsic criterion: for a row a
code could occupy, the full two-clause criterion holds after all. -/
theorem fullFiberCriterion_of_s0_of_feasible
    (i : PairId)
    (henum : isRejectRight
        (MainTheory.Generated.FiniteCoarseDirectory.directory.decisionAt i)
        = true →
      MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i ∈
        MainTheory.Generated.ExtraMoment.rejectRightPairs)
    (h0 : S0Clause
      (MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i))
    (hf : ∃ p0 p1, Feasible
      (MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i) p0 p1) :
    FullFiberCriterion
      (MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i) :=
  (MainTheory.Generated.FiniteCoarseDirectory.keep_iff_fullFiberCriterion i).1
    (keepAt_of_s0_of_feasible i henum h0 hf)

end MainTheory.CoarseFilterSound
