import MainTheory.CodeActiveFace
import MainTheory.RankThresholdBridge
import MainTheory.Generated.RankSymmetry

/-!
# A code's row is rank-compatible

`lem:six-active-rank-reduction` is the second semantic filter: it keeps a
moment-feasible pair only when

  `q <= beta (min (affdim U_0) (affdim U_1))`,

with `U_0, U_1` the *active* faces.  Entering it from a code needs three things
that did not previously exist together.

* The code's two logical supports must lie inside the active masks, not merely
  inside the residue fibres.  That is `CodeActiveFace`, over
  `RealFaceBridge`'s real form of `six:eq:forcedzero`.
* The pivot's denominator bound must be read in the rank filter's own table.
  `RankThresholdBridge` identifies `FiniteRankPipeline.beta` with
  `CoarseFilter.threshold` and supplies the monotonicity.
* The `min` must be resolvable.  The pivot bounds the *left* active rank only;
  the right one comes from the paper's unlabeled Lemma "Maximum support rank
  from the active face", whose finite content -- `affdim U_0 = affdim U_1` on
  every certified row -- is `Generated.RankSymmetry.ranks_equal`.

With those, a code's row satisfies the criterion, so the code is never
discarded by the rank filter either.
-/

namespace MainTheory.CodeRankFilter

open MainTheory
open MainTheory.FinitePipeline
open MainTheory.FiniteRankPipeline
open MainTheory.SortedForm
open MainTheory.SortedPivot
open MainTheory.OuterCompleteness
open MainTheory.RealMomentSeparatorBridge

variable {C : CodeSpec.ExactCode 6 2 3}

/-- **A code occupying a certified rank row makes that row compatible.**

`hsym` is the row's instance of the equal-active-rank lemma; for a row of the
generated table it is `Generated.RankSymmetry.ranks_equal`. -/
theorem compatible_of_pivot {S : SortedNormalForm C} (P : Pivot S)
    (rr : RankRow) (hv : rr.Valid)
    (hpair : rr.pair = recordFiberPair (MainTheory.CodeFiberBridge.recordOf S))
    (hsym : rr.rank0.rank = rr.rank1.rank)
    (hp : RealFeasible rr.pair
      (MainTheory.CodeMomentPoint.weightOf rr.pair
        (S.frame.vec 0) (S.frame.vec 1)))
    (hzero : S.frame.vec 0 (fun _ => false) ≠ 0) :
    rr.compatible = true := by
  have hrank : P.rank ≤ AffineRankCertificate.maskAffineRank rr.face.active0 :=
    MainTheory.CodeActiveFace.rank_le_activeMaskRank P
      (rr.face.certificate rr.pair hv.face_valid) hpair hp hzero
  rw [RankRow.rank0_eq_of_valid hv] at hrank
  have hq : rr.pair.q = S.q := by rw [hpair]; rfl
  have hthr : rr.pair.q ≤ CoarseFilter.threshold P.rank := by
    rw [hq]
    exact MainTheory.CodeActiveFace.pivot_q_le_threshold P
  rw [RankRow.compatible_iff_of_valid hv, ← hsym, min_self]
  exact MainTheory.RankThresholdBridge.q_le_beta_of_le_threshold hthr hrank
    hv.rank0_in_range

/-- The same, for a certified row of the generated table, where the
equal-active-rank hypothesis is discharged. -/
theorem compatible_of_pivot_certified {S : SortedNormalForm C} (P : Pivot S)
    (cert : CertifiedRankRow)
    (hmem : cert ∈ MainTheory.Generated.FiniteRankData.certifiedRows)
    (hpair : cert.row.pair = recordFiberPair (MainTheory.CodeFiberBridge.recordOf S))
    (hp : RealFeasible cert.row.pair
      (MainTheory.CodeMomentPoint.weightOf cert.row.pair
        (S.frame.vec 0) (S.frame.vec 1)))
    (hzero : S.frame.vec 0 (fun _ => false) ≠ 0) :
    cert.row.compatible = true :=
  compatible_of_pivot P cert.row cert.valid hpair
    (MainTheory.Generated.RankSymmetry.ranks_equal cert hmem) hp hzero

end MainTheory.CodeRankFilter
