import MainTheory.RealFaceBridge
import MainTheory.CodeMomentPoint
import MainTheory.SortedPivot

/-!
# A code's support lies on the active face, and bounds its rank

The coarse filter's `S_0` clause is a statement about the *full* residue fibre
`mask0`.  The next filter, `lem:six-active-rank-reduction`, asks the same
question of the strictly smaller *active* mask: the coordinates that can be
positive at some feasible moment point.  A code does not automatically live
there -- unless one knows that its own point is feasible and that the face
certificate forces every feasible point onto the face.

Both are now available.  `CodeMomentPoint` gives the code's real point, and
`RealFaceBridge` extends the paper's `six:eq:forcedzero` from the rational
programme to the real one.  Together they put the code's two logical supports
inside the two active masks.

The rank bound then follows from the same pivot that proves the `S_0` clause.
`SortedPivot.Pivot.rank_le_maskAffineRank` is stated for `mask0` because it
appeals to `residueZeroMask_affineRank_eq_span`; the underlying lemma
`MaskRankBridge.maskAffineRank_eq_finrank_span` needs only that the mask
contains the zero word, which the active mask does -- because the normalized
first logical word is nonzero there.
-/

namespace MainTheory.CodeActiveFace

open MainTheory
open MainTheory.FinitePipeline
open MainTheory.SortedForm
open MainTheory.SortedPivot
open MainTheory.OuterCompleteness
open MainTheory.RealMomentSeparatorBridge

variable {C : CodeSpec.ExactCode 6 2 3}

/-- The zero word names the all-false Boolean string. -/
@[simp] theorem wordBitString_zero :
    wordBitString (0 : Word6) = (fun _ => false) := by decide

/-! ## The pivot bound at an arbitrary mask -/

/-- **The pivot's rank bounds the affine rank of any mask containing the zero
word and the pivot's own words.**

This is `SortedPivot.Pivot.rank_le_maskAffineRank` with the residue-zero fibre
replaced by a hypothesis, which is what lets it be applied at the active
mask. -/
theorem pivot_rank_le_maskAffineRank {S : SortedNormalForm C} (P : Pivot S)
    (mask : ℕ) (hzero : InMask mask (0 : Word6))
    (hmem : ∀ i, InMask mask (P.words i)) :
    P.rank ≤ AffineRankCertificate.maskAffineRank mask := by
  rw [MaskRankBridge.maskAffineRank_eq_finrank_span hzero]
  refine MaskRankBridge.card_le_finrank_span_of_subset P.words hmem ?_
  have hfun : (fun i => AffineRankCertificate.point (P.words i))
      = fun i => MaskRankBridge.qpoint (P.vertex i) := by
    funext i
    rw [← MaskRankBridge.qpoint_wordBitString, P.wordBitString_words]
  rw [hfun]
  exact P.linearIndependent

/-- **The denominator bound the pivot really proves.**

`SortedPivot.Pivot.rMin_le_rank` immediately converts this into the `r_min`
form the coarse filter wants; the rank filter wants the `threshold` form
instead, so it is exposed here rather than reproved. -/
theorem pivot_q_le_threshold {S : SortedNormalForm C} (P : Pivot S) :
    S.q ≤ CoarseFilter.threshold P.rank :=
  (Nat.le_of_dvd (SharpClearing.inverseDenominator_pos P.matrix)
      P.q_dvd_inverseDenominator).trans
    (MainTheory.ThresholdBoundsSmall.thresholdBounds.upper
      P.rank P.rank_pos P.rank_le P.rank P.rank_pos (Nat.le_refl _)
      P.matrix P.isZeroOne P.nonsingular)

/-! ## The code's support is active -/

/-- A word carrying nonzero amplitude has positive weight. -/
theorem weightOf_ne_zero {pair : FiberPair} {c d : SS.State 6 ℂ}
    (x : LeftFiber pair) (hx : c (wordBitString x.1) ≠ 0) :
    MainTheory.CodeMomentPoint.weightOf pair c d (Sum.inl x) ≠ 0 := by
  simpa [MainTheory.CodeMomentPoint.weightOf, Complex.normSq_eq_zero] using hx

theorem weightOf_ne_zero_right {pair : FiberPair} {c d : SS.State 6 ℂ}
    (y : RightFiber pair) (hy : d (wordBitString y.1) ≠ 0) :
    MainTheory.CodeMomentPoint.weightOf pair c d (Sum.inr y) ≠ 0 := by
  simpa [MainTheory.CodeMomentPoint.weightOf, Complex.normSq_eq_zero] using hy

/-- **The first logical word is supported inside the active mask.** -/
theorem inMask_active0 {pair : FiberPair} (cert : FaceCertificate pair)
    {c d : SS.State 6 ℂ}
    (hp : RealFeasible pair (MainTheory.CodeMomentPoint.weightOf pair c d))
    (x : Word6) (hx0 : InMask pair.mask0 x) (hx : c (wordBitString x) ≠ 0) :
    InMask cert.active0 x := by
  by_contra hno
  exact weightOf_ne_zero (pair := pair) (c := c) (d := d) ⟨x, hx0⟩ hx
    ((MainTheory.RealFaceBridge.realSupport_subset_face cert hp).1 ⟨x, hx0⟩ hno)

/-- **The second logical word is supported inside the active mask.** -/
theorem inMask_active1 {pair : FiberPair} (cert : FaceCertificate pair)
    {c d : SS.State 6 ℂ}
    (hp : RealFeasible pair (MainTheory.CodeMomentPoint.weightOf pair c d))
    (y : Word6) (hy1 : InMask pair.mask1 y) (hy : d (wordBitString y) ≠ 0) :
    InMask cert.active1 y := by
  by_contra hno
  exact weightOf_ne_zero_right (pair := pair) (c := c) (d := d) ⟨y, hy1⟩ hy
    ((MainTheory.RealFaceBridge.realSupport_subset_face cert hp).2 ⟨y, hy1⟩ hno)

/-! ## The `S_0` clause at the active mask -/

/-- **The active-face form of the `S_0` clause.**

Given a code in sorted normal form whose first logical word is nonzero at the
zero word -- which the normalization arranges -- its pivot's rank bounds the
affine rank of the *active* mask, not merely of the full residue fibre. -/
theorem rank_le_activeMaskRank {S : SortedNormalForm C} (P : Pivot S)
    {pair : FiberPair} (cert : FaceCertificate pair)
    (hpair : pair = recordFiberPair (MainTheory.CodeFiberBridge.recordOf S))
    (hp : RealFeasible pair
      (MainTheory.CodeMomentPoint.weightOf pair
        (S.frame.vec 0) (S.frame.vec 1)))
    (hzero : S.frame.vec 0 (fun _ => false) ≠ 0) :
    P.rank ≤ AffineRankCertificate.maskAffineRank cert.active0 := by
  subst hpair
  refine pivot_rank_le_maskAffineRank P cert.active0 ?_ ?_
  · refine inMask_active0 cert hp (0 : Word6) ?_ ?_
    · exact MainTheory.CodeFiberBridge.support_mask0 S (0 : Word6)
        (by simpa [wordBitString_zero] using hzero)
    · simpa [wordBitString_zero] using hzero
  · intro i
    refine inMask_active0 cert hp (P.words i) ?_ ?_
    · exact P.words_inMask i
    · rw [P.wordBitString_words]
      exact P.vertex_supported i

end MainTheory.CodeActiveFace
