import MainTheory.D3AffineRankBound
import MainTheory.BoundedGeneratorOrder

/-!
# The sorted distance-three normal form with its actual affine-rank pivot

This module keeps the sparse binary minor through the later local X and
permutation normalizations.  Thus one normal form has the source logical
order, the primitive physical modulus, the real rank of its actual supports,
and the Smith-factor divisibility supplied by that same pivot.
-/

namespace MainTheory.D3AffineNormalForm

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.D3NormalizedFreshPhase
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.D3BoundedNormalForm
open MainTheory.RealSupportAffineRank

variable {n : ℕ}

theorem normalForm_supportAffineRank {d : ℕ} {C : CodeSpec.ExactCode n 2 d}
    (S : SortedForm.SortedNormalForm C) (k : Fin 2) :
    supportAffineRank (S.frame.vec k) = supportAffineRank (S.source.vec k) := by
  have hvec : S.frame.vec k = SixQubit.CodeEquiv.permAct S.perm
      (fun s => S.source.vec k (SS.bxor s S.x0)) := by
    funext s
    exact S.frame_eq k s
  rw [hvec, supportAffineRank_permAct, supportAffineRank_bxor]

theorem boundedGenerator_eigenFrame {q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    letI : NeZero (frameFreshSparsePhase T).data.order := frameFreshOrderNeZero T
    (boundedGenerator T).eigenFrame = G.eigenFrame := by
  letI : NeZero (frameFreshSparsePhase T).data.order := frameFreshOrderNeZero T
  change IntrinsicTransport.shiftFrame (normalizedCode T).frame T.x0 = G.eigenFrame
  exact shiftFrame_normalizedFrame T

/-- The matrix is retained as mathematical data. Its dimension is proved to
be the actual support's affine rank, not merely bounded by that rank. -/
structure AffinePivotBound {d : ℕ} {C : CodeSpec.ExactCode n 2 d}
    (S : SortedForm.SortedNormalForm C) where
  rank : ℕ
  rank_eq : rank = supportAffineRank (S.frame.vec 0)
  rank_pos : 1 ≤ rank
  rank_le_n : rank ≤ n
  matrix : Matrix (Fin rank) (Fin rank) ℤ
  binary : BinaryBeta.IsZeroOne matrix
  nonsingular : matrix.det ≠ 0
  order_dvd : S.q ∣ DeterminantalFactor.lastInvariantFactor matrix
  order_le : S.q ≤ BetaExists.betaOf rank

/-- The sorted normal form from a supplied source generator preserves its
logical order and the sparse modulus, and carries the affine-rank pivot. -/
theorem exists_normalForm_affinePivot_of_generator {q : ℕ} [NeZero q]
    (C : CodeSpec.ExactCode n 2 3)
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    ∃ S : SortedForm.SortedNormalForm C,
      S.q = (frameFreshSparsePhase T).data.order ∧
      S.m = orderOf G.intrinsicClass ∧ S.source = G.eigenFrame ∧
      Nonempty (AffinePivotBound S) := by
  letI : NeZero (frameFreshSparsePhase T).data.order := frameFreshOrderNeZero T
  let Gb := boundedGenerator T
  let Tb := canonicalTwoFiber Gb
  obtain ⟨S, hq, hm, hsource, _, _⟩ :=
    SortedForm.exists_sortedNormalForm_of_generator' C Gb
  have hsource' : S.source = G.eigenFrame :=
    hsource.trans (boundedGenerator_eigenFrame T)
  have hm' : S.m = orderOf G.intrinsicClass := by
    rw [hm, Tb.intrinsic_order_eq,
      BoundedGeneratorOrder.logicalOrder_boundedGenerator T Tb]
    exact T.intrinsic_order_eq.symm
  obtain ⟨r, A, hr, hrpos, hrn, hbinary, hdet, hdvd, hbound, _⟩ :=
    D3AffineRankBound.source_affine_pivot_certificate T
  have hrS : r = supportAffineRank (S.frame.vec 0) := by
    rw [normalForm_supportAffineRank S 0, hsource']
    exact hr
  refine ⟨S, hq, hm', hsource', ⟨{
    rank := r
    rank_eq := hrS
    rank_pos := hrpos
    rank_le_n := hrn
    matrix := A
    binary := hbinary
    nonsingular := hdet
    order_dvd := ?_
    order_le := ?_ }⟩⟩
  · rw [hq]
    exact hdvd
  · rw [hq]
    exact hbound

/-- Returning from the distance-three view restores the original target
distance of the unchanged displayed normal-form frame. -/
def restoreDistance {d : ℕ} (C : CodeSpec.ExactCode n 2 d) (hd : 3 ≤ d)
    (S : SortedForm.SortedNormalForm (SSLPCompleteness.weakenDistance hd C)) :
    SortedForm.SortedNormalForm C :=
  { S with hasDistance := SSLPCompleteness.hasDistance_normalForm hd C S }

def restoreDistance_affinePivot {d : ℕ} (C : CodeSpec.ExactCode n 2 d)
    (hd : 3 ≤ d)
    (S : SortedForm.SortedNormalForm (SSLPCompleteness.weakenDistance hd C))
    (P : AffinePivotBound S) : AffinePivotBound (restoreDistance C hd S) :=
  { P with }

/-- The distance-three SSLP classification for a generator of the entire
intrinsic group, at arbitrary length and original target distance.

One sorted primitive normal form has `m = |G_diag|`, equal actual-support
affine ranks, `q ≤ beta_r ≤ beta_n`, and an r-by-r binary nonsingular pivot
whose last invariant factor is divisible by that same q. -/
theorem d3_sslp_classification_generator_affineRank {d : ℕ}
    (C : CodeSpec.ExactCode n 2 d) (hd : 3 ≤ d)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm C,
      S.m = Nat.card (IntrinsicGroup C) ∧
      supportAffineRank (S.frame.vec 0) = supportAffineRank (S.frame.vec 1) ∧
      S.q ≤ BetaExists.betaOf (supportAffineRank (S.frame.vec 0)) ∧
      BetaExists.betaOf (supportAffineRank (S.frame.vec 0)) ≤ BetaExists.betaOf n ∧
      Nonempty (AffinePivotBound S) := by
  let C3 := SSLPCompleteness.weakenDistance hd C
  haveI := GeneralFiniteness.finite_intrinsicGroup C3
  haveI := GeneralFiniteness.isCyclic C3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := IntrinsicGroup C3)
  have hg1 : g ≠ 1 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hnontrivial
    exact hx (by simpa using hg x)
  have hgcard : orderOf g = Nat.card (IntrinsicGroup C3) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ := LocalPhaseAngle.exists_angleVector (u : LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C3.frame
    (u : LocalPhase n) u.2 theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C3 (u : LocalPhase n) u.2 theta hexp hg1
  letI : NeZero (rationalLift C3 GeneralFiniteness.two_le_three theta hpres).order :=
    ⟨(rationalLift C3 GeneralFiniteness.two_le_three theta hpres).order_pos.ne'⟩
  let G := finiteGenerator C3 GeneralFiniteness.two_le_three theta hpres hnt
  have hclass : G.intrinsicClass = intrinsicClass (exactCodeProjector C3) u :=
    GeneralFiniteness.intrinsicClass_finiteGenerator C3 u theta hexp hpres hnt
  obtain ⟨S3, _, hm, _, ⟨P3⟩⟩ :=
    exists_normalForm_affinePivot_of_generator C3 G (canonicalTwoFiber G)
  let S := restoreDistance C hd S3
  let P := restoreDistance_affinePivot C hd S3 P3
  have hmcard : S.m = Nat.card (IntrinsicGroup C) := by
    change S3.m = Nat.card (IntrinsicGroup C3)
    rw [hm, hclass]
    exact hgcard
  have hrank : supportAffineRank (S.frame.vec 0) = supportAffineRank (S.frame.vec 1) := by
    let hc : CodeSpec.ExactCode n 2 d :=
      { positiveRank := by decide, frame := S.frame, hasDistance := S.hasDistance }
    exact supportAffineRank_eq_of_commonAffineSpan
      (CodeAffineSpanBridge.commonAffineSpan_of_exactCode hc hd)
  refine ⟨S, hmcard, hrank, ?_, ?_, ⟨P⟩⟩
  · rw [← P.rank_eq]
    exact P.order_le
  · exact BetaAtPivotRank.betaOf_mono (supportAffineRank_le _)

end MainTheory.D3AffineNormalForm
