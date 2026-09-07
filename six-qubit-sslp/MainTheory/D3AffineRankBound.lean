import MainTheory.RealSupportAffineRank
import MainTheory.BetaAtPivotRank
import MainTheory.PaperSmithFactor
import MainTheory.QMinBound
import MainTheory.SSLPCompleteness

/-!
# Distance-three lift bounds at the real affine rank of the source support

The sparse pivot is taken after local X normalization, but its size is
identified below with the real affine rank of the original generator's
actual support.  The bounded-class transport recovers the original
projective class, rather than retaining only the normalized coprime power.

The code-facing theorem retains the original target distance in the
displayed eigenframe.  The dimension is neither the full-fiber rank nor
an unconstrained auxiliary natural number.
-/

namespace MainTheory.D3AffineRankBound

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.GeneralLiftOrder
open MainTheory.SectionTwoGeneral
open MainTheory.D3NormalizedFreshPhase
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.RealSupportAffineRank

variable {n : ℕ}

theorem normalized_zero_supported {d q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 d}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    (normalizedFrame T).vec 0 (fun _ => false) ≠ 0 := by
  have hval : (normalizedFrame T).vec 0 (fun _ => false)
      = G.eigenFrame.vec 0 T.x0 := by
    simp [normalizedFrame, normalizedState]
  rw [hval]
  exact T.base_supported

/-- Local X normalization preserves each actual support's real affine rank. -/
theorem normalized_supportAffineRank {d q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 d}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) (k : Fin 2) :
    supportAffineRank ((normalizedFrame T).vec k)
      = supportAffineRank (G.eigenFrame.vec k) :=
  supportAffineRank_bxor (G.eigenFrame.vec k) T.x0

/-- The actual pivot dimension is precisely the original left support's
real affine dimension. -/
theorem fresh_basis_rank_eq_source_affineRank {q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    (frameFreshSparsePhase T).basis.rank
      = supportAffineRank (G.eigenFrame.vec 0) := by
  rw [RealSupportAffineRank.SupportedBitBasis.rank_eq_supportAffineRank
    (frameFreshSparsePhase T).basis (normalized_zero_supported T)]
  exact normalized_supportAffineRank T 0

theorem fresh_order_le_betaOf_source_affineRank {q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    (frameFreshSparsePhase T).data.order
      ≤ BetaExists.betaOf (supportAffineRank (G.eigenFrame.vec 0)) := by
  rw [← fresh_basis_rank_eq_source_affineRank T]
  exact BetaAtPivotRank.FreshSparsePhase.order_le_betaOf_rank (frameFreshSparsePhase T)

/-- A single sparse pivot has the source's affine dimension, is binary and
nonsingular, and gives the sharp denominator divisibility and size bound. -/
theorem source_affine_pivot_certificate {q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    ∃ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ),
      r = supportAffineRank (G.eigenFrame.vec 0) ∧
      1 ≤ r ∧ r ≤ n ∧ BinaryBeta.IsZeroOne A ∧ A.det ≠ 0 ∧
      (frameFreshSparsePhase T).data.order ∣
        DeterminantalFactor.lastInvariantFactor A ∧
      (frameFreshSparsePhase T).data.order ≤ BetaExists.betaOf r ∧
      BetaExists.betaOf r ≤ BetaExists.betaOf n := by
  let F := frameFreshSparsePhase T
  letI : Nonempty (Fin F.basis.rank) := ⟨⟨0, by have := F.rank_pos; omega⟩⟩
  exact ⟨F.basis.rank, F.data.minor, fresh_basis_rank_eq_source_affineRank T,
    F.rank_pos, F.rank_le_six, F.minor_isZeroOne, F.data.minor_nonsingular,
    PaperSmithFactor.sparsePivot_order_dvd_lastInvariantFactor F,
    BetaAtPivotRank.FreshSparsePhase.order_le_betaOf_rank F,
    BetaAtPivotRank.FreshSparsePhase.betaOf_rank_le_betaOf F⟩

/-- Recovering the original class after both normalizations retains the
bound at the original support's affine rank. -/
theorem boundedClass_at_source_affineRank {q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    BoundedClassPower.BoundedClass
      (BetaExists.betaOf (supportAffineRank (G.eigenFrame.vec 0)))
      (exactCodeProjector C) G.intrinsicClass :=
  BoundedRepresentationProof.boundedClass_of_twoFiber G T
    (fresh_order_le_betaOf_source_affineRank T)
    (automaticFreshGenerator_sameProjective_normalizedFinite T)

/-- A primitive lift of the same source class obeys the sharp affine-rank
cutoff.  The modulus and the intrinsic class belong to this one lift. -/
theorem primitiveLift_at_source_affineRank {q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    ∃ q' : ℕ, 0 < q' ∧ HasPrimitiveLift C G.intrinsicClass q' ∧
      orderOf G.intrinsicClass ∣ q' ∧
      q' ≤ BetaExists.betaOf (supportAffineRank (G.eigenFrame.vec 0)) ∧
      BetaExists.betaOf (supportAffineRank (G.eigenFrame.vec 0)) ≤ BetaExists.betaOf n := by
  obtain ⟨q', hpos, hbound, hlift⟩ :=
    QMinBound.exists_primitiveLift_le_of_boundedClass (boundedClass_at_source_affineRank G T)
  exact ⟨q', hpos, hlift, orderOf_dvd_of_hasPrimitiveLift hlift, hbound,
    BetaAtPivotRank.betaOf_mono (supportAffineRank_le _)⟩

/-- The real-gate eigenframe associated with a finite generator remains an
eigenframe of any real diagonal operation projectively equal to it. -/
theorem eigenframe_of_sameProjective {d q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) (theta : Fin n → ℝ)
    (h : CodeSpec.SameProjectiveOnCode C.frame
      (RankTwoGlobal.finiteGateEnd G.zeta G.angle)
      (PhaseSectorBridge.realGateEnd theta)) :
    ∃ eigenvalue : Fin 2 → ℂ, eigenvalue 0 ≠ eigenvalue 1 ∧
      ∀ k, RealGate.realGate theta (G.eigenFrame.vec k)
        = fun s => eigenvalue k * G.eigenFrame.vec k s := by
  obtain ⟨lam, hlam, hact⟩ := h
  refine ⟨fun k => G.eigenvalue k / lam, ?_, ?_⟩
  · intro heq
    apply G.projectively_nontrivial
    exact (div_left_inj' hlam).1 heq
  · intro k
    have hmem : G.eigenFrame.vec k ∈ CodeSpec.codeSpan C.frame := by
      rw [G.span_eq]
      exact Submodule.subset_span (Set.mem_range_self k)
    have heq := hact (G.eigenFrame.vec k) hmem
    change Gate.gate G.zeta G.angle (G.eigenFrame.vec k)
      = lam • RealGate.realGate theta (G.eigenFrame.vec k) at heq
    rw [G.eigen k] at heq
    funext s
    have hs := congrFun heq s
    change G.eigenvalue k * G.eigenFrame.vec k s
      = lam * RealGate.realGate theta (G.eigenFrame.vec k) s at hs
    apply (mul_left_cancel₀ hlam)
    rw [← hs]
    field_simp

/-- The sharp affine-rank lift bound for a prescribed nontrivial diagonal
class at arbitrary length and target distance at least three.

The displayed orthonormal frame is an eigenframe of the original real gate,
spans the original code, and retains its full target distance.  Its two actual
supports have the same real affine rank, and the primitive lift represents
the original class itself. -/
theorem d3_bound_same_class_at_affineRank {d : ℕ}
    (C : CodeSpec.ExactCode n 2 d) (hd : 3 ≤ d)
    (v : diagonalSymmetryGroup (exactCodeProjector C)) (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (hg : intrinsicClass (exactCodeProjector C) v ≠ 1) :
    ∃ (F : CodeSpec.OrthonormalFrame n 2) (eigenvalue : Fin 2 → ℂ) (q : ℕ),
      CodeSpec.codeSpan C.frame = CodeSpec.codeSpan F ∧
      SS.HasDistance F.vec d ∧ eigenvalue 0 ≠ eigenvalue 1 ∧
      (∀ k, RealGate.realGate theta (F.vec k)
        = fun s => eigenvalue k * F.vec k s) ∧
      supportAffineRank (F.vec 0) = supportAffineRank (F.vec 1) ∧
      HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q ∧
      orderOf (intrinsicClass (exactCodeProjector C) v) ∣ q ∧
      2 ≤ q ∧ q ≤ BetaExists.betaOf (supportAffineRank (F.vec 0)) ∧
      BetaExists.betaOf (supportAffineRank (F.vec 0)) ≤ BetaExists.betaOf n := by
  let C3 := SSLPCompleteness.weakenDistance hd C
  have hpres3 : CodeSpec.CodePreserving C3.frame (PhaseSectorBridge.realGateEnd theta) :=
    hpres
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C3 (v : LocalPhase n) v.2 theta hexp hg
  letI : NeZero (rationalLift C3 GeneralFiniteness.two_le_three theta hpres3).order :=
    ⟨(rationalLift C3 GeneralFiniteness.two_le_three theta hpres3).order_pos.ne'⟩
  let G := finiteGenerator C3 GeneralFiniteness.two_le_three theta hpres3 hnt
  have hclass : G.intrinsicClass = intrinsicClass (exactCodeProjector C) v :=
    GeneralFiniteness.intrinsicClass_finiteGenerator C3 v theta hexp hpres3 hnt
  obtain ⟨q, hqpos, hlift, hdvd, hbound, hbetan⟩ :=
    primitiveLift_at_source_affineRank G (canonicalTwoFiber G)
  rw [hclass] at hlift hdvd
  have hsame : CodeSpec.SameProjectiveOnCode C3.frame
      (RankTwoGlobal.finiteGateEnd G.zeta G.angle)
      (PhaseSectorBridge.realGateEnd theta) :=
    finiteGenerator_sameProjective C3 GeneralFiniteness.two_le_three theta hpres3 hnt
  obtain ⟨ev, hev, heigen⟩ := eigenframe_of_sameProjective G theta hsame
  have hdist : SS.HasDistance G.eigenFrame.vec d :=
    CodeSpec.hasDistance_of_codeSpan_eq C.frame G.eigenFrame G.span_eq C.hasDistance
  have hrank := supportAffineRank_eq_of_commonAffineSpan
    (CodeAffineSpanBridge.commonAffineSpan_of_exactCodeFrame C G.eigenFrame G.span_eq hd)
  have hm0 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    exact hqpos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  have hm1 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 1 := by
    intro h1
    exact hg (orderOf_eq_one_iff.mp h1)
  have hmle := Nat.le_of_dvd hqpos hdvd
  exact ⟨G.eigenFrame, ev, q, G.span_eq, hdist, hev, heigen, hrank,
    hlift, hdvd, by omega, hbound, hbetan⟩

end MainTheory.D3AffineRankBound
