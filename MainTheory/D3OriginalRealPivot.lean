import MainTheory.D3AffineRankBound
import MainTheory.D3BoundedNormalForm
import MainTheory.D3FreshGenerator
import MainTheory.RealXNormalization
import MainTheory.SparseSmithDisplays

/-! The sparse pivot belongs to the prescribed real diagonal action. -/
namespace MainTheory.D3OriginalRealPivot

open MainTheory MainTheory.ClassificationLevels MainTheory.SectionTwoGeneral
open MainTheory.D3NormalizedFreshPhase MainTheory.D3FreshSparseAssembly
open MainTheory.D3BoundedNormalForm MainTheory.RealSupportAffineRank

noncomputable section
set_option maxHeartbeats 16000000
variable {n : ℕ}

theorem shifted_eigen (theta : Fin n → ℝ) (x0 : SS.BitString n)
    (psi : SS.State n ℂ) (lam : ℂ)
    (he : RealGate.realGate theta psi = fun x => lam * psi x) :
    RealGate.realGate (RealXNormalization.flipAngle theta x0)
      (fun x => psi (SS.bxor x x0)) =
        fun x => (lam / PhaseSectorFull.phaseExp (RealGate.angle theta x0)) *
          psi (SS.bxor x x0) := by
  funext x
  have hx := congrFun he (SS.bxor x x0)
  change PhaseSectorFull.phaseExp (RealGate.angle theta (SS.bxor x x0)) *
    psi (SS.bxor x x0) = _ at hx
  rw [RealXNormalization.angle_bxor, RealXNormalization.phaseExp_add] at hx
  change PhaseSectorFull.phaseExp
    (RealGate.angle (RealXNormalization.flipAngle theta x0) x) * _ = _
  apply (mul_left_cancel₀
    (RealXNormalization.phaseExp_ne_zero (RealGate.angle theta x0)))
  field_simp [RealXNormalization.phaseExp_ne_zero]
  linear_combination hx

/-- One original real eigenframe produces one fresh sparse phase and one
finite generator on the original code. The denominator, pivot and class
agreement all refer to that same construction. -/
theorem for_eigenframe {q : ℕ} [NeZero q]
    (C : CodeSpec.ExactCode n 2 3)
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (theta : Fin n → ℝ) (ev : Fin 2 → ℂ) (hev : ev 0 ≠ ev 1)
    (he : ∀ k, RealGate.realGate theta (G.eigenFrame.vec k) =
      fun x => ev k * G.eigenFrame.vec k x) :
    ∃ T : RankTwoGlobal.TwoFiberCertificate G,
      ∃ F : FreshSparsePhase (normalizedState T 0) (normalizedState T 1)
          (RealXNormalization.flipAngle theta T.x0),
      letI : NeZero F.data.order := ⟨F.data.order_pos.ne'⟩
      ∃ Gb : RankTwoGlobal.FiniteGeneratorResolution C F.data.order,
        Gb.eigenFrame = G.eigenFrame ∧
        CodeSpec.SameProjectiveOnCode C.frame
          (RankTwoGlobal.finiteGateEnd Gb.zeta Gb.angle)
          (PhaseSectorBridge.realGateEnd theta) ∧
        F.basis.rank = supportAffineRank (G.eigenFrame.vec 0) ∧
        F.data.order ∣ DeterminantalFactor.lastInvariantFactor F.data.minor ∧
        2 ≤ F.data.order ∧
        F.data.order ≤ BetaExists.betaOf F.basis.rank ∧
        BetaExists.betaOf F.basis.rank ≤ BetaExists.betaOf n := by
  let T := canonicalTwoFiber G
  let c0 := PhaseSectorFull.phaseExp (RealGate.angle theta T.x0)
  have hc0 : c0 ≠ 0 := RealXNormalization.phaseExp_ne_zero _
  have hc0eq : c0 = ev 0 :=
    RealGate.exp_eq_of_eigen theta (G.eigenFrame.vec 0) (ev 0)
      (he 0) T.x0 T.base_supported
  let thetaX := RealXNormalization.flipAngle theta T.x0
  let evX : Fin 2 → ℂ := fun k => ev k / c0
  have heX (k : Fin 2) : RealGate.realGate thetaX
      ((normalizedFrame T).vec k) =
        fun x => evX k * (normalizedFrame T).vec k x :=
    shifted_eigen theta T.x0 (G.eigenFrame.vec k) (ev k) (he k)
  have he0 : RealGate.realGate thetaX (normalizedState T 0) =
      normalizedState T 0 := by
    simpa only [evX, hc0eq, div_self (hc0eq ▸ hc0), one_mul] using heX 0
  let F := freshSparsePhase T thetaX he0
  have hevX : evX 0 ≠ evX 1 := fun h => hev ((div_left_inj' hc0).1 h)
  letI : NeZero F.data.order := ⟨F.data.order_pos.ne'⟩
  let GX := D3FreshGenerator.ofFreshSparsePhase (C := normalizedCode T)
    thetaX (normalizedFrame T)
    rfl evX heX hevX F
  let Gb := FlipSemanticTransport.flipFiniteGeneratorResolution (C' := C)
    GX T.x0 (codeSpan_shift_of_span T _ GX.span_eq)
  have hframe : Gb.eigenFrame = G.eigenFrame := shiftFrame_normalizedFrame T
  let cF := Cyclic.chi GX.zeta (SS.weight GX.angle T.x0)
  have hcF : cF ≠ 0 := FlipSemanticTransport.chi_ne_zero GX.zeta GX.primitiveRoot _
  have hs : CodeSpec.SameProjectiveOnCode C.frame
      (RankTwoGlobal.finiteGateEnd Gb.zeta Gb.angle)
      (PhaseSectorBridge.realGateEnd theta) := by
    have hsF : CodeSpec.SameProjectiveOnCode G.eigenFrame
        (RankTwoGlobal.finiteGateEnd Gb.zeta Gb.angle)
        (PhaseSectorBridge.realGateEnd theta) := by
      apply (CodeSpec.sameProjectiveOnCode_iff_frame _ _ _).2
      refine ⟨(c0 * cF)⁻¹, inv_ne_zero (mul_ne_zero hc0 hcF), ?_⟩
      intro k
      have hk := Gb.eigen k
      rw [hframe] at hk
      change Gate.gate Gb.zeta Gb.angle (G.eigenFrame.vec k) = _
      rw [hk, show PhaseSectorBridge.realGateEnd theta (G.eigenFrame.vec k) =
        RealGate.realGate theta (G.eigenFrame.vec k) from rfl, he k]
      funext x
      change (ev k / c0 / cF) * G.eigenFrame.vec k x =
        (c0 * cF)⁻¹ * (ev k * G.eigenFrame.vec k x)
      field_simp
    unfold CodeSpec.SameProjectiveOnCode at hsF ⊢
    rw [G.span_eq]
    exact hsF
  have hr : F.basis.rank = supportAffineRank (G.eigenFrame.vec 0) := by
    rw [RealSupportAffineRank.SupportedBitBasis.rank_eq_supportAffineRank
      F.basis (D3AffineRankBound.normalized_zero_supported T)]
    exact D3AffineRankBound.normalized_supportAffineRank T 0
  let TG := canonicalTwoFiber Gb
  have htwo : 2 ≤ F.data.order := TG.two_le_physicalOrder
  haveI : Nonempty (Fin F.basis.rank) := ⟨⟨0, by have := F.rank_pos; omega⟩⟩
  exact ⟨T, F, Gb, hframe, hs, hr,
    PaperSmithFactor.sparsePivot_order_dvd_lastInvariantFactor F,
    htwo, BetaAtPivotRank.FreshSparsePhase.order_le_betaOf_rank F,
    BetaAtPivotRank.FreshSparsePhase.betaOf_rank_le_betaOf F⟩

/-- Projective agreement with the prescribed real operation identifies its
class, without taking a coprime power of that operation. -/
theorem intrinsicClass_of_sameProjective {q : ℕ} [NeZero q]
    (C : CodeSpec.ExactCode n 2 3)
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (v : diagonalSymmetryGroup (GlobalClassificationBridge.exactCodeProjector C))
    (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (hs : CodeSpec.SameProjectiveOnCode C.frame
      (RankTwoGlobal.finiteGateEnd G.zeta G.angle)
      (PhaseSectorBridge.realGateEnd theta)) :
    G.intrinsicClass = intrinsicClass (GlobalClassificationBridge.exactCodeProjector C) v := by
  rw [BoundedRepresentationProof.intrinsicClass_eq_phaseOfAngle G]
  obtain ⟨lam, hlam, hact⟩ := hs
  refine IntrinsicClassBridge.intrinsicClass_eq_of_sameProjective
    (GlobalClassificationBridge.exactCodeProjector C) _ _ lam hlam (fun phi hphi => ?_)
  have hmem := (GlobalClassificationBridge.inProjectorRange_ofFrame_iff C.frame phi).1 hphi
  have hthis := hact phi hmem
  simp only [RankTwoGlobal.finiteGateEnd, LinearMap.coe_mk, AddHom.coe_mk] at hthis
  rw [FiniteGateAsPhase.gate_eq_diagonalAction G.zeta G.primitiveRoot.pow_eq_one G.angle phi,
    SymmetryToEntrance.realGateEnd_eq_diagonalAction (v : LocalPhase n) theta hexp phi] at hthis
  exact hthis

/-- The original real action, its actual support rank, and its selected binary
minor satisfy the entire sharp divisibility chain in one construction. -/
theorem full_sparse_bound {d : ℕ}
    (C : CodeSpec.ExactCode n 2 d) (hd : 3 ≤ d)
    (v : diagonalSymmetryGroup (GlobalClassificationBridge.exactCodeProjector C))
    (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (hg : intrinsicClass (GlobalClassificationBridge.exactCodeProjector C) v ≠ 1) :
    let C3 := SSLPCompleteness.weakenDistance hd C
    ∃ (q : ℕ) (_ : NeZero q) (Gb : RankTwoGlobal.FiniteGeneratorResolution C3 q)
      (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ),
      SS.HasDistance Gb.eigenFrame.vec d ∧
      CodeSpec.SameProjectiveOnCode C.frame (RankTwoGlobal.finiteGateEnd Gb.zeta Gb.angle)
        (PhaseSectorBridge.realGateEnd theta) ∧
      Gb.intrinsicClass = intrinsicClass (GlobalClassificationBridge.exactCodeProjector C) v ∧
      r = supportAffineRank (Gb.eigenFrame.vec 0) ∧
      supportAffineRank (Gb.eigenFrame.vec 0) = supportAffineRank (Gb.eigenFrame.vec 1) ∧
      1 ≤ r ∧ r ≤ n ∧ BinaryBeta.IsZeroOne A ∧ A.det ≠ 0 ∧
      orderOf (intrinsicClass (GlobalClassificationBridge.exactCodeProjector C) v) ∣ q ∧
      q ∣ DeterminantalFactor.lastInvariantFactor A ∧
      2 ≤ q ∧ q ≤ DeterminantalFactor.lastInvariantFactor A ∧
      DeterminantalFactor.lastInvariantFactor A ≤ BetaExists.betaOf r ∧
      BetaExists.betaOf r ≤ BetaExists.betaOf n := by
  let C3 := SSLPCompleteness.weakenDistance hd C
  have hpres3 : CodeSpec.CodePreserving C3.frame (PhaseSectorBridge.realGateEnd theta) := hpres
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C3 (v : LocalPhase n) v.2 theta hexp hg
  letI : NeZero (rationalLift C3 GeneralFiniteness.two_le_three theta hpres3).order :=
    ⟨(rationalLift C3 GeneralFiniteness.two_le_three theta hpres3).order_pos.ne'⟩
  let G := finiteGenerator C3 GeneralFiniteness.two_le_three theta hpres3 hnt
  have hs : CodeSpec.SameProjectiveOnCode C3.frame
      (RankTwoGlobal.finiteGateEnd G.zeta G.angle) (PhaseSectorBridge.realGateEnd theta) :=
    finiteGenerator_sameProjective C3 GeneralFiniteness.two_le_three theta hpres3 hnt
  obtain ⟨ev, hev, he⟩ := D3AffineRankBound.eigenframe_of_sameProjective G theta hs
  obtain ⟨T, F, Gb, hframe, hsame, hr, hdvd, htwo, _, hbetan⟩ :=
    for_eigenframe C3 G theta ev hev he
  letI : NeZero F.data.order := ⟨F.data.order_pos.ne'⟩
  haveI : Nonempty (Fin F.basis.rank) := ⟨⟨0, by have := F.rank_pos; omega⟩⟩
  have hclass : Gb.intrinsicClass = intrinsicClass
      (GlobalClassificationBridge.exactCodeProjector C) v :=
    intrinsicClass_of_sameProjective C3 Gb v theta hexp hsame
  have hm := (canonicalTwoFiber Gb).logicalOrder_dvd_physical
  rw [← (canonicalTwoFiber Gb).intrinsic_order_eq, hclass] at hm
  have hlast : DeterminantalFactor.lastInvariantFactor F.data.minor =
      SharpClearing.inverseDenominator F.data.minor :=
    (DeterminantalFactor.inverseDenominator_eq_det_div_cofactorGcd
      F.data.minor F.data.minor_nonsingular).symm
  have hlastpos : 0 < DeterminantalFactor.lastInvariantFactor F.data.minor := by
    rw [hlast]; exact SharpClearing.inverseDenominator_pos _
  have hlastbound : DeterminantalFactor.lastInvariantFactor F.data.minor ≤
      BetaExists.betaOf F.basis.rank := by
    rw [hlast]
    exact BetaExists.betaBound_betaOf F.basis.rank F.basis.rank F.rank_pos le_rfl
      F.data.minor F.minor_isZeroOne F.data.minor_nonsingular
  have hdist : SS.HasDistance Gb.eigenFrame.vec d :=
    CodeSpec.hasDistance_of_codeSpan_eq C.frame Gb.eigenFrame Gb.span_eq C.hasDistance
  have hrank := supportAffineRank_eq_of_commonAffineSpan
    (CodeAffineSpanBridge.commonAffineSpan_of_exactCodeFrame C Gb.eigenFrame Gb.span_eq hd)
  refine ⟨F.data.order, inferInstance, Gb, F.basis.rank, F.data.minor,
    hdist, hsame, hclass, ?_, hrank, F.rank_pos, F.rank_le_six,
    F.minor_isZeroOne, F.data.minor_nonsingular, hm, hdvd, htwo,
    Nat.le_of_dvd hlastpos hdvd, hlastbound, hbetan⟩
  rw [hframe]
  exact hr

end
end MainTheory.D3OriginalRealPivot
