import MainTheory.BoundedClassPower
import MainTheory.UndoNormalization
import MainTheory.PhaseTranscription
import MainTheory.SameProjectiveClass
import MainTheory.D3SpectralOuterEntrance
import MainTheory.SymmetryToEntrance
import MainTheory.LocalPhaseAngle

/-!
# The bounded representative on the original code

`D3SpectralOuterEntrance` bounds the fresh modulus by nine, but on the
*normalized* code: the fresh generator is compared with the local-`X`- and
unit-power-normalized operation, and that file is explicit that this is "not
asserted to be the identical group element on the original code".

This file performs that transport.  Given a finite generator `G` on `C` and a
two-fibre certificate `T`, the fresh generator's projective agreement on the
normalized code becomes a bounded representative of `G`'s own intrinsic class
on `C`, in three moves:

* `SameProjectiveClass` converts the projective agreement into an equality of
  intrinsic classes on the normalized frame;
* `NormalizationIsShift` identifies that frame as `shiftFrame G.eigenFrame T.x0`,
  so `IntrinsicTransport.intrinsicClass_flip_eq` carries the equality back to
  `G.eigenFrame` and `intrinsicClass_congr` from there to `C.frame`;
* `UndoNormalization` evaluates the transported right-hand side as the
  `T.unit`-th power of `G`'s own phase, and `BoundedClass.of_pow_coprime`
  removes that exponent.

The left-hand side stays bounded throughout: conjugation by a local `X` only
flips the angle vector, leaving the modulus -- and hence the label -- alone.
-/

namespace MainTheory.BoundedRepresentationProof

variable {n : ℕ}

open MainTheory.ClassificationLevels
open MainTheory.FiniteGateAsPhase
open MainTheory.BoundedClassPower
open MainTheory.LocalPhaseConjugation
open MainTheory.IntrinsicTransport
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.D3NormalizedFreshPhase
open MainTheory.GlobalClassificationBridge

variable {C : CodeSpec.ExactCode n 2 3} {q : ℕ} [NeZero q]

/-! ## Memberships -/

/-- A resolved generator's phase, in the `phaseOfAngle` transcription, is a
diagonal symmetry of the code it spans. -/
theorem mem_symmetryGroup_phaseOfAngle_code
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    phaseOfAngle G.zeta G.primitiveRoot.pow_eq_one G.angle ∈
      diagonalSymmetryGroup (exactCodeProjector C) := by
  rw [PhaseTranscription.phaseOfAngle_eq_finiteLocalPhase]
  exact G.intrinsicSymmetry.2

/-- The same membership stated on the generator's own eigenframe. -/
theorem mem_symmetryGroup_phaseOfAngle
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    phaseOfAngle G.zeta G.primitiveRoot.pow_eq_one G.angle ∈
      diagonalSymmetryGroup (CodeProjector.ofFrame G.eigenFrame) := by
  rw [← diagonalSymmetryGroup_congr (F := C.frame) G.span_eq]
  exact mem_symmetryGroup_phaseOfAngle_code G

/-- The class of a resolved generator is the class of its `phaseOfAngle`
transcription. -/
theorem intrinsicClass_eq_phaseOfAngle
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    G.intrinsicClass
      = intrinsicClass (exactCodeProjector C)
          ⟨phaseOfAngle G.zeta G.primitiveRoot.pow_eq_one G.angle,
            mem_symmetryGroup_phaseOfAngle_code G⟩ := by
  have hcoe : (G.intrinsicSymmetry : LocalPhase n)
      = finiteLocalPhase G.zeta G.primitiveRoot G.angle := rfl
  refine congrArg (intrinsicClass (exactCodeProjector C)) (Subtype.ext ?_)
  rw [hcoe]
  exact (PhaseTranscription.phaseOfAngle_eq_finiteLocalPhase _ _ _).symm

/-- The intrinsic class of a resolved generator is killed by its modulus. -/
theorem intrinsicClass_pow_order
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    G.intrinsicClass ^ q = 1 := by
  show (intrinsicClass (exactCodeProjector C) G.intrinsicSymmetry) ^ q = 1
  rw [intrinsicClass, ← QuotientGroup.mk_pow]
  have hone : G.intrinsicSymmetry ^ q = 1 := by
    refine Subtype.ext ?_
    simpa using
      GlobalClassificationBridge.finiteLocalPhase_pow_order
        G.zeta G.primitiveRoot G.angle
  rw [hone]
  rfl

/-! ## The core transport -/

/-- **A bounded representative on the normalized code is a bounded
representative on the original one.**

The hypothesis is exactly the second conjunct of
`D3SpectralOuterEntrance.ResolutionOuterStatement` together with the fresh
order bound from its third conjunct. -/
theorem boundedClass_of_twoFiber
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (T : RankTwoGlobal.TwoFiberCertificate G)
    {B : ℕ} (hle : (frameFreshSparsePhase T).data.order ≤ B)
    (h2 : CodeSpec.SameProjectiveOnCode (normalizedCode T).frame
      (freshFiniteGateEnd T)
      (RankTwoGlobal.finiteGateEnd G.zeta
        (SixQubitSemanticEntrance.normalizedFiniteAngle (G := G) T))) :
    BoundedClass B (exactCodeProjector C) G.intrinsicClass := by
  letI : NeZero (frameFreshSparsePhase T).data.order := frameFreshOrderNeZero T
  have hz : G.zeta ^ q = 1 := G.primitiveRoot.pow_eq_one
  have hzF : (automaticFreshGenerator T).zeta
      ^ (frameFreshSparsePhase T).data.order = 1 :=
    (automaticFreshGenerator T).primitiveRoot.pow_eq_one
  have hshift : (normalizedCode T).frame = shiftFrame G.eigenFrame T.x0 :=
    NormalizationIsShift.normalizedFrame_eq_shiftFrame T
  set c := UndoNormalization.unitNat T.unit with hcdef
  -- the generator's own phase, and its unit power, on the eigenframe
  have hmemG : phaseOfAngle G.zeta hz G.angle ∈
      diagonalSymmetryGroup (CodeProjector.ofFrame G.eigenFrame) :=
    mem_symmetryGroup_phaseOfAngle G
  have hmemPow : (phaseOfAngle G.zeta hz G.angle) ^ c ∈
      diagonalSymmetryGroup (CodeProjector.ofFrame G.eigenFrame) :=
    pow_mem hmemG c
  -- undoing the normalization
  have hundo : flipPhase (phaseOfAngle G.zeta hz
        (SixQubitSemanticEntrance.normalizedFiniteAngle (G := G) T)) T.x0
      = (phaseOfAngle G.zeta hz G.angle) ^ c :=
    UndoNormalization.flipPhase_phaseOfAngle_normalized
      G.zeta hz G.angle T.x0 T.unit
  have hback : phaseOfAngle G.zeta hz
        (SixQubitSemanticEntrance.normalizedFiniteAngle (G := G) T)
      = flipPhase ((phaseOfAngle G.zeta hz G.angle) ^ c) T.x0 := by
    rw [← hundo, flipPhase_flipPhase]
  have hmemNorm : phaseOfAngle G.zeta hz
        (SixQubitSemanticEntrance.normalizedFiniteAngle (G := G) T) ∈
      diagonalSymmetryGroup
        (CodeProjector.ofFrame (shiftFrame G.eigenFrame T.x0)) := by
    rw [hback]
    exact mem_symmetryGroup_flip' G.eigenFrame T.x0 _ hmemPow
  have hmemFresh : phaseOfAngle (automaticFreshGenerator T).zeta hzF
        (automaticFreshGenerator T).angle ∈
      diagonalSymmetryGroup
        (CodeProjector.ofFrame (shiftFrame G.eigenFrame T.x0)) := by
    rw [← hshift]
    exact mem_symmetryGroup_phaseOfAngle_code (automaticFreshGenerator T)
  -- projective agreement becomes class equality on the normalized frame
  have hcls := SameProjectiveClass.intrinsicClass_eq_of_sameProjective
    (shiftFrame G.eigenFrame T.x0)
    (automaticFreshGenerator T).zeta hzF (automaticFreshGenerator T).angle
    G.zeta hz (SixQubitSemanticEntrance.normalizedFiniteAngle (G := G) T)
    hmemFresh hmemNorm (by rw [← hshift]; exact h2)
  -- transport back across the local X
  have hflip := intrinsicClass_flip_eq G.eigenFrame T.x0
    ⟨_, hmemFresh⟩ ⟨_, hmemNorm⟩ hcls
  -- put the fresh side in labelled form
  have hfreshFlip :
      flipPhase (phaseOfAngle (automaticFreshGenerator T).zeta hzF
          (automaticFreshGenerator T).angle) T.x0
        = phaseOfAngle (automaticFreshGenerator T).zeta hzF
            (MainTheory.Normalize.flip (automaticFreshGenerator T).angle T.x0) :=
    flipPhase_phaseOfAngle _ _ _ _
  have hmemL : phaseOfAngle (automaticFreshGenerator T).zeta hzF
        (MainTheory.Normalize.flip (automaticFreshGenerator T).angle T.x0) ∈
      diagonalSymmetryGroup (CodeProjector.ofFrame G.eigenFrame) := by
    rw [← hfreshFlip]
    exact mem_symmetryGroup_flip G.eigenFrame T.x0 _ hmemFresh
  have hkey :
      intrinsicClass (CodeProjector.ofFrame G.eigenFrame)
          ⟨phaseOfAngle (automaticFreshGenerator T).zeta hzF
            (MainTheory.Normalize.flip (automaticFreshGenerator T).angle T.x0),
            hmemL⟩
        = intrinsicClass (CodeProjector.ofFrame G.eigenFrame)
          ⟨(phaseOfAngle G.zeta hz G.angle) ^ c, hmemPow⟩ :=
    (intrinsicClass_congr_val hfreshFlip.symm).trans
      (hflip.trans (intrinsicClass_congr_val hundo))
  -- move both sides to the code's own frame
  have hmemLC : phaseOfAngle (automaticFreshGenerator T).zeta hzF
        (MainTheory.Normalize.flip (automaticFreshGenerator T).angle T.x0) ∈
      diagonalSymmetryGroup (exactCodeProjector C) := by
    rw [diagonalSymmetryGroup_congr (F := C.frame) G.span_eq]
    exact hmemL
  have hmemPowC : (phaseOfAngle G.zeta hz G.angle) ^ c ∈
      diagonalSymmetryGroup (exactCodeProjector C) := by
    rw [diagonalSymmetryGroup_congr (F := C.frame) G.span_eq]
    exact hmemPow
  have hkeyC := intrinsicClass_congr G.span_eq.symm _ _
    ⟨_, hmemLC⟩ ⟨_, hmemPowC⟩ rfl rfl hkey
  -- the right-hand side is the generator's class raised to the unit power
  have hpowclass :
      intrinsicClass (exactCodeProjector C)
          ⟨(phaseOfAngle G.zeta hz G.angle) ^ c, hmemPowC⟩
        = G.intrinsicClass ^ c := by
    rw [intrinsicClass_eq_phaseOfAngle G, intrinsicClass, intrinsicClass,
      ← QuotientGroup.mk_pow]
    rfl
  -- the left-hand side is a labelled gate
  obtain ⟨lbl, hlbl⟩ := exists_label_of_phaseOfAngle_le hle
    (automaticFreshGenerator T).zeta hzF
    (MainTheory.Normalize.flip (automaticFreshGenerator T).angle T.x0)
  have hb : BoundedClass B (exactCodeProjector C) (G.intrinsicClass ^ c) := by
    refine ⟨lbl, ⟨_, hmemLC⟩, ?_, hlbl.symm⟩
    rw [hkeyC, hpowclass]
  exact BoundedClass.of_pow_coprime (Nat.pos_of_ne_zero (NeZero.ne q))
    (intrinsicClass_pow_order G) (UndoNormalization.coprime_unitNat T.unit) hb

/-! ## The nontrivial branch -/

open MainTheory.D3SpectralOuterEntrance in
/-- **Every nontrivial class has a bounded representative.**

The spectral extraction principle is the only unproved semantic premise, the
same one `D3SpectralOuterEntrance` exposes; the modulus bound is the certified
`BetaBound 6 9`. -/
theorem boundedClass_of_class_ne_one
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : CodeSpec.ExactCode 6 2 3)
    (v : LocalPhase 6)
    (hv : v ∈ diagonalSymmetryGroup (exactCodeProjector C))
    (theta : Fin 6 → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = ((v j : ℂ)))
    (hne : intrinsicClass (exactCodeProjector C) ⟨v, hv⟩ ≠ 1) :
    BoundedClass 9 (exactCodeProjector C)
      (intrinsicClass (exactCodeProjector C) ⟨v, hv⟩) := by
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame v hv theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C v hv theta hexp hne
  obtain ⟨R, hc1, hc2, _⟩ :=
    arbitrary_code_enters_outer_from_spectral spectral betaSix C theta hpres hnt
  letI : NeZero (rationalLiftOfResolution R).order := resolutionOrderNeZero R
  set G := finiteGeneratorOfResolution R hnt with hGdef
  set T := twoFiberOfResolution R hnt with hTdef
  have hz : G.zeta ^ (rationalLiftOfResolution R).order = 1 :=
    G.primitiveRoot.pow_eq_one
  -- the generator's class is the class we started from
  have hGu : G.intrinsicClass
      = intrinsicClass (exactCodeProjector C) ⟨v, hv⟩ := by
    rw [intrinsicClass_eq_phaseOfAngle G]
    obtain ⟨lam, hlam, hact⟩ := hc1
    refine IntrinsicClassBridge.intrinsicClass_eq_of_sameProjective
      (exactCodeProjector C) _ _ lam hlam (fun phi hphi => ?_)
    have hmem : phi ∈ CodeSpec.codeSpan C.frame :=
      (inProjectorRange_ofFrame_iff C.frame phi).1 hphi
    have hthis := hact phi hmem
    simp only [resolutionFiniteGateEnd,
      D3RationalLiftFiniteGenerator.finiteGeneratorOfLiftEnd,
      RankTwoGlobal.finiteGateEnd, LinearMap.coe_mk, AddHom.coe_mk] at hthis
    rw [show D3RationalLiftFiniteGenerator.finiteGeneratorOfLift R
        (rationalLiftOfResolution R) hnt = G from rfl] at hthis
    rw [gate_eq_diagonalAction G.zeta hz G.angle phi,
      SymmetryToEntrance.realGateEnd_eq_diagonalAction v theta hexp phi] at hthis
    exact hthis
  rw [← hGu]
  refine boundedClass_of_twoFiber G T (B := 9)
    (automaticFreshGenerator_order_le_nine betaSix T) ?_
  exact hc2

/-! ## The obligation, discharged -/

/-- **`HasBoundedRepresentation` holds for every exact six-qubit code.**

The trivial class is handled by `SymmetryToEntrance.exists_label_of_class_one`;
every other class goes through the entrance and the transport above.  The only
remaining premise is the spectral extraction principle. -/
theorem hasBoundedRepresentation
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : CodeSpec.ExactCode 6 2 3) :
    BoundedRepresentation.HasBoundedRepresentation 9 C := by
  intro g
  by_cases hg : g = 1
  · subst hg
    exact SymmetryToEntrance.exists_label_of_class_one C (by norm_num)
  · obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨theta, hexp⟩ :=
      LocalPhaseAngle.exists_angleVector (u : LocalPhase 6)
    exact boundedClass_of_class_ne_one spectral betaSix C
      (u : LocalPhase 6) u.2 theta hexp hg

/-- The intrinsic projective diagonal group of an exact six-qubit code is
finite. -/
theorem finite_intrinsicGroup
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : CodeSpec.ExactCode 6 2 3) :
    Finite (GlobalClassificationBridge.IntrinsicGroup C) :=
  BoundedRepresentation.finite_of_representation
    (hasBoundedRepresentation spectral betaSix C)

/-- The certified inputs to the finite-cyclic classification, with the bounded
representation hypothesis discharged.  A faithful character is still supplied
by the caller; that is a separate interface, unrelated to the modulus bound. -/
noncomputable def intrinsicFiniteCyclicInputs
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : CodeSpec.ExactCode 6 2 3)
    (chi : GlobalClassificationBridge.IntrinsicGroup C →* ℂ)
    (hchi : Function.Injective chi) :
    GlobalClassificationBridge.IntrinsicFiniteCyclicInputs (B := 9) C :=
  BoundedRepresentation.inputsOfRepresentation
    (hasBoundedRepresentation spectral betaSix C) chi hchi

end MainTheory.BoundedRepresentationProof
