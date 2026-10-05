import QECC.DistanceThreeMatrixProvenance
import QECC.PhaseCoefficientTransport
import QECC.PauliTransport

namespace QECC

noncomputable section

namespace CodeProjector

variable {n d : ℕ} (C : CodeProjector n 2)

-- Port to Lean 4.27: generating the constructor injectivity theorems
-- (`mk.inj`, `mk.injEq`) for this dependent structure times out there, even
-- at ten times the default heartbeats; Lean 4.28 does it quickly. Nothing
-- in this development uses them, and any use would fail to compile.
set_option genInjectivity false in
/-- The complete abstract conclusion of the distance-three refinement in
Section III.C.  The two stored sectors are the actual phase sectors of the
source reduced representative.  `matrixSize_eq_r` records that the Smith
certificate is an `r × r` binary matrix, where `r` is their common real
affine dimension. -/
structure DistanceThreePhysicalOrderBoundConclusion
    (U : C.ProjectiveDiagonalGroup) where
  sourceRepresentative : ReducedDiagonalRepresentative n
  sourcePreserves : C.Preserves sourceRepresentative.phase
  sourceClass_eq :
    C.projectiveClassMap ⟨sourceRepresentative.phase, sourcePreserves⟩ = U
  firstSector : C.ActiveResidue sourceRepresentative.a
  secondSector : C.ActiveResidue sourceRepresentative.a
  sectors_ne : firstSector ≠ secondSector
  sectors_exhaust : ∀ b : C.ActiveResidue sourceRepresentative.a,
    b = firstSector ∨ b = secondSector
  affineSpan_eq :
    C.actualSectorAffineSpan sourceRepresentative.a firstSector =
      C.actualSectorAffineSpan sourceRepresentative.a secondSector
  r : ℕ
  r_eq_firstAffineDimension :
    r = C.actualSectorAffineDimension sourceRepresentative.a firstSector
  r_eq_secondAffineDimension :
    r = C.actualSectorAffineDimension sourceRepresentative.a secondSector
  r_pos : 1 ≤ r
  r_le : r ≤ n
  representative : ReducedDiagonalRepresentative n
  preserves : C.Preserves representative.phase
  class_eq : C.projectiveClassMap ⟨representative.phase, preserves⟩ = U
  matrixSize : ℕ
  matrixSize_eq_r : matrixSize = r
  binaryMatrix : NonsingularBinaryMatrix matrixSize
  normalizationOrigin : BitString n
  normalizationOrigin_mem : normalizationOrigin ∈
    C.actualSectorSupport sourceRepresentative.a firstSector
  pivotRows : Fin matrixSize ↪
    ((C.reindex (xorEquiv normalizationOrigin)).actualSectorSupport
      (xorCoefficient normalizationOrigin sourceRepresentative.a)
      (C.xorActiveResidueEquiv sourceRepresentative.a
        normalizationOrigin firstSector))
  pivotColumns : Fin matrixSize ↪ Fin n
  pivotRows_independent : LinearIndependent ℝ
    (fun i ↦ bitVector (pivotRows i).1)
  pivotRows_span_affineDirection :
    Submodule.span ℝ (Set.range fun i ↦ bitVector (pivotRows i).1) =
      ((C.reindex (xorEquiv normalizationOrigin)).actualSectorAffineSpan
        (xorCoefficient normalizationOrigin sourceRepresentative.a)
        (C.xorActiveResidueEquiv sourceRepresentative.a
          normalizationOrigin firstSector)).direction
  pivotRows_span_secondAffineDirection :
    Submodule.span ℝ (Set.range fun i ↦ bitVector (pivotRows i).1) =
      ((C.reindex (xorEquiv normalizationOrigin)).actualSectorAffineSpan
        (xorCoefficient normalizationOrigin sourceRepresentative.a)
        (C.xorActiveResidueEquiv sourceRepresentative.a
          normalizationOrigin secondSector)).direction
  binaryMatrix_eq_coordinateMinor : binaryMatrix.matrix =
    ((C.reindex (xorEquiv normalizationOrigin)).anchorActualSupportMatrix
      (xorCoefficient normalizationOrigin sourceRepresentative.a)
      (C.xorActiveResidueEquiv sourceRepresentative.a
        normalizationOrigin firstSector)).submatrix pivotRows pivotColumns
  projectiveOrder_ge_two : 2 ≤ addOrderOf U
  projectiveOrder_dvd : addOrderOf U ∣ representative.q
  projectiveOrder_le_physicalOrder : addOrderOf U ≤ representative.q
  physicalOrder_dvd_smith :
    representative.q ∣ binaryMatrix.finalSmithInvariant
  physicalOrder : orderOf (diagonalGate representative.phase) = representative.q
  physicalOrder_ge_two : 2 ≤ representative.q
  physicalOrder_le_smith :
    representative.q ≤ binaryMatrix.finalSmithInvariant
  smith_le_beta_r : binaryMatrix.finalSmithInvariant ≤ smithBeta r
  beta_r_le_beta_n : smithBeta r ≤ smithBeta n
  physicalOrder_le_beta_r : representative.q ≤ smithBeta r
  physicalOrder_le_beta_n : representative.q ≤ smithBeta n
  minimalPhysicalOrder_le_beta_r : C.minimalPhysicalOrder U ≤ smithBeta r
  minimalPhysicalOrder_le_beta_n : C.minimalPhysicalOrder U ≤ smithBeta n

/-- **Distance-three physical-order bound for rank-two codes.**

For every nonzero projective diagonal logical class of a rank-two code of
distance at least three, the two actual phase-sector supports of a reduced
source representative have the same real affine span.  If `r` is their
common affine dimension, then `1 ≤ r ≤ n`, and the same projective class has
a reduced physical representative of exact order `q` together with an
invertible binary `r × r` Smith certificate satisfying

`addOrderOf U ∣ q`, `q ∣ d_r`, and
`2 ≤ q ≤ d_r ≤ smithBeta r ≤ smithBeta n`.

The conclusion also records the corresponding bounds for the minimum
physical representative order.  No numerical value of `smithBeta` is used. -/
theorem distanceThree_physicalOrder_bound_of_representative
    (hd : C.HasDistanceAtLeast d) (hd3 : 3 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0)
    (R : ReducedDiagonalRepresentative n)
    (hRpres : C.Preserves R.phase)
    (hRclass : C.projectiveClassMap ⟨ R.phase, hRpres⟩ = U) :
    Nonempty {H : C.DistanceThreePhysicalOrderBoundConclusion U //
      H.sourceRepresentative = R} := by
  classical
  have hdTwo : C.HasDistanceAtLeast 2 := by
    intro p hp
    exact hd p (lt_of_lt_of_le hp (by omega))
  have hZ : C.DetectsSingleZ :=
    C.detectsSingleZ_of_hasDistanceAtLeast_two hdTwo
  have hdetect : C.DetectsNumberOps :=
    C.detectsNumberOps_of_detectsSingleZ hZ
  let q := R.q
  have hq : 0 < q := lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero q := ⟨hq.ne'⟩
  have hRpres' : C.Preserves (phaseHom n q hq R.a) := by
    simpa [q, ReducedDiagonalRepresentative.phase] using hRpres
  have hRclass' :
      C.projectiveClassMap ⟨phaseHom n q hq R.a, hRpres'⟩ = U := by
    simpa [q, ReducedDiagonalRepresentative.phase] using hRclass
  have hsourceNe :
      C.projectiveClassMap ⟨phaseHom n q hq R.a, hRpres'⟩ ≠ 0 := by
    rw [hRclass']
    exact hU
  have hcard : Fintype.card (C.ActiveResidue R.a) = 2 :=
    C.card_activeResidue_eq_two_of_projectiveClass_ne_zero
      hq R.a hRpres' hsourceNe
  obtain ⟨b0, b1, hb01, hexhaust⟩ :=
    C.exists_activeResidue_pair_of_card_eq_two R.a hcard
  have hspan : C.actualSectorAffineSpan R.a b0 =
      C.actualSectorAffineSpan R.a b1 :=
    C.actualSectorAffineSpan_eq_of_hasDistanceAtLeast
      hq R.a hRpres' hd hd3 b0 b1
  obtain ⟨t, ht⟩ := C.actualSectorSupport_nonempty hq R.a hRpres' b0

  let CX : CodeProjector n 2 := C.reindex (xorEquiv t)
  let aX : Fin n → ZMod q := xorCoefficient t R.a
  let b0X : CX.ActiveResidue aX := C.xorActiveResidueEquiv R.a t b0
  let b1X : CX.ActiveResidue aX := C.xorActiveResidueEquiv R.a t b1
  have hXpres : CX.Preserves (phaseHom n q hq aX) := by
    exact C.reindex_xor_preserves_phaseHom hq R.a t hRpres'
  have hdX : CX.HasDistanceAtLeast d :=
    C.hasDistanceAtLeast_reindex_xor hd t
  have hb0X : b0X.1 = 0 := by
    exact C.transported_anchor_val_eq_zero R.a t b0 ht
  have hzeroX : (0 : BitString n) ∈ CX.actualSectorSupport aX b0X := by
    exact C.zero_mem_transported_actualSectorSupport R.a t b0 ht
  have hb01X : b0X ≠ b1X := by
    exact (C.xorActiveResidueEquiv R.a t).injective.ne hb01
  obtain ⟨D⟩ := CX.exists_normalizedDistanceThreePhaseSystem
    hq aX hXpres hdX hd3 b0X b1X hb01X hb0X hzeroX
  letI : Fintype (CX.actualSectorSupport aX b0X) :=
    CategoryTheory.FinCategory.fintypeObj

  let thetaRat : Fin n → ℚ := D.pivot.solution
  let thetaRatReal : Fin n → ℝ := fun j ↦ (thetaRat j : ℝ)
  let thetaOld : Fin n → ℝ := phaseLift (phaseHom n q hq aX)
  have hphaseOld : realVectorPhase thetaOld = phaseHom n q hq aX := by
    exact realVectorPhase_phaseLift _
  have hexhaustX (b : CX.ActiveResidue aX) : b = b0X ∨ b = b1X := by
    obtain ⟨b, rfl⟩ := (C.xorActiveResidueEquiv R.a t).surjective b
    rcases hexhaust b with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hagree (b : CX.ActiveResidue aX) (x : BitString n)
      (hx : x ∈ CX.actualSectorSupport aX b) :
      realSupportWeight thetaRatReal x = realSupportWeight thetaOld x := by
    rcases hexhaustX b with rfl | rfl
    · simpa [thetaRatReal, thetaRat, thetaOld] using
        D.agreesOnAnchor x hx
    · simpa [thetaRatReal, thetaRat, thetaOld] using
        D.agreesOnSecond x hx
  have hscalarX : CX.ActsAsScalar
      (rationalVectorPhase thetaRat - phaseHom n q hq aX) := by
    rw [← hphaseOld]
    change CX.ActsAsScalar
      (realVectorPhase thetaRatReal - realVectorPhase thetaOld)
    rw [← realVectorPhase_sub]
    apply CX.actsAsScalar_of_constant_on_actualSectorSupports
      hq aX hXpres (realVectorPhase (thetaRatReal - thetaOld)) 0
    intro b x hx
    rw [supportPhase_realVectorPhase, realSupportWeight_sub,
      hagree b x hx, sub_self]
    rfl
  have hdiffPresX : CX.Preserves
      (rationalVectorPhase thetaRat - phaseHom n q hq aX) :=
    CX.preserves_of_actsAsScalar hscalarX
  have hratPresX : CX.Preserves (rationalVectorPhase thetaRat) := by
    have hadd := CX.preserves_add hdiffPresX hXpres
    simpa only [sub_add_cancel] using hadd
  have hnormalizedSource :
      phaseHom n q hq aX = xorPhase t R.phase := by
    symm
    simpa [aX, q, ReducedDiagonalRepresentative.phase] using
      (xorPhase_phaseHom hq t R.a)
  have hscalarX' : CX.ActsAsScalar
      (rationalVectorPhase thetaRat - xorPhase t R.phase) := by
    simpa [hnormalizedSource] using hscalarX
  obtain ⟨hratPresBack, hclassBack, _hscalarBack⟩ :=
    C.exists_preserves_projectiveClass_eq_of_xor_replacement
      t R.phase hRpres (rationalVectorPhase thetaRat)
      hratPresX hscalarX'
  have hclassBackU :
      C.projectiveClassMap
        ⟨xorPhase t (rationalVectorPhase thetaRat), hratPresBack⟩ = U :=
    hclassBack.trans hRclass

  let M := D.binaryPivotMinor
  let smithDenominator := M.finalSmithInvariant
  have hphaseX : rationalVectorPhase thetaRat =
      rationalPhase smithDenominator D.smithNumerator := by
    apply rationalVectorPhase_eq_rationalPhase_of_smul_eq
      M.finalSmithInvariant_pos thetaRat D.smithNumerator
    simpa [M, thetaRat] using D.smithNumerator_spec_binaryPivotMinor
  let numerator : Fin n → ℤ := xorIntegerVector t D.smithNumerator
  have hphaseBack : xorPhase t (rationalVectorPhase thetaRat) =
      rationalPhase smithDenominator numerator := by
    rw [hphaseX, xorPhase_rationalPhase]
  have hratPres : C.Preserves
      (rationalPhase smithDenominator numerator) := by
    rw [← hphaseBack]
    exact hratPresBack
  have hratClass : C.projectiveClassMap
      ⟨rationalPhase smithDenominator numerator, hratPres⟩ = U := by
    have hsubtype :
        (⟨rationalPhase smithDenominator numerator, hratPres⟩ :
          C.preservingPhases) =
        ⟨xorPhase t (rationalVectorPhase thetaRat), hratPresBack⟩ := by
      apply Subtype.ext
      exact hphaseBack.symm
    rw [hsubtype]
    exact hclassBackU
  have hsmithPos : 0 < smithDenominator :=
    M.finalSmithInvariant_pos
  have hkill : smithDenominator •
      rationalPhase smithDenominator numerator = 0 :=
    rationalPhase_nsmul hsmithPos numerator
  obtain ⟨R', hR'pres, hR'class, hmdiv, hqdiv, hR'order⟩ :=
    C.exists_reduced_representative_of_nsmul_eq_zero
      (rationalPhase smithDenominator numerator) hratPres U hratClass hU
      smithDenominator hsmithPos hkill

  have hmatrixSizePos : 1 ≤ D.pivot.size := by
    rw [D.pivot_size_eq]
    exact D.r_pos
  have hmatrixSizeLe : D.pivot.size ≤ D.r := D.pivot_size_eq.le
  have hsmithBeta : M.finalSmithInvariant ≤ smithBeta D.r :=
    finalSmithInvariant_le_smithBeta
      hmatrixSizePos hmatrixSizeLe M
  have hbetaN : smithBeta D.r ≤ smithBeta n :=
    smithBeta_mono D.r_le
  have hqleSmith : R'.q ≤ M.finalSmithInvariant :=
    Nat.le_of_dvd M.finalSmithInvariant_pos hqdiv
  have hmpos : 0 < addOrderOf U :=
    Nat.pos_of_dvd_of_pos hmdiv
      (lt_of_lt_of_le Nat.zero_lt_two R'.q_ge_two)
  have hmneOne : addOrderOf U ≠ 1 := by
    intro hm
    apply hU
    exact AddMonoid.addOrderOf_eq_one_iff.mp hm
  have hmTwo : 2 ≤ addOrderOf U := by omega
  have hmleq : addOrderOf U ≤ R'.q :=
    Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_two R'.q_ge_two) hmdiv
  have hqleBetaR : R'.q ≤ smithBeta D.r :=
    hqleSmith.trans hsmithBeta
  have hqleBetaN : R'.q ≤ smithBeta n :=
    hqleBetaR.trans hbetaN
  have hminBetaR : C.minimalPhysicalOrder U ≤ smithBeta D.r :=
    (C.minimalPhysicalOrder_le U R' hR'pres hR'class).trans hqleBetaR
  have hminBetaN : C.minimalPhysicalOrder U ≤ smithBeta n :=
    hminBetaR.trans hbetaN
  have hrFirst : D.r = C.actualSectorAffineDimension R.a b0 := by
    exact D.r_eq_actualSectorAffineDimension.trans
      (C.actualSectorAffineDimension_xor R.a t b0)
  have hrSecond : D.r = C.actualSectorAffineDimension R.a b1 := by
    unfold actualSectorAffineDimension
    rw [← hspan]
    exact hrFirst
  exact ⟨⟨{
    sourceRepresentative := R
    sourcePreserves := hRpres
    sourceClass_eq := hRclass
    firstSector := b0
    secondSector := b1
    sectors_ne := hb01
    sectors_exhaust := hexhaust
    affineSpan_eq := hspan
    r := D.r
    r_eq_firstAffineDimension := hrFirst
    r_eq_secondAffineDimension := hrSecond
    r_pos := D.r_pos
    r_le := D.r_le
    representative := R'
    preserves := hR'pres
    class_eq := hR'class
    matrixSize := D.pivot.size
    matrixSize_eq_r := D.pivot_size_eq
    binaryMatrix := M
    normalizationOrigin := t
    normalizationOrigin_mem := ht
    pivotRows := D.pivot.row
    pivotColumns := D.pivot.column
    pivotRows_independent := by
      simpa [CX, aX, b0X] using D.selectedSupportVectors_independent_real
    pivotRows_span_affineDirection := by
      simpa [CX, aX, b0X] using
        D.selectedSupportVectors_span_affineDirection hzeroX
    pivotRows_span_secondAffineDirection := by
      simpa [CX, aX, b0X, b1X] using
        D.selectedSupportVectors_span_secondAffineDirection hzeroX
    binaryMatrix_eq_coordinateMinor := by
      rfl
    projectiveOrder_ge_two := hmTwo
    projectiveOrder_dvd := hmdiv
    projectiveOrder_le_physicalOrder := hmleq
    physicalOrder_dvd_smith := hqdiv
    physicalOrder := hR'order
    physicalOrder_ge_two := R'.q_ge_two
    physicalOrder_le_smith := hqleSmith
    smith_le_beta_r := hsmithBeta
    beta_r_le_beta_n := hbetaN
    physicalOrder_le_beta_r := hqleBetaR
    physicalOrder_le_beta_n := hqleBetaN
    minimalPhysicalOrder_le_beta_r := hminBetaR
    minimalPhysicalOrder_le_beta_n := hminBetaN }, rfl⟩⟩


/-- The class-only entry point retains its original statement. The specified
representative entry point above also exposes which gate supplies the supports. -/
theorem distanceThree_physicalOrder_bound
    (hd : C.HasDistanceAtLeast d) (hd3 : 3 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    Nonempty (C.DistanceThreePhysicalOrderBoundConclusion U) := by
  have hdTwo : C.HasDistanceAtLeast 2 := by
    intro p hp
    exact hd p (lt_of_lt_of_le hp (by omega))
  have hZ := C.detectsSingleZ_of_hasDistanceAtLeast_two hdTwo
  have hdetect := C.detectsNumberOps_of_detectsSingleZ hZ
  obtain ⟨R, hRpres, hRclass, _, _, _⟩ :=
    C.exists_reduced_representative hdetect U hU
  obtain ⟨H⟩ := C.distanceThree_physicalOrder_bound_of_representative
    hd hd3 U hU R hRpres hRclass
  exact ⟨H.1⟩

end CodeProjector

end

end QECC
