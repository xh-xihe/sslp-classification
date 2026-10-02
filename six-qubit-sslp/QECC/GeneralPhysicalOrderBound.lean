import QECC.ActiveSectorCount
import QECC.ActualSupportTransport
import QECC.NumberDetectionTransport
import QECC.PhaseCoefficientTransport
import QECC.SectorPhaseSystem
import QECC.RationalDenominator
import QECC.SmithOrderBound

namespace QECC

noncomputable section

namespace CodeProjector

variable {n K : ℕ} (C : CodeProjector n K)

/-- Number of active phase sectors of a reduced representative.  The
representative's positive denominator supplies the local `NeZero` instance. -/
def reducedActiveSectorCount (R : ReducedDiagonalRepresentative n) : ℕ := by
  letI : NeZero R.q :=
    ⟨(lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two).ne'⟩
  exact Fintype.card (C.ActiveResidue R.a)

/-- The formal conclusion of the general physical-order theorem in Section
III.C.  `sectorCount` is the number of distinct logical phase sectors of the
source representative, while `bounded` is the rationally replaced reduced
representative and its Smith certificate. -/
structure GeneralPhysicalOrderBoundConclusion
    (U : C.ProjectiveDiagonalGroup) where
  sourceRepresentative : ReducedDiagonalRepresentative n
  sourcePreserves : C.Preserves sourceRepresentative.phase
  sourceClass_eq :
    C.projectiveClassMap ⟨sourceRepresentative.phase, sourcePreserves⟩ = U
  sectorCount : ℕ
  sectorCount_eq :
    sectorCount = C.reducedActiveSectorCount sourceRepresentative
  two_le_sectorCount : 2 ≤ sectorCount
  sectorCount_le_rank : sectorCount ≤ K
  bounded : C.SmithBoundedPhysicalRepresentative U
    (n + sectorCount - 1)
  beta_sector_le_rank :
    smithBeta (n + sectorCount - 1) ≤ smithBeta (n + K - 1)
  physicalOrder_le_rankBeta :
    bounded.representative.q ≤ smithBeta (n + K - 1)
  minimalPhysicalOrder_le_sectorBeta :
    C.minimalPhysicalOrder U ≤ smithBeta (n + sectorCount - 1)
  minimalPhysicalOrder_le_rankBeta :
    C.minimalPhysicalOrder U ≤ smithBeta (n + K - 1)

/-- A zero-variable pivot has final Smith invariant one. -/
private theorem pivotMinor_finalSmithInvariant_eq_one_of_size_eq_zero
    {rows : Type*} [Fintype rows] {N : ℕ}
    {A : Matrix rows (Fin N) ℤ} {h : rows → ℤ}
    (S : BinaryPivotSolution N A h) (hsize : S.size = 0) :
    S.pivotMinor.finalSmithInvariant = 1 := by
  haveI : Subsingleton (Fin S.size → ℤ) := by
    constructor
    intro u v
    funext i
    exact Fin.elim0 (hsize ▸ i)
  haveI : Subsingleton S.pivotMinor.Cokernel := inferInstance
  exact AddMonoid.exp_eq_one_of_subsingleton

/-- **Physical-order bound for general code dimension.**

For every nonzero projective diagonal logical class on a code detecting all
single-coordinate number operators, the binary actual-support system produces
a reduced representative of exact physical order `q` with
`addOrderOf U ∣ q`, `q ∣ d_s(C)`, and
`q ≤ d_s(C) ≤ β_(n+ell-1) ≤ β_(n+K-1)`.  The same first beta also bounds the
minimum physical order. -/
theorem general_physicalOrder_bound
    (hdetect : C.DetectsNumberOps)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    Nonempty (C.GeneralPhysicalOrderBoundConclusion U) := by
  classical
  obtain ⟨R, hRpres, hRclass, _hgcd, _hphysical, _hprojectiveDvd⟩ :=
    C.exists_reduced_representative hdetect U hU
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
  let ell := Fintype.card (C.ActiveResidue R.a)
  have hell2 : 2 ≤ ell :=
    C.two_le_card_activeResidue_of_projectiveClass_ne_zero
      hq R.a hRpres' hsourceNe
  have hellK : ell ≤ K := C.card_activeResidue_le hq R.a hRpres'
  have hK : 0 < K := C.rank_pos_of_projectiveClass_ne_zero U hU
  obtain ⟨b0⟩ := C.exists_activeResidue hK hq R.a hRpres'
  obtain ⟨t, ht⟩ := C.actualSectorSupport_nonempty hq R.a hRpres' b0

  let CX : CodeProjector n K := C.reindex (xorEquiv t)
  let aX : Fin n → ZMod q := xorCoefficient t R.a
  let bX : CX.ActiveResidue aX := C.xorActiveResidueEquiv R.a t b0
  have hXpres : CX.Preserves (phaseHom n q hq aX) := by
    exact C.reindex_xor_preserves_phaseHom hq R.a t hRpres'
  have hbX : bX.1 = 0 := by
    exact C.transported_anchor_val_eq_zero R.a t b0 ht
  have hzeroX : (0 : BitString n) ∈ CX.actualSectorSupport aX bX := by
    exact C.zero_mem_transported_actualSectorSupport R.a t b0 ht
  have hdetectX : CX.DetectsNumberOps :=
    C.detectsNumberOps_reindex_xor t hdetect
  obtain ⟨P⟩ := CX.exists_normalizedSectorPhasePivot
    hq aX hXpres bX hbX hzeroX

  let physicalX : Fin n → ℚ :=
    NormalizedSectorPhasePivot.rationalPhysical CX P
  let sectorX : CX.ActiveResidue aX → ℚ :=
    NormalizedSectorPhasePivot.rationalSector CX P
  have horiginalSol :
      CX.SolvesActualSectorEquations aX
        (CX.actualSectorPhaseRHS hq aX)
        (phaseLift (phaseHom n q hq aX))
        (fun b => zmodPhaseLift q hq b.1) := by
    intro b x hx
    exact CX.actualSectorPhaseRHS_spec hq aX b x hx
  have hrationalSol :
      CX.SolvesActualSectorEquations aX
        (CX.actualSectorPhaseRHS hq aX)
        (fun j => (physicalX j : ℝ))
        (fun b => (sectorX b : ℝ)) := by
    simpa [physicalX, sectorX,
      NormalizedSectorPhasePivot.rationalPhysical,
      NormalizedSectorPhasePivot.rationalSector] using
      (SectorPhasePivot.solvesActualSectorEquations
        CX hq aX bX P.pivot)
  have hphysicalPres :
      CX.Preserves (realVectorPhase (phaseLift (phaseHom n q hq aX))) := by
    simpa using hXpres
  obtain ⟨hphysicalXPres, hclassX, hscalarX⟩ :=
    CX.rationalVectorPhase_same_projectiveClass_of_sameSectorEquations
      hq aX hXpres hdetectX
      (CX.actualSectorPhaseRHS hq aX)
      (phaseLift (phaseHom n q hq aX)) hphysicalPres
      (fun b => zmodPhaseLift q hq b.1)
      physicalX sectorX horiginalSol hrationalSol bX
  have hnormalizedSource :
      phaseHom n q hq aX = xorPhase t R.phase := by
    symm
    simpa [aX, q, ReducedDiagonalRepresentative.phase] using
      (xorPhase_phaseHom hq t R.a)
  have hscalarX' : CX.ActsAsScalar
      (rationalVectorPhase physicalX - xorPhase t R.phase) := by
    simpa [hnormalizedSource] using hscalarX
  obtain ⟨hphysicalPresBack, hclassBack, _hscalarBack⟩ :=
    C.exists_preserves_projectiveClass_eq_of_xor_replacement
      t R.phase hRpres (rationalVectorPhase physicalX)
      hphysicalXPres hscalarX'
  have hclassBackU :
      C.projectiveClassMap
        ⟨xorPhase t (rationalVectorPhase physicalX), hphysicalPresBack⟩ = U := by
    exact hclassBack.trans hRclass

  let S := P.pivot
  let d := S.pivotMinor.finalSmithInvariant
  obtain ⟨k, hk⟩ := S.exists_integral_finalSmithInvariant_smul_solution
  let kPhysicalX : Fin n → ℤ :=
    fun j => k (CX.physicalPhaseColumn aX bX j)
  have hkPhysical : (fun j => (kPhysicalX j : ℚ)) = d • physicalX := by
    funext j
    have hj := congrFun hk (CX.physicalPhaseColumn aX bX j)
    simpa [kPhysicalX, d, physicalX,
      NormalizedSectorPhasePivot.rationalPhysical,
      SectorPhasePivot.physical, sectorPhasePhysicalPart,
      Pi.smul_apply] using hj
  have hd : 0 < d := S.pivotMinor.finalSmithInvariant_pos
  have hphaseX : rationalVectorPhase physicalX =
      rationalPhase d kPhysicalX :=
    rationalVectorPhase_eq_rationalPhase_of_smul_eq
      hd physicalX kPhysicalX hkPhysical
  let kPhysical : Fin n → ℤ := xorIntegerVector t kPhysicalX
  have hphaseBack :
      xorPhase t (rationalVectorPhase physicalX) =
          rationalPhase d kPhysical := by
    rw [hphaseX, xorPhase_rationalPhase]
  have hratPres : C.Preserves (rationalPhase d kPhysical) := by
    rw [← hphaseBack]
    exact hphysicalPresBack
  have hratClass :
      C.projectiveClassMap ⟨rationalPhase d kPhysical, hratPres⟩ = U := by
    have hsubtype :
        (⟨rationalPhase d kPhysical, hratPres⟩ : C.preservingPhases) =
          ⟨xorPhase t (rationalVectorPhase physicalX), hphysicalPresBack⟩ := by
      apply Subtype.ext
      exact hphaseBack.symm
    rw [hsubtype]
    exact hclassBackU
  have hsize : 1 ≤ S.size := by
    apply Nat.one_le_iff_ne_zero.2
    intro hs0
    have hdOne : d = 1 := by
      exact pivotMinor_finalSmithInvariant_eq_one_of_size_eq_zero S hs0
    have hphaseZero : rationalPhase d kPhysical = 0 := by
      rw [hdOne]
      funext j
      simp [rationalPhase]
    apply hU
    rw [← hratClass]
    have hrepZero :
        (⟨rationalPhase d kPhysical, hratPres⟩ : C.preservingPhases) = 0 := by
      apply Subtype.ext
      exact hphaseZero
    rw [hrepZero, map_zero]

  have hwidth : CX.sectorPhaseSystemWidth aX bX = n + ell - 1 := by
    rw [CX.sectorPhaseSystemWidth_eq]
    have hcard : Fintype.card (CX.ActiveResidue aX) = ell := by
      exact Fintype.card_congr (C.xorActiveResidueEquiv R.a t) |>.symm
    rw [hcard]
    omega
  have hsizeBound : S.size ≤ n + ell - 1 := by
    rw [← hwidth]
    exact S.size_le
  obtain ⟨B⟩ := C.exists_smithBoundedPhysicalRepresentative
    U hU hsize hsizeBound S.pivotMinor kPhysical hratPres hratClass
  have hnu : n + ell - 1 ≤ n + K - 1 := by omega
  have hbeta : smithBeta (n + ell - 1) ≤ smithBeta (n + K - 1) :=
    smithBeta_mono hnu
  exact ⟨{
    sourceRepresentative := R
    sourcePreserves := hRpres
    sourceClass_eq := hRclass
    sectorCount := ell
    sectorCount_eq := by
      simp [ell, reducedActiveSectorCount]
    two_le_sectorCount := hell2
    sectorCount_le_rank := hellK
    bounded := B
    beta_sector_le_rank := hbeta
    physicalOrder_le_rankBeta := B.physicalOrder_le_beta.trans hbeta
    minimalPhysicalOrder_le_sectorBeta := B.minimalPhysicalOrder_le_beta
    minimalPhysicalOrder_le_rankBeta :=
      B.minimalPhysicalOrder_le_beta.trans hbeta }⟩

end CodeProjector

end

end QECC
