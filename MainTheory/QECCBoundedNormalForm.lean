import MainTheory.QECCFrameBridge
import MainTheory.QECCSmithBridge
import QECC.GeneralPhysicalOrderBound
import QECC.GeneralSSLP
import QECC.GeneralCanonicalSSLP
import QECC.DistanceThreeOrderBound

/-!
# One bounded representative carries the normal form and its moments

The previous existence theorems could select different representatives. Here
the normal-form colors and all low-degree sector moments belong to the same
representative that carries the physical-order bound. The specified-gate
distance-three entry point additionally retains its source representative.
-/

namespace MainTheory.QECCBoundedNormalForm

noncomputable section

variable {n K d : ℕ}

/-- Build intrinsic sector data on the supplied representative, without choosing
another representative of its projective class. -/
theorem intrinsic_of_representative (C : QECC.CodeProjector n K)
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0)
    (R : QECC.ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (hclass : C.projectiveClassMap ⟨R.phase, hpres⟩ = U) :
    ∃ b0 : C.ActiveResidue R.a, C.IntrinsicSSLPData U R hpres b0 := by
  have hK := C.rank_pos_of_projectiveClass_ne_zero U hU
  have hdTwo : C.HasDistanceAtLeast 2 := by
    intro p hp
    exact hd p (lt_of_lt_of_le hp hd2)
  have hZ := C.detectsSingleZ_of_hasDistanceAtLeast_two hdTwo
  let H := C.finite_diagonal_logical_group_and_physical_representatives hZ
  letI : Finite C.ProjectiveDiagonalGroup := H.groupFinite
  have hq : 0 < R.q := lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hq.ne'⟩
  obtain ⟨b0⟩ := C.exists_activeResidue hK hq R.a hpres
  have hmpos : 0 < addOrderOf U := addOrderOf_pos U
  have hmne : addOrderOf U ≠ 1 := by
    intro hm
    exact hU (AddMonoid.addOrderOf_eq_one_iff.mp hm)
  have hrelative : addOrderOf (C.relativeResidues R.a b0) = addOrderOf U := by
    rw [← hclass]
    exact (C.projectiveOrder_eq_relativeResiduesOrder hq R.a hpres b0).symm
  refine ⟨b0, {
    class_eq := hclass
    commonGCD_eq_one := R.commonGCD_eq_one
    physicalOrder := R.orderOf_diagonalGate
    logicalOrder_gt_one := by omega
    logicalOrder_dvd_physical := ?_
    relativeOrder := hrelative
    relativeInjective := ?_
    multiplicityPositive := fun b => C.activeResidue_finrank_pos R.a b
    multiplicitySum := C.sum_finrank_activeResidue hq R.a hpres
    supportedInFiber := fun _ psi _ hx => C.phaseSector_support psi hx }⟩
  · rw [← hclass]
    let rep : C.preservingPhases := ⟨R.phase, hpres⟩
    have hmap := addOrderOf_map_dvd C.projectiveClassMap rep
    have hrep : addOrderOf rep = R.q := by
      have hi := addOrderOf_injective C.preservingPhases.subtype
        (AddSubgroup.subtype_injective C.preservingPhases) rep
      change addOrderOf R.phase = addOrderOf rep at hi
      rw [R.addOrderOf_phase] at hi
      exact hi.symm
    rwa [hrep] at hmap
  · intro b c hbc
    apply Subtype.ext
    change b.1 - b0.1 = c.1 - b0.1 at hbc
    exact sub_left_injective hbc

/-- Normal form and probability moments attached to one Smith-bounded lift.
The beta bound uses the manuscript's constant, via the existing Smith bridge. -/
theorem bounded_normal_form (C : QECC.CodeProjector n K)
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    ∃ B : C.GeneralPhysicalOrderBoundConclusion U,
      ∃ (b0 : C.ActiveResidue B.bounded.representative.a)
        (gamma : C.ActiveResidue B.bounded.representative.a → ZMod (addOrderOf U)),
        C.GeneralSSLPData U B.bounded.representative B.bounded.preserves b0 gamma ∧
        C.SSLPSectorProbabilityConclusion
          (lt_of_lt_of_le Nat.zero_lt_two B.bounded.representative.q_ge_two)
          B.bounded.representative.a B.bounded.preserves hd ∧
        B.bounded.representative.q ≤ MainTheory.BetaExists.betaOf (n + K - 1) := by
  have hdTwo : C.HasDistanceAtLeast 2 := by
    intro p hp
    exact hd p (lt_of_lt_of_le hp hd2)
  have hZ := C.detectsSingleZ_of_hasDistanceAtLeast_two hdTwo
  have hN := C.detectsNumberOps_of_detectsSingleZ hZ
  obtain ⟨B⟩ := C.general_physicalOrder_bound hN U hU
  obtain ⟨b0, H⟩ := intrinsic_of_representative C hd hd2 U hU
    B.bounded.representative B.bounded.preserves B.bounded.class_eq
  obtain ⟨gamma, hzero, hinj, hformula, hprimitive, hgcd⟩ :=
    C.exists_primitive_sslp_colors U B.bounded.representative B.bounded.preserves b0 H
  refine ⟨B, b0, gamma, {
    intrinsic := H
    anchorColor := hzero
    colorsDistinct := hinj
    residueFormula := hformula
    colorsPrimitive := hprimitive
    colorGCD_eq_one := hgcd }, ?_, ?_⟩
  · exact C.sslp_sector_probabilities_and_moments _ _ _ hd
  · have hnu : 1 ≤ n + K - 1 := by
      have := B.two_le_sectorCount
      have := B.sectorCount_le_rank
      omega
    rw [← MainTheory.QECCSmithBridge.smithBeta_eq_betaOf hnu]
    exact B.physicalOrder_le_rankBeta

/-- The canonical colored decomposition, sector probabilities and physical
order bounds all start from one bounded representative. `B.sectorCount`
retains the source-sector count used by its actual-support Smith system. -/
theorem bounded_full_normal_form (C : QECC.CodeProjector n K)
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    ∃ B : C.GeneralPhysicalOrderBoundConclusion U,
      ∃ (b0 : C.ActiveResidue B.bounded.representative.a)
        (gamma : C.ActiveResidue B.bounded.representative.a → ZMod (addOrderOf U))
        (H : C.GeneralSSLPData U B.bounded.representative B.bounded.preserves b0 gamma),
        C.HasCanonicalGeneralSSLPData U B.bounded.representative
          B.bounded.preserves b0 gamma H ∧
        C.SSLPSectorProbabilityConclusion
          (lt_of_lt_of_le Nat.zero_lt_two B.bounded.representative.q_ge_two)
          B.bounded.representative.a B.bounded.preserves hd ∧
        B.bounded.representative.q ≤
          MainTheory.BetaExists.betaOf (n + B.sectorCount - 1) ∧
        B.bounded.representative.q ≤
          MainTheory.BetaExists.betaOf (n + K - 1) := by
  obtain ⟨B, b0, gamma, H, hmom, hbound⟩ := bounded_normal_form C hd hd2 U hU
  refine ⟨B, b0, gamma, H,
    C.exists_canonical_general_sslp_data U _ _ b0 gamma H, hmom, ?_, hbound⟩
  have hnu : 1 ≤ n + B.sectorCount - 1 := by
    have := B.two_le_sectorCount
    omega
  rw [← MainTheory.QECCSmithBridge.smithBeta_eq_betaOf hnu]
  exact B.bounded.physicalOrder_le_beta

/-- Distance-three Smith data are bound to the caller's chosen gate. -/
theorem distanceThree_for_supplied_gate (C : MainTheory.CodeSpec.ExactCode n 2 d)
    (hd3 : 3 ≤ d) (R : QECC.ReducedDiagonalRepresentative n)
    (hpres : (MainTheory.QECCFrameBridge.ofFrame C.frame).Preserves R.phase)
    (hne : (MainTheory.QECCFrameBridge.ofFrame C.frame).projectiveClassMap
      ⟨R.phase, hpres⟩ ≠ 0) :
    ∃ H : QECC.CodeProjector.DistanceThreePhysicalOrderBoundConclusion
        (MainTheory.QECCFrameBridge.ofFrame C.frame)
          ((MainTheory.QECCFrameBridge.ofFrame C.frame).projectiveClassMap ⟨R.phase, hpres⟩),
      H.sourceRepresentative = R ∧
      H.representative.q ≤ MainTheory.BetaExists.betaOf H.r := by
  let Q := MainTheory.QECCFrameBridge.ofFrame C.frame
  obtain ⟨H⟩ := Q.distanceThree_physicalOrder_bound_of_representative
    (MainTheory.QECCFrameBridge.hasDistanceAtLeast C) hd3 _ hne R hpres rfl
  refine ⟨H.1, H.2, ?_⟩
  rw [← MainTheory.QECCSmithBridge.smithBeta_eq_betaOf H.1.r_pos]
  exact H.1.physicalOrder_le_beta_r

end

end MainTheory.QECCBoundedNormalForm
