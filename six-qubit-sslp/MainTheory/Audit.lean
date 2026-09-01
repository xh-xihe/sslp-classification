import MainTheory.Rationalize
import MainTheory.Denominator
import MainTheory.Clearing
import MainTheory.Covariance
import MainTheory.AffineSpan
import MainTheory.ActiveFace
import MainTheory.D3Bound
import MainTheory.RealGate
import MainTheory.OuterIndex
import MainTheory.Levels
import MainTheory.WImages
import MainTheory.Gate
import MainTheory.PhaseSector
import MainTheory.Normalize
import MainTheory.Cyclic
import MainTheory.RankTwo
import MainTheory.BoundedRepresentationCertified
import MainTheory.SectionTwoGeneral
import MainTheory.GeneralSpectralSectors
import MainTheory.PivotSize
import MainTheory.SectorMeanValue
import MainTheory.UnitarySpectral
import MainTheory.LogicalCharacter
import MainTheory.IntrinsicAbelian
import MainTheory.GeneralFiniteness
import MainTheory.BetaExists
import MainTheory.DeterminantalRank
import MainTheory.BinaryPivot
import MainTheory.ColoredBound
import MainTheory.GeneralLiftOrder
import MainTheory.QuantitativeGroup
import MainTheory.RankTwoSSLP
import MainTheory.GroupOrder
import MainTheory.NumberOperator
import MainTheory.SortedNormalForm
import MainTheory.FlipSemanticTransport
import MainTheory.D3BoundedNormalForm
import MainTheory.SSLPCompleteness
import MainTheory.PrimitiveReduction
import MainTheory.QMinBound
import MainTheory.SectionThreeNonVacuity

/-!
# Axiom audit for the `main.tex` general theory

Every headline of `MainTheory` is printed here, on the same standard the
six-qubit development is held to: the footprint must be contained in
`{propext, Classical.choice, Quot.sound}`, with no `sorryAx`, no
`ofReduceBool` and no `native_decide`.

`Classical.choice` is expected throughout this library: the retraction of the
structure map is chosen, not constructed.
-/

#print axioms MainTheory.Rationalize.retract
#print axioms MainTheory.Rationalize.retract_algebraMap
#print axioms MainTheory.Rationalize.retract_algebraMap_mul
#print axioms MainTheory.Rationalize.exists_solution_of_exists_solution_ext
#print axioms MainTheory.Rationalize.eq_of_ker_eq_zero
#print axioms MainTheory.Rationalize.pi_solution
#print axioms MainTheory.Rationalize.rationalized_pi_solution

#print axioms MainTheory.Denominator.clears_iff
#print axioms MainTheory.Denominator.lcmDen_pos
#print axioms MainTheory.Denominator.lcmDen_clears
#print axioms MainTheory.Denominator.lcmDen_dvd_of_clears
#print axioms MainTheory.Denominator.liftNum_spec
#print axioms MainTheory.Denominator.eq_one_of_dvd_lcmDen_of_dvd_liftNum
#print axioms MainTheory.Denominator.lcmDen_example
#print axioms MainTheory.Denominator.lift_exists

#print axioms MainTheory.Gate.weight_stdBasis
#print axioms MainTheory.Gate.diag_pow
#print axioms MainTheory.Gate.natCast_mul_weight
#print axioms MainTheory.Gate.dvd_of_forall_mul_eq_zero
#print axioms MainTheory.Gate.pow_eq_one_iff
#print axioms MainTheory.Gate.primitive_orbit21
#print axioms MainTheory.Gate.not_primitive_allEven
#print axioms MainTheory.Gate.orbit21_order

#print axioms MainTheory.PhaseSector.diag_eq_of_eigen
#print axioms MainTheory.PhaseSector.weight_eq_of_eigen
#print axioms MainTheory.PhaseSector.ssCondition_of_eigen
#print axioms MainTheory.PhaseSector.disjoint_of_ne
#print axioms MainTheory.PhaseSector.eigen_of_ssCondition
#print axioms MainTheory.PhaseSector.eigen_iff_ssCondition
#print axioms MainTheory.PhaseSector.exists_eigen
#print axioms MainTheory.PhaseSector.ssCondition_nonvacuous
#print axioms MainTheory.PhaseSector.support_of_ssCondition
#print axioms MainTheory.PhaseSector.support_of_eigen

#print axioms MainTheory.Normalize.flip_flip
#print axioms MainTheory.Normalize.weight_bxor
#print axioms MainTheory.Normalize.weight_flip_self
#print axioms MainTheory.Normalize.addOrderOf_dvd
#print axioms MainTheory.Normalize.exists_unit_reduction_inv
#print axioms MainTheory.Normalize.exists_unit_mul_eq_one
#print axioms MainTheory.Normalize.ssCondition_bxor
#print axioms MainTheory.Normalize.weight_bxor_check

#print axioms MainTheory.Cyclic.chi_zero
#print axioms MainTheory.Cyclic.diag_eq_chi
#print axioms MainTheory.Cyclic.pow_mod
#print axioms MainTheory.Cyclic.chi_add
#print axioms MainTheory.Cyclic.chi_pow
#print axioms MainTheory.Cyclic.chi_eq_one_iff
#print axioms MainTheory.Cyclic.chi_ne_zero
#print axioms MainTheory.Cyclic.chi_injective
#print axioms MainTheory.Cyclic.chi_pow_eq_one_iff
#print axioms MainTheory.Cyclic.addOrderOf_dvd_card
#print axioms MainTheory.Cyclic.isCyclic_of_faithful
#print axioms MainTheory.Cyclic.addOrderOf_orbit21_gap
#print axioms MainTheory.Cyclic.orbit21_projective_order

#print axioms MainTheory.Cyclic.chi_sub
#print axioms MainTheory.RankTwo.normal_form_core
#print axioms MainTheory.RankTwo.addOrderOf_div
#print axioms MainTheory.RankTwo.order_of_two_fiber
#print axioms MainTheory.RankTwo.normal_form_nonvacuous
#print axioms MainTheory.RankTwo.addOrderOf_dvd_q

#print axioms MainTheory.Normalize.primitive_flip
#print axioms MainTheory.RankTwo.gap_ne_zero
#print axioms MainTheory.RankTwo.exists_unit_mul_eq_div

#print axioms MainTheory.Clearing.map_mulVec
#print axioms MainTheory.Clearing.det_smul_eq_adjugate_mulVec
#print axioms MainTheory.Clearing.exists_cleared_of_real
#print axioms MainTheory.Clearing.exists_clearing
#print axioms MainTheory.Clearing.clearing_example

#print axioms MainTheory.Covariance.quad_eq_sum_sq
#print axioms MainTheory.Covariance.quad_eq_zero_iff
#print axioms MainTheory.Covariance.quad_nonneg
#print axioms MainTheory.Covariance.proj_eq_zero_congr
#print axioms MainTheory.Covariance.orthDir_mem_kernel
#print axioms MainTheory.Covariance.along_not_mem_kernel

#print axioms MainTheory.AffineSpan.covariance_eq_of_hasDistance
#print axioms MainTheory.AffineSpan.mean_eq_of_hasDistance

#print axioms MainTheory.D3Bound.dot_eq_of_mulVec_eq
#print axioms MainTheory.D3Bound.exists_rational_agreeing
#print axioms MainTheory.D3Bound.exists_primitive_lift

#print axioms MainTheory.Levels.WImage_orbit21
#print axioms MainTheory.WImages.WImage_orbit9
#print axioms MainTheory.WImages.WImage_orbit10
#print axioms MainTheory.WImages.WImage_orbit11
#print axioms MainTheory.WImages.WImage_orbit16
#print axioms MainTheory.WImages.WImage_orbit22
#print axioms MainTheory.WImages.WImage_orbit23

#print axioms MainTheory.WImages.WImage_orbit7
#print axioms MainTheory.WImages.WImage_orbit8
#print axioms MainTheory.WImages.WImage_orbit45

#print axioms MainTheory.RealGate.exp_eq_of_eigen
#print axioms MainTheory.RealGate.angle_sub_int_of_eigen
#print axioms MainTheory.RealGate.diffMatrix_mulVec
#print axioms MainTheory.RealGate.exists_rational_angle

#print axioms MainTheory.OuterIndex.card_two
#print axioms MainTheory.OuterIndex.card_three
#print axioms MainTheory.OuterIndex.card_four
#print axioms MainTheory.OuterIndex.card_five
#print axioms MainTheory.OuterIndex.outerRecords_finite

#print axioms MainTheory.ActiveFace.avg_mem
#print axioms MainTheory.ActiveFace.avg_pos

#print axioms MainTheory.Covariance.mem_dualAnnihilator_span
#print axioms MainTheory.Covariance.span_eq_of_cov_eq

#print axioms MainTheory.PhaseSector.weight_eq_of_eigen_family
#print axioms MainTheory.PhaseSector.disjoint_of_ne_family
#print axioms MainTheory.PhaseSector.ssCondition_of_eigen_family

/-! ## The bounded-representation route to finiteness

These are the declarations that replace the Cartan argument: a diagonal
symmetry is transported across the entrance's local-`X` and unit-power
normalizations, comes back as a bounded label, and the resulting surjection
off `BoundedPhaseLabel 6 9` makes the intrinsic group finite. -/

#print axioms MainTheory.IntrinsicTransport.intrinsicClass_flip_eq
#print axioms MainTheory.IntrinsicTransport.mem_symmetryGroup_flip
#print axioms MainTheory.IntrinsicTransport.intrinsicClass_congr
#print axioms MainTheory.NormalizationIsShift.normalizedFrame_eq_shiftFrame
#print axioms MainTheory.FiniteGateAsPhase.gate_eq_diagonalAction
#print axioms MainTheory.FiniteGateAsPhase.exists_label_of_phaseOfAngle_le
#print axioms MainTheory.PhaseTranscription.phaseOfAngle_eq_finiteLocalPhase
#print axioms MainTheory.SameProjectiveClass.intrinsicClass_eq_of_sameProjective
#print axioms MainTheory.SymmetryToEntrance.exists_label_of_class_one
#print axioms MainTheory.CoprimePowerRecovery.exists_pow_eq_self
#print axioms MainTheory.BoundedClassPower.BoundedClass.of_pow_coprime
#print axioms MainTheory.UndoNormalization.flipPhase_phaseOfAngle_normalized
#print axioms MainTheory.BoundedRepresentationProof.boundedClass_of_twoFiber
#print axioms MainTheory.BoundedRepresentationProof.boundedClass_of_class_ne_one
#print axioms MainTheory.BoundedRepresentationProof.hasBoundedRepresentation
#print axioms MainTheory.BoundedRepresentationCertified.hasBoundedRepresentation
#print axioms MainTheory.BoundedRepresentationCertified.finite_intrinsicGroup

/-! ## Section II at general code shape

These are the paper's own statements: an exact code and a preserving diagonal
operation, with the spectral data produced rather than assumed. -/

#print axioms MainTheory.IntrinsicAbelian.intrinsicGroup_mul_comm
#print axioms MainTheory.LogicalCharacter.isCyclic_of_nontrivial
#print axioms MainTheory.UnitarySpectral.directSum_isInternal
#print axioms MainTheory.GeneralSpectral.spectralExtractionPrinciple
#print axioms MainTheory.SectionTwoGeneral.phaseSectors
#print axioms MainTheory.SectionTwoGeneral.phaseSectors_mean
#print axioms MainTheory.SectionTwoGeneral.qualitativeFiniteLift
#print axioms MainTheory.SectorMeanValue.sectorMean_eq_klScalar
#print axioms MainTheory.PivotSize.card_eq_rank
#print axioms MainTheory.PivotSize.card_le
#print axioms MainTheory.BoundedRepresentationCertified.finite_intrinsicGroup_unconditional

/-! ## Section II at arbitrary n -/

#print axioms MainTheory.GeneralFiniteness.finite_intrinsicGroup
#print axioms MainTheory.GeneralFiniteness.isCyclic
#print axioms MainTheory.GeneralFiniteness.finite_and_abelian
#print axioms MainTheory.BetaExists.exists_betaBound
#print axioms MainTheory.DeterminantalRank.exists_nonsingular_minor
#print axioms MainTheory.PivotSize.exists_pivot_card_eq_rank_le

/-! ## The paper's rank-two theorem, stated whole -/

#print axioms MainTheory.GeneralLiftOrder.liftSymmetry
#print axioms MainTheory.GeneralLiftOrder.intrinsicClass_liftSymmetry
#print axioms MainTheory.GeneralLiftOrder.exists_lift_order_dvd
#print axioms MainTheory.GeneralLiftOrder.orderOf_dvd_of_hasPrimitiveLift
#print axioms MainTheory.GeneralLiftOrder.qMin
#print axioms MainTheory.GeneralLiftOrder.qMin_spec
#print axioms MainTheory.GeneralLiftOrder.qMin_le
#print axioms MainTheory.GeneralLiftOrder.orderOf_dvd_qMin
#print axioms MainTheory.GeneralLiftOrder.orderOf_pos
#print axioms MainTheory.Generated.BinaryBetaSixKernel.Certificate.betaExact
#print axioms MainTheory.BoundedRepresentationCertified.hasBoundedRepresentation_unconditional
#print axioms MainTheory.RankTwoSSLP.rank_two_sslp
#print axioms MainTheory.RankTwoSSLP.two_fibre_normal_form
#print axioms MainTheory.RankTwoSSLP.two_fibre_normal_form_of_nontrivial
#print axioms MainTheory.RankTwoSSLP.cyclic_of_finite
#print axioms MainTheory.GroupOrder.rank_two_sslp_generator
#print axioms MainTheory.SortedForm.exists_sortedNormalForm
#print axioms MainTheory.SortedForm.exists_sortedNormalForm_le
#print axioms MainTheory.SortedForm.d2_sslp_classification
#print axioms MainTheory.SortedForm.SortedNormalForm.gate_left
#print axioms MainTheory.SortedForm.SortedNormalForm.val_rightResidue
#print axioms MainTheory.SortedForm.SortedNormalForm.gate_right
#print axioms MainTheory.SortedForm.SortedNormalForm.physicalOrder
#print axioms MainTheory.SortedForm.SortedNormalForm.projectiveOrder
#print axioms MainTheory.SortedForm.exists_sortedNormalForm_of_generator
#print axioms MainTheory.FlipSemanticTransport.gate_flip_shift
#print axioms MainTheory.FlipSemanticTransport.flipFiniteGeneratorResolution
#print axioms MainTheory.D3BoundedNormalForm.boundedGenerator
#print axioms MainTheory.D3BoundedNormalForm.exists_sortedNormalForm_le_betaN
#print axioms MainTheory.D3BoundedNormalForm.d3_bound
#print axioms MainTheory.D3BoundedNormalForm.exists_sortedNormalForm_le_nine
#print axioms MainTheory.SSLPCompleteness.weakenDistance
#print axioms MainTheory.SSLPCompleteness.completeness_distance_two
#print axioms MainTheory.SSLPCompleteness.completeness_distance_three
#print axioms MainTheory.SSLPCompleteness.completeness_six_qubit
#print axioms MainTheory.SSLPCompleteness.hasDistance_normalForm
#print axioms MainTheory.SSLPCompleteness.completeness_of_nontrivial_two
#print axioms MainTheory.SSLPCompleteness.completeness_of_nontrivial_three
#print axioms MainTheory.SSLPCompleteness.orderOf_le_nine
#print axioms MainTheory.PrimitiveReduction.primitive_reducedAngle
#print axioms MainTheory.PrimitiveReduction.finiteLocalPhase_reduced
#print axioms MainTheory.QMinBound.exists_primitiveLift_le_of_boundedClass
#print axioms MainTheory.QMinBound.qMin_le_of_boundedClass
#print axioms MainTheory.QMinBound.qMin_le_nine
#print axioms MainTheory.QMinBound.d3_bound_same_class
#print axioms MainTheory.QMinBound.d3_bound_nine
#print axioms MainTheory.SectionTwoGeneral.sectorCount_eq_two
#print axioms MainTheory.SectionTwoGeneral.rationalLift_order_le
#print axioms MainTheory.ColoredBound.pivotLift_order_le
#print axioms MainTheory.GroupOrder.exists_generator_orderOf_eq_natCard
#print axioms MainTheory.GroupOrder.logicalOrder_dvd_natCard
#print axioms MainTheory.NumberOperator.numberOp_apply
#print axioms MainTheory.NumberOperator.innerC_numberOp
#print axioms MainTheory.NumberOperator.codeProj_numberOp_codeProj

/-! ## Section III: the quantitative bound -/

#print axioms MainTheory.SharpClearing.solution_lcmDen_dvd_inverseDenominator
#print axioms MainTheory.SharpClearing.inverseDenominator_eq_smithLastFactor
#print axioms MainTheory.FiniteLift.sharp_pivot_divisibility
#print axioms MainTheory.FiniteLift.quantitative_colored_finite_lift
#print axioms MainTheory.BinaryPivot.inverseDenominator_mul_diagonal
#print axioms MainTheory.BinaryPivot.coloredMatrixZ_eq
#print axioms MainTheory.ColoredBound.pivot_order_le
#print axioms MainTheory.ColoredBound.quantitative_colored_finite_lift
#print axioms MainTheory.SectionTwoGeneral.sectorCount_le
#print axioms MainTheory.QuantitativeGroup.quantitative_projective_group
#print axioms MainTheory.QuantitativeGroup.qMin_le_beta
#print axioms MainTheory.QuantitativeGroup.exists_sectorCount_qMin_le
#print axioms MainTheory.QuantitativeGroup.k2_q_bound

/-! ## Section III is about something -/

#print axioms MainTheory.SectionThreeNonVacuity.exists_nontrivial_six_qubit_code
#print axioms MainTheory.SectionThreeNonVacuity.completeness_applies
#print axioms MainTheory.SectionThreeNonVacuity.qMin_and_order_on_witness
