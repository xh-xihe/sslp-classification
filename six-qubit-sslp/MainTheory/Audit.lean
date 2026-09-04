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
import MainTheory.InterchangeTransport
import MainTheory.D3BoundedNormalForm
import MainTheory.SSLPCompleteness
import MainTheory.PrimitiveReduction
import MainTheory.QMinBound
import MainTheory.FiniteProjectiveGroup
import MainTheory.MomentEquivalence
import MainTheory.SectionThreeNonVacuity
import MainTheory.CodeFiberBridge
import MainTheory.Generated.FiniteOrbitCertificate
import MainTheory.OrderFourNoCompletion
import MainTheory.OrderSevenNoCompletion
import MainTheory.OrderRange
import MainTheory.DirectoryOrbitStatus
import MainTheory.MaskRankBridge
import MainTheory.ThresholdBoundsSmall
import MainTheory.CoarseFilterEntry
import MainTheory.CoarseFilterSound
import MainTheory.Generated.CoarseRightRowsData
import MainTheory.CoarseFilterUnconditional
import MainTheory.SortedPivot
import MainTheory.SortedPivotConstruction
import MainTheory.BinaryBetaTinyLower
import MainTheory.RankThresholdBridge
import MainTheory.Generated.RankSymmetry
import MainTheory.PaperReductionChain
import MainTheory.ProvedWEUnion
import MainTheory.OpenOrbitsRealized
import MainTheory.RealizationOrbits15
import MainTheory.CodeMomentPoint
import MainTheory.RealFaceBridge
import MainTheory.CodeDirectoryEntry
import MainTheory.CodeMomentFeasible
import MainTheory.CodeActiveFace
import MainTheory.CodeRankFilter
import MainTheory.CodeOrbitKey
import MainTheory.CodeOrbitStatus
import MainTheory.PrimitiveMobius
import MainTheory.Orbit36LUBridge
import MainTheory.D3CertifiedSpectralOuterEntrance
import MainTheory.Orbit9IntrinsicRealization
import MainTheory.SixQubitIntrinsicAttainment
import MainTheory.IntrinsicProjectiveAbelian
import MainTheory.UnitPowerSemanticTransport
import MainTheory.ActiveRankRecordCount
import MainTheory.SSLPOrbitLevels
import MainTheory.ClassificationLevelsSix
import MainTheory.Generated.FiniteOrbitRankBridge
import MainTheory.GeneralFinitenessRank
import MainTheory.ProjectiveGroupGeneral
import MainTheory.RankTwoSSLPCanonical
import MainTheory.SharpSectorBound

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
#print axioms MainTheory.FiniteProjectiveGroup.lifts
#print axioms MainTheory.FiniteProjectiveGroup.whole_of_finite
#print axioms MainTheory.FiniteProjectiveGroup.whole
#print axioms MainTheory.FiniteProjectiveGroup.whole_six_qubit
#print axioms MainTheory.MomentEquivalence.charOn_stdBasis_eq_iff
#print axioms MainTheory.MomentEquivalence.charOn_stdBasis_pair_eq_iff
#print axioms MainTheory.MomentEquivalence.lp_normalization_and_positivity
#print axioms MainTheory.BetaExists.exists_betaBound
#print axioms MainTheory.DeterminantalRank.exists_nonsingular_minor
#print axioms MainTheory.PivotSize.exists_pivot_rank_le

/-! ## The paper's rank-two theorem, stated whole -/

#print axioms MainTheory.GeneralLiftOrder.liftSymmetry
#print axioms MainTheory.GeneralLiftOrder.intrinsicClass_liftSymmetry
#print axioms MainTheory.GeneralLiftOrder.sector_in_fibre
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
#print axioms MainTheory.InterchangeTransport.swapFiniteGeneratorResolution
#print axioms MainTheory.InterchangeTransport.swap_ratio
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
#print axioms MainTheory.QuantitativeGroup.qualitative_finite_lift
#print axioms MainTheory.QuantitativeGroup.quantitative_projective_group
#print axioms MainTheory.QuantitativeGroup.qMin_le_beta
#print axioms MainTheory.QuantitativeGroup.exists_sectorCount_qMin_le
#print axioms MainTheory.QuantitativeGroup.k2_q_bound

/-! ## Section III is about something -/

#print axioms MainTheory.SectionThreeNonVacuity.exists_nontrivial_six_qubit_code
#print axioms MainTheory.SectionThreeNonVacuity.completeness_applies
#print axioms MainTheory.SectionThreeNonVacuity.qMin_and_order_on_witness

/-! ## Section IV: the semantic bridge into the enumerated fibre pairs -/

#print axioms MainTheory.CodeFiberBridge.recordOf_mem
#print axioms MainTheory.CodeFiberBridge.support_mask0
#print axioms MainTheory.CodeFiberBridge.support_mask1
#print axioms MainTheory.CodeFiberBridge.code_supports_in_enumerated_fibres
#print axioms MainTheory.CodeFiberBridge.recordOf_hasSecondFiber
#print axioms MainTheory.CodeFiberBridge.recordOf_mem_nonemptyFiber

/-! ## Section IV: the 215-to-66 orbit directory -/

#print axioms MainTheory.Generated.OrbitCertificate.signature_exact
#print axioms MainTheory.Generated.OrbitCertificate.witness_valid
#print axioms MainTheory.Generated.OrbitCertificate.expectedSignatureAt_injective
#print axioms MainTheory.Generated.FiniteOrbitCertificate.directory_valid
#print axioms MainTheory.Generated.FiniteOrbitCertificate.orbit_coverage
#print axioms MainTheory.Generated.FiniteOrbitCertificate.no_ghost_key
#print axioms MainTheory.Generated.FiniteOrbitCertificate.hasExactlyClasses

/-! ## Section IV: which orders a code can carry -/

#print axioms MainTheory.OrderFourNoCompletion.noCompletion_of_orderFour
#print axioms MainTheory.OrderSevenNoCompletion.noCompletion_of_orderSeven
#print axioms MainTheory.OrderRange.logicalOrder_mem
#print axioms MainTheory.OrderRange.maxLogicalOrder_eq_five
#print axioms MainTheory.OrderRange.logicalOrders_attained
#print axioms MainTheory.OrderRange.physicalOrder_le_six
#print axioms MainTheory.OrderRange.maxPhysicalOrder_eq_six
#print axioms MainTheory.OrderRange.physicalOrders_attained

/-! ## Section IV: the completion status of all 66 keys -/

#print axioms MainTheory.DirectoryOrbitStatus.noCompletion_of_mem_noGoKeys
#print axioms MainTheory.DirectoryOrbitStatus.hasCompletion_of_mem_realizedKeys
#print axioms MainTheory.DirectoryOrbitStatus.settled_or_open
#print axioms MainTheory.DirectoryOrbitStatus.keys_partition
#print axioms MainTheory.DirectoryOrbitStatus.openKeys_paperIds
#print axioms MainTheory.DirectoryOrbitStatus.noGoKeys_paperIds
#print axioms MainTheory.DirectoryOrbitStatus.realizedKeys_paperIds

/-! ## Section IV: entering the coarse affine-rank filter -/

#print axioms MainTheory.MaskRankBridge.maskAffineRank_eq_finrank_span
#print axioms MainTheory.MaskRankBridge.residueZeroMask_affineRank_eq_span
#print axioms MainTheory.MaskRankBridge.linearIndependent_point_of_real
#print axioms MainTheory.MaskRankBridge.le_maskAffineRank_mask0
#print axioms MainTheory.MaskRankBridge.finrank_direction_image_affine
#print axioms MainTheory.MaskRankBridge.finrank_direction_bxor_image
#print axioms MainTheory.MaskRankBridge.vectorSpan_eq_span_of_zero_mem
#print axioms MainTheory.MaskRankBridge.finrank_vectorSpan_le_finrank_span
#print axioms MainTheory.MaskRankBridge.exists_nonsingular_rows
#print axioms MainTheory.CoarseFilterEntry.supportRank_le_maskAffineRank_mask0
#print axioms MainTheory.Generated.ExtraMoment.rejectRightPairs_infeasible
#print axioms MainTheory.Generated.ExtraMoment.rejectRightPairs_realInfeasible
#print axioms MainTheory.Generated.ExtraMoment.rejectRightPairs_length
#print axioms MainTheory.Generated.CoarseRightRows.rejectRight_mem
#print axioms MainTheory.CoarseFilterSound.not_s0Clause_of_rejectLeft
#print axioms MainTheory.CoarseFilterUnconditional.keepAt_of_s0_of_feasible
#print axioms MainTheory.CoarseFilterUnconditional.fullFiberCriterion_of_s0_of_feasible
#print axioms MainTheory.CoarseFilterUnconditional.exists_output_of_s0_of_feasible
#print axioms MainTheory.ThresholdBoundsSmall.betaBound_one
#print axioms MainTheory.ThresholdBoundsSmall.betaBound_two
#print axioms MainTheory.ThresholdBoundsSmall.betaBound_three
#print axioms MainTheory.ThresholdBoundsSmall.thresholdBounds
#print axioms MainTheory.SortedPivot.Pivot.rank_le_maskAffineRank
#print axioms MainTheory.SortedPivot.lcmDen_phase
#print axioms MainTheory.SortedPivot.Pivot.q_dvd_inverseDenominator
#print axioms MainTheory.SortedPivot.Pivot.rMin_le_rank
#print axioms MainTheory.SortedPivot.Pivot.s0Clause
#print axioms MainTheory.SortedPivot.angle_eq_zero_of_not_mem
#print axioms MainTheory.SortedPivot.nonempty_pivot_of_spanning
#print axioms MainTheory.SortedPivot.span_rqpoint_bxor_iff
#print axioms MainTheory.SortedPivot.span_rqpoint_of_shifted_nonsingular
#print axioms MainTheory.SortedPivot.span_rqpoint_permStr
#print axioms MainTheory.MaskRankBridge.span_rqpoint_comp
#print axioms MainTheory.MaskRankBridge.span_eq_top_of_nonsingular
#print axioms MainTheory.MaskRankBridge.finrank_direction_rqpoint_bxor
#print axioms MainTheory.MaskRankBridge.bitVec_xor
#print axioms MainTheory.SortedForm.exists_sortedNormalForm_of_generator'
#print axioms MainTheory.SortedPivotConstruction.freshMinor_det_ne_zero
#print axioms MainTheory.SortedPivotConstruction.zero_mem_normalizedSupport
#print axioms MainTheory.SortedPivotConstruction.zero_mem_sortedSupport
#print axioms MainTheory.SortedPivotConstruction.sparseAngle_eq_zero
#print axioms MainTheory.SortedPivotConstruction.exists_sortedNormalForm_pivot
#print axioms MainTheory.SortedPivotConstruction.exists_sortedNormalForm_pivot_nine
#print axioms MainTheory.SortedPivotConstruction.exists_normalForm_s0Clause
#print axioms MainTheory.SortedPivot.nonempty_pivot_of_spanning_at
#print axioms MainTheory.BinaryBetaTinyLower.betaExact_one
#print axioms MainTheory.BinaryBetaTinyLower.betaExact_two
#print axioms MainTheory.BinaryBetaTinyLower.betaExact_three
#print axioms MainTheory.BinaryBetaTinyLower.rMin_two_eq_three
#print axioms MainTheory.RankThresholdBridge.beta_eq_threshold
#print axioms MainTheory.RankThresholdBridge.q_le_beta_of_le_threshold
#print axioms MainTheory.Generated.RankSymmetry.ranks_equal
#print axioms MainTheory.PaperReductionChain.six_66_orbits
#print axioms MainTheory.PaperReductionChain.primitive_sorted_counts
#print axioms MainTheory.ProvedWEUnion.provedImages_eq
#print axioms MainTheory.OpenOrbitsRealized.openKeys_hasCompletion
#print axioms MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys
#print axioms MainTheory.RealizationOrbits15.realizationKeys_paperIds
#print axioms MainTheory.RealizationOrbits15.realizationKeys_orderDistribution
#print axioms MainTheory.RealizationOrbits15.card_realization_orbits
#print axioms MainTheory.RealizationOrbits15.settled
#print axioms MainTheory.CodeMomentPoint.exists_realFeasible
#print axioms MainTheory.RealFaceBridge.realSupport_subset_face
#print axioms MainTheory.CodeDirectoryEntry.code_enters_coarse_directory
#print axioms MainTheory.CodeMomentFeasible.code_enters_moment_stage
#print axioms MainTheory.CodeActiveFace.rank_le_activeMaskRank
#print axioms MainTheory.CodeRankFilter.compatible_of_pivot_certified
#print axioms MainTheory.CodeOrbitKey.code_reaches_orbit_key
#print axioms MainTheory.CodeOrbitStatus.code_logicalOrder_mem
#print axioms MainTheory.CodeOrbitStatus.code_in_realization_orbit
#print axioms MainTheory.CodeOrbitStatus.code_logicalOrder_le_five
#print axioms MainTheory.SortedPivotConstruction.exists_normalForm_pivot_full
#print axioms MainTheory.PrimitiveMobius.primitiveCount_eq_mobiusCount
#print axioms MainTheory.PrimitiveMobius.mobius_nine
#print axioms MainTheory.CodeOrbitStatus.code_orderFive_is_orbit36
#print axioms MainTheory.Orbit36LUBridge.original_projector_luEquivalent_canonical
#print axioms MainTheory.D3CertifiedSpectralOuterEntrance.arbitrary_code_enters_outer
#print axioms MainTheory.D3CertifiedSpectralOuterEntrance.code_with_nontrivial_diagonal_symmetry_enters_outer
#print axioms MainTheory.Orbit9IntrinsicRealization.exists_exact_six_qubit_intrinsic_order_three
#print axioms MainTheory.SixQubitIntrinsicAttainment.two_three_five_attained
#print axioms MainTheory.SixQubitIntrinsicAttainment.two_three_five_subset_attained
#print axioms MainTheory.IntrinsicProjectiveAbelian.intrinsic_group_abelian
#print axioms MainTheory.UnitPowerSemanticTransport.unitPower_ratio
#print axioms MainTheory.ActiveRankRecordCount.compatible_record_count
#print axioms MainTheory.ActiveRankRecordCount.one_more_record_than_pair
#print axioms MainTheory.SSLPOrbitLevels.card_realizationOrbit
#print axioms MainTheory.SSLPOrbitLevels.isRealizationOrbit_iff_mem
#print axioms MainTheory.SSLPOrbitLevels.realization_or_empty
#print axioms MainTheory.ClassificationLevelsSix.level_one_intrinsic_group
#print axioms MainTheory.ClassificationLevelsSix.level_two_realization_orbits
#print axioms MainTheory.ClassificationLevelsSix.level_three_weight_enumerators
#print axioms MainTheory.ClassificationLevelsSix.level_four_lu_class
#print axioms MainTheory.SSLPOrbitLevels.activeAffineRank_of_fiberEquivalent
#print axioms MainTheory.SSLPOrbitLevels.activeAffineRanks_of_fiberEquivalent
#print axioms MainTheory.SSLPOrbitLevels.degreeTwoFeasible_of_fiberEquivalent
#print axioms MainTheory.Generated.FiniteOrbitRankBridge.inputPairIds_eq_rankCompatible
#print axioms MainTheory.GeneralFinitenessRank.finite_intrinsicGroup
#print axioms MainTheory.GeneralFinitenessRank.hasBoundedRepresentation_general
#print axioms MainTheory.ProjectiveGroupGeneral.whole
#print axioms MainTheory.ProjectiveGroupGeneral.cyclic_of_rank_two
#print axioms MainTheory.ProjectiveGroupGeneral.k2_bound_and_cyclic
#print axioms MainTheory.RankTwoSSLPCanonical.rank_two_sslp_canonical
#print axioms MainTheory.SharpSectorBound.hasPrimitiveLift_le_beta_sectorCount
#print axioms MainTheory.SharpSectorBound.hasPrimitiveLift_of_rationalLift'
#print axioms MainTheory.SectionTwoGeneral.two_le_sectorCount_of_resolution
