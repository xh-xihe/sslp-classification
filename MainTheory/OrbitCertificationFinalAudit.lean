import MainTheory.KernelAxiomAudit
import MainTheory.Orbit2FullImage
import MainTheory.Orbit3FullImage
import MainTheory.Orbit2SpectralTable
import SixQubit.Generated.Orbit2PhysicalSpectra
import MainTheory.GateGCD
import MainTheory.DiagonalMomentBridge
import MainTheory.NumberDetectionBridge
import MainTheory.RationalSectionSteps
import MainTheory.BinaryFeatureMoments
import MainTheory.FiniteGateCanonicalNormalization
import MainTheory.DiagonalProofSteps
import MainTheory.SevenQubitLogicalAction
import MainTheory.CommonMeanReplacement
import MainTheory.PositiveAffineMoments
import MainTheory.PositiveAffineFunctionExpansion
import MainTheory.D3OriginalRealPivot
import MainTheory.SmallTransversalOrders
import MainTheory.QuaternionSpinMatrices
import MainTheory.QuaternionProjectiveOrders
import MainTheory.QuaternionProjectiveSurjectivity
import MainTheory.QuaternionAxisConjugation
import MainTheory.QuaternionAxisFrames
import MainTheory.QuaternionAxisAngles
import MainTheory.SmallTransversalClifford
import MainTheory.Orbit2StrictBlocks
import MainTheory.Orbit2GenericRigidity
import MainTheory.SmallNonCliffordMinimum
import MainTheory.Orbit2ActiveProjectorRank
import MainTheory.Orbit2RemainingCoordinates
import MainTheory.Orbit2QuarticContractions
import MainTheory.Orbit2PrintedJContractions
import MainTheory.Orbit2PrintedCContractions
import MainTheory.Orbit2PrintedQuartic
import MainTheory.Orbit2FullGramMatrix
import MainTheory.Orbit2PrintedRigidity
import MainTheory.Orbit2TrigonometricSplit
import MainTheory.Orbit2PhysicalMarginals
import MainTheory.RationalSchurStep
import MainTheory.Orbit2PrintedPurityMasses
import MainTheory.Orbit2PrintedActiveMasses
import MainTheory.Orbit2StandardSeedBridge
import MainTheory.Orbit2OutsideActiveLow
import MainTheory.Orbit2PrintedPlane
import MainTheory.Orbit2ProductMarginal
import MainTheory.Orbit2PrintedNormalization
import MainTheory.Orbit2PauliReflectionEnergy
import MainTheory.Orbit3NormalizedMoment
import MainTheory.Orbit21UnsignedClasses
import MainTheory.Orbit45PrintedMoments
import MainTheory.Orbit45PrintedConsequences
import MainTheory.Orbit45TrianglePolynomial

/-! Final actual-encoder roots and exhaustive finite certificate bindings. -/

#certification_axioms [
  MainTheory.Orbit2ProductMarginal.conditional_coefficient,
  MainTheory.Orbit2ProductMarginal.product_marginal,
  MainTheory.Orbit2PrintedNormalization.purification_norm,
  MainTheory.Orbit2PrintedNormalization.mass,
  MainTheory.Orbit2PrintedNormalization.magic_fixed,
  MainTheory.Orbit2PrintedNormalization.Q_isometry,
  MainTheory.Orbit2PrintedNormalization.Q_projector,
  MainTheory.Orbit2PrintedPlane.full_plane,
  MainTheory.Orbit2PrintedEnumeratorMasses.low_enumerators,
  MainTheory.Orbit2PauliReflection.involution,
  MainTheory.Orbit2PauliReflection.support_counts,
  MainTheory.Orbit2PauliReflection.expansion,
  MainTheory.Orbit2PauliReflectionEnergy.coefficient_real,
  MainTheory.Orbit2PauliReflectionEnergy.trace_enumerator,
  MainTheory.FiniteCubicTensorTrace.positive,
  MainTheory.FiniteCubicTensorTrace.trace,
  MainTheory.Orbit3NormalizedMoment.norm_one,
  MainTheory.Orbit3NormalizedMoment.expectation,
  MainTheory.Orbit3NormalizedMoment.positive,
  MainTheory.Orbit3NormalizedMoment.trace_one,
  MainTheory.Orbit3NormalizedMoment.normalized_gram,
  MainTheory.Orbit3NormalizedMoment.factor_positive,
  MainTheory.Orbit3NormalizedMoment.table_positive,
  MainTheory.Orbit2PrintedActiveMasses.pattern_counts,
  MainTheory.Orbit2PrintedActiveMasses.active_partition,
  MainTheory.Orbit2PrintedActiveMasses.purity_one_named,
  MainTheory.Orbit2PrintedActiveMasses.purity_two_named,
  MainTheory.Orbit2StandardFiveQubit.ground_construction,
  MainTheory.Orbit2StandardFiveQubit.rotation_clifford,
  MainTheory.Orbit2StandardSeedBridge.code_pure_KL,
  MainTheory.Orbit2StandardSeedBridge.normalized_transport,
  MainTheory.Orbit2OutsideActiveLow.coefficient_zero,
  MainTheory.Orbit2PrintedPurityMasses.reference_h,
  MainTheory.Orbit2PrintedPurityMasses.purity_h,
  MainTheory.Orbit2PrintedPurityMasses.purity_sos,
  MainTheory.Orbit2PhysicalMarginals.active_density,
  MainTheory.Orbit2PhysicalMarginals.spectator_density,
  MainTheory.Orbit2PhysicalMarginals.active_commutes,
  MainTheory.Orbit2PhysicalMarginals.literal_parity_rank,
  MainTheory.RationalSchurStep.completed_square,
  MainTheory.RationalSchurStep.positive_pivot,
  MainTheory.Orbit2QuarticContractions.weighted_c13,
  MainTheory.Orbit2QuarticContractions.weighted_c33,
  MainTheory.Orbit2QuarticContractions.c13_real,
  MainTheory.Orbit2QuarticContractions.c33_real,
  MainTheory.Orbit2PrintedJContractions.exact_incidence,
  MainTheory.Orbit2PrintedJContractions.printed_J_weights,
  MainTheory.Orbit2PrintedCContractions.weighted_multiplier,
  MainTheory.Orbit2PrintedQuartic.Q_identity,
  MainTheory.Orbit2PrintedQuartic.coefficient_identity,
  MainTheory.Orbit2PrintedQuartic.coercivity,
  MainTheory.Orbit2FullGramMatrix.symmetric,
  MainTheory.Orbit2FullGramMatrix.zero_rows,
  MainTheory.Orbit2FullGramMatrix.matrix_identity,
  MainTheory.Orbit2PrintedRigidity.J_zero,
  MainTheory.Orbit2PrintedRigidity.constrained_Q,
  MainTheory.Orbit2PrintedRigidity.printed_inequality,
  MainTheory.Orbit2TrigonometricSplit.isometry,
  MainTheory.Orbit2TrigonometricSplit.logical_lift,
  MainTheory.Orbit2TrigonometricSplit.projection,
  MainTheory.Orbit2TrigonometricSplit.low_enumerators,
  MainTheory.Orbit2TrigonometricSplit.enumerator,
  MainTheory.Orbit2RemainingCoordinates.covered,
  MainTheory.Orbit2RemainingCoordinates.unique,
  MainTheory.Orbit2RemainingCoordinates.family_mass,
  MainTheory.Orbit2RemainingCoordinates.coercivity,
  MainTheory.SmallNonCliffordMinimum.minimum_attained,
  MainTheory.CliffordProjectiveOrder.bounded_order,
  MainTheory.CliffordProjectiveOrder.order_five_no_clifford_basis,
  MainTheory.QuaternionCliffordTrace.allowed_trace,
  MainTheory.Orbit2ActiveProjectorRank.projector,
  MainTheory.Orbit2GenericRigidity.rigidity,
  MainTheory.Orbit2GenericRigidity.pauli_set_counts,
  MainTheory.SmallTransversalClifford.bool_unitary,
  MainTheory.SmallTransversalClifford.common_basis,
  MainTheory.BoundedProjectiveCliffordGroup.common_basis,
  MainTheory.QuaternionCliffordMatrixBridge.normalizer_clifford,
  MainTheory.QuaternionCliffordMatrixBridge.same_action,
  MainTheory.QuaternionBoundedGroup.bounded_group,
  MainTheory.QuaternionQuarterGroup.quarter_group,
  MainTheory.QuaternionThirdAxisGroup.shared_axis,
  MainTheory.QuaternionThirdOrbit.third_pair_nonparallel,
  MainTheory.QuaternionThirdPair.perpendicular_pair,
  MainTheory.QuaternionThirdGroup.pauli_frame,
  MainTheory.QuaternionHalfTurnGroup.half_turn_group,
  MainTheory.QuaternionThirdTraceFrame.third_half_frame,
  MainTheory.QuaternionThirdCanonicalTargets.bodyHalf_action,
  MainTheory.QuaternionCommutingThird.cyclic_part,
  MainTheory.QuaternionQuarterAxisGroup.shared_axis,
  MainTheory.QuaternionQuarterPair.common_frame,
  MainTheory.QuaternionQuarterPlane.plane_normalizes,
  MainTheory.QuaternionRationalNormalizer.rational_normalizes,
  MainTheory.QuaternionOrthogonalFrame.ordered_frame,
  MainTheory.QuaternionAxisGeometry.quarter_related,
  MainTheory.QuaternionCliffordAxes.normalizes_of_two,
  MainTheory.QuaternionAxisNormalizerShape.quarter_root_I,
  MainTheory.QuaternionConjugatedSubgroup.rotated_bounded,
  MainTheory.Orbit2StrictBlocks.certificate_strict,
  MainTheory.Orbit2StrictBlocks.physical_strict,
  MainTheory.QuaternionSpinMatrices.spin_mul,
  MainTheory.QuaternionSpinMatrices.spin_star,
  MainTheory.QuaternionSpinMatrices.projective_kernel,
  MainTheory.QuaternionSpinMatrices.projective_pow,
  MainTheory.QuaternionProjectiveOrders.allowed_of_projective_order,
  MainTheory.QuaternionProjectiveSurjectivity.scalar_unitary,
  MainTheory.QuaternionProjectiveSurjectivity.adjoint_surjective,
  MainTheory.QuaternionAxisConjugation.conjugate_axis,
  MainTheory.QuaternionAxisFrames.any_axis,
  MainTheory.QuaternionAxisAngles.quarter_relative_dot,
  MainTheory.QuaternionAxisAngles.third_relative_dot,
  MainTheory.Orbit21UnsignedClasses.classes_count,
  MainTheory.Orbit21UnsignedClasses.representative_exists,
  MainTheory.Orbit45PrintedFibers.bit_transport,
  MainTheory.Orbit45PrintedFibers.full_fibers,
  MainTheory.Orbit45PrintedFibers.reverse_sign,
  MainTheory.Orbit45PrintedMoments.probabilities,
  MainTheory.Orbit45PrintedMoments.actual_rows,
  MainTheory.Orbit45PrintedMoments.kernel_dimension,
  MainTheory.Orbit45PrintedMoments.rank_seventeen,
  MainTheory.Orbit45PrintedMoments.minor_determinant,
  MainTheory.Orbit45PrintedWalsh.actual_rows,
  MainTheory.Orbit45PrintedWalsh.kernel_iff,
  MainTheory.Orbit45PrintedWalsh.rank_seven,
  MainTheory.Orbit45PrintedWalsh.minor_absolute_determinant,
  MainTheory.Orbit45PrintedAttainment.canonical_bottom,
  MainTheory.Orbit45PrintedAttainment.canonical_top,
  MainTheory.Orbit45PrintedAttainment.full_kl,
  MainTheory.Orbit45PrintedAttainment.normalized,
  MainTheory.Orbit45PrintedConsequences.fixed_mass,
  MainTheory.Orbit45PrintedConsequences.triangle_bounds,
  MainTheory.Orbit45PrintedConsequences.triangle_phases,
  MainTheory.Orbit45TrianglePolynomial.lower_equality,
  MainTheory.Orbit45TrianglePolynomial.upper_equality,
  MainTheory.Orbit45TrianglePolynomial.interval,
  MainTheory.Orbit45TrianglePolynomial.path_domain,
  MainTheory.Orbit45TrianglePolynomial.path_parameter,
  MainTheory.DiagonalAdjointOrder.intrinsic_order,
  MainTheory.DiagonalAdjointOrder.scalar_order,
  MainTheory.DiagonalAdjointOrder.normalized_intrinsic_order,
  MainTheory.SmallTransversalOrders.bounded_order,
  MainTheory.D3OriginalRealPivot.shifted_eigen,
  MainTheory.D3OriginalRealPivot.for_eigenframe,
  MainTheory.D3OriginalRealPivot.intrinsicClass_of_sameProjective,
  MainTheory.D3OriginalRealPivot.full_sparse_bound,
  MainTheory.PositiveAffineFunctionExpansion.expansion,
  MainTheory.PositiveAffineFunctionExpansion.affineSpan_eq_of_coordinate_squares,
  MainTheory.PositiveAffineMoments.zero_transfer,
  MainTheory.PositiveAffineMoments.affineSpan_le,
  MainTheory.PositiveAffineMoments.affineSpan_eq,
  MainTheory.CommonMeanReplacement.support_value,
  MainTheory.CommonMeanReplacement.replacement_on_supported_union,
  MainTheory.CommonMeanReplacement.replacement_on_direct_sum,
  MainTheory.SevenQubitExampleStates.hasDistance_two,
  MainTheory.SevenQubitExampleStates.not_hasDistance_three,
  MainTheory.SevenQubitExampleStates.first_moments,
  MainTheory.SevenQubitPrintedStates.state0_printed,
  MainTheory.SevenQubitPrintedStates.state1_printed,
  MainTheory.SevenQubitExampleProjector.preserving_phases,
  MainTheory.SevenQubitExampleProjector.real_kernel,
  MainTheory.SevenQubitLogicalCharacter.projectiveEquiv,
  MainTheory.SevenQubitMinimumOrder.logical_order,
  MainTheory.SevenQubitMinimumOrder.twelve_dvd_representative,
  MainTheory.SevenQubitMinimumOrder.minimum_physical_order,
  MainTheory.SevenQubitMinimumOrder.physical_order,
  MainTheory.SevenQubitRationalFamily.family_infinite_order,
  MainTheory.SevenQubitRationalFamily.direction_identity,
  MainTheory.SevenQubitRationalFamily.family_class,
  MainTheory.SevenQubitLogicalAction.family_eigenvalues,
  MainTheory.DiagonalProofSteps.real_conjugation_entry,
  MainTheory.DiagonalProofSteps.hamiltonian_commutator,
  MainTheory.DiagonalProofSteps.hamiltonian_scalar,
  MainTheory.DiagonalProofSteps.kernel_direction_scalar,
  MainTheory.DiagonalProofSteps.preserving_integer_matrix_iff,
  MainTheory.DiagonalProofSteps.real_projective_replacement,
  MainTheory.FiniteGateCanonicalNormalization.common_divisor_phase_zero,
  MainTheory.BinaryFeatureMoments.average_iff_binary_moments,
  MainTheory.BinaryFeatureMoments.average_iff_character_moments,
  MainTheory.BinaryFeatureMoments.average_eq_of_distance,
  MainTheory.BinaryFeatureMoments.average_eq_fiber,
  MainTheory.FiniteGateCanonicalNormalization.primitive_addOrder,
  MainTheory.FiniteGateCanonicalNormalization.supplied_primitive_gate,
  MainTheory.DiagonalMomentBridge.binary_iff_character_moments,
  MainTheory.DiagonalMomentBridge.character_eq_product,
  MainTheory.DiagonalMomentBridge.diagonal_action,
  MainTheory.DiagonalMomentBridge.fiber_probability_sum,
  MainTheory.NumberDetectionBridge.single_site_iff,
  MainTheory.NumberDetectionBridge.all_sites_iff,
  MainTheory.RationalSectionSteps.cast_num_mulVec_div_den,
  MainTheory.RationalSectionSteps.rational_section_chain,
  MainTheory.RationalSectionSteps.gram_quadratic_form,
  MainTheory.RationalSectionSteps.gram_euclidean_norm,
  MainTheory.GateGCD.primitive_iff_gcd,
  MainTheory.Orbit2FullImage.logicalZ,
  MainTheory.Orbit2FullImage.actual_enumerator,
  MainTheory.Orbit2FullImage.actual_A3_zero,
  MainTheory.Orbit2FullImage.exact_distance_three,
  MainTheory.Orbit2FullImage.directory_image,
  MainTheory.Orbit3TargetInterpretation.term_eq_sum,
  MainTheory.Orbit3TargetInterpretation.target_eq_raw,
  MainTheory.Orbit3TargetInterpretation.collected_sum,
  SixQubit.Generated.Orbit3TargetData.coverage,
  SixQubit.Generated.Orbit3TargetData.target_coefficients,
  SixQubit.Generated.Orbit3CollectedTarget.all_evaluations,
  SixQubit.Generated.Orbit3CollectedKLRows.all_kl_primitive_rows_zero,
  SixQubit.Generated.Orbit3CollectedSpinRows.all_spin_primitive_rows_zero,
  SixQubit.Generated.Orbit3CollectedHadamardRows.all_hadamard_primitive_rows_zero,
  MainTheory.Orbit3FullImage.all_primitive_rows_zero,
  MainTheory.Orbit3FullImage.target_coordinates,
  MainTheory.Orbit3FullImage.target_zero,
  MainTheory.Orbit3FullImage.actual_A3_zero,
  MainTheory.Orbit3FullImage.exact_distance_three,
  MainTheory.Orbit3FullImage.actual_enumerator,
  MainTheory.Orbit3FullImage.directory_image,
  MainTheory.RationalSpectralCertificate.charpoly_of_similarity,
  MainTheory.Orbit2SpectralTable.counts_correct,
  MainTheory.Orbit2SpectralTable.number_of_blocks,
  MainTheory.Orbit2SpectralTable.number_of_coordinates,
  MainTheory.Orbit2SpectralTable.all_polynomials,
  SixQubit.Generated.Orbit2PhysicalSpectra.physical_dimensions,
  SixQubit.Generated.Orbit2PhysicalSpectra.physical_characteristic_polynomials
]
