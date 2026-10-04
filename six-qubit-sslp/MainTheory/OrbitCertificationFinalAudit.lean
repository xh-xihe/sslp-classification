import MainTheory.Orbit3PrintedScalarPlane
import MainTheory.KernelAxiomAudit
import MainTheory.Orbit2ActiveProjectorRank
import MainTheory.Orbit2FullGramMatrix
import MainTheory.Orbit2FullImage
import MainTheory.Orbit2GenericRigidity
import MainTheory.Orbit2OutsideActiveLow
import MainTheory.Orbit2PauliReflectionEnergy
import MainTheory.Orbit2PhysicalMarginals
import MainTheory.Orbit2PrintedActiveMasses
import MainTheory.Orbit2PrintedCContractions
import MainTheory.Orbit2PrintedJContractions
import MainTheory.Orbit2PrintedNormalization
import MainTheory.Orbit2PrintedPlane
import MainTheory.Orbit2PrintedPurityMasses
import MainTheory.Orbit2PrintedQuartic
import MainTheory.Orbit2PrintedRigidity
import MainTheory.Orbit2ProductMarginal
import MainTheory.Orbit2QuarticContractions
import MainTheory.Orbit2RemainingCoordinates
import MainTheory.Orbit2SpectralTable
import MainTheory.Orbit2StandardSeedBridge
import MainTheory.Orbit2StrictBlocks
import MainTheory.Orbit2TrigonometricSplit
import MainTheory.Orbit3FullImage
import MainTheory.Orbit3NormalizedMoment
import MainTheory.OrbitCertificationAudit
import Orbit2
import SixQubit.Generated.Orbit2PhysicalSpectra

/-! End-to-end orbit-2/3 images and their physical certificate bridges. -/

#certification_axioms [
  Orbit2.checked_polynomial_rigidity,
  Orbit2.enumerator_of_flatness_and_rigidity,
  Orbit2.commonJ_block_identity,
  Orbit2.split_isometry,
  Orbit2.split_projection,
  Orbit2.macWilliams_normal_form,
  Orbit2.alternating_shadow_identity,
  Orbit2.Encoder.macWilliams,
  Orbit2.Encoder.shadow,
  Orbit2.Frames.omega_left,
  Orbit2.Defects.frame_compressionDefect,
  Orbit2.Quartic.J_trace_shortcut,
  Orbit2.Quartic.twiceCoefficient_offblock,
  Orbit2.Quartic.Coefficient000.certified_matrix,
  Orbit2.FiveQubit.code_pure_KL,
  Orbit2.Quartic.reconstructed_polynomial_eq_certificate,
  Orbit2.SplitSeed.every_parameter_attained_exact_distance,
  Orbit2.Encoder.flat,
  Orbit2.PhysicalFlatness.target_masses_zero,
  Orbit2.TensorPauli.matrix_reconstruction,
  Orbit2.Encoder.spectatorDensity_flat,
  Orbit2.Encoder.computationalFrames_isometry,
  Orbit2.Encoder.schmidtFrame_parity,
  Orbit2.Encoder.physical_commonJ,
  Orbit2.Encoder.physicalT_equations,
  Orbit2.Encoder.A3_projector,
  Orbit2.Encoder.activeProjector_diagonal,
  Orbit2.Encoder.physicalOmega_distance_one_zero,
  Orbit2.Encoder.physicalT_support,
  Orbit2.Encoder.physicalT_expansion,
  Orbit2.Quartic.wordTrace_four_real,
  Orbit2.Encoder.A3_zero_of_T_rigidity,
  Orbit2.Encoder.enumerator_of_certificate_nonpositive,
  Orbit2.Quartic.projection_contraction_expansion,
  Orbit2.Quartic.J_contraction_expansion,
  Orbit2.Quartic.c_contraction_expansion,
  Orbit2.Quartic.physical_raw_nonpositive,
  Orbit2.Quartic.orderedPolynomial_eq_fullEnergy,
  Orbit2.Quartic.fullCoefficientEnergy_eq_certificate,
  Orbit2.Encoder.certificate_nonpositive,
  Orbit2.Encoder.enumerator,
  Orbit2.Encoder.A3_zero,
  Orbit2.Encoder.exact_distance_three,
  Orbit2.orbit2_exact_enumerator_image,
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
  MainTheory.Orbit2ActiveProjectorRank.projector,
  MainTheory.Orbit2GenericRigidity.rigidity,
  MainTheory.Orbit2GenericRigidity.pauli_set_counts,
  MainTheory.Orbit2StrictBlocks.certificate_strict,
  MainTheory.Orbit2StrictBlocks.physical_strict,
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
  MainTheory.Orbit2SpectralTable.counts_correct,
  MainTheory.Orbit2SpectralTable.number_of_blocks,
  MainTheory.Orbit2SpectralTable.number_of_coordinates,
  MainTheory.Orbit2SpectralTable.all_polynomials,
  SixQubit.Generated.Orbit2PhysicalSpectra.physical_dimensions,
  SixQubit.Generated.Orbit2PhysicalSpectra.physical_characteristic_polynomials,
  MainTheory.Orbit3PrintedScalarPlane.three_parameter,
  MainTheory.Orbit3PrintedScalarPlane.low_plane,
  MainTheory.Orbit3PrintedScalarPlane.two_parameter,
  MainTheory.Orbit3PrintedScalarPlane.domain
]
