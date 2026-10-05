# Prose review of the 20261003 manuscripts

Review status: **partial**.

Explicit review of the frozen 20261003 main source and current SI. Reviewed prose blocks bind their exact current line ranges and kernel-inspected physical theorem types. All other running text still requires review. Five author-held main issues remain gaps; the main source is unchanged. No source-wide coverage is inherited.

This is a version-bound review record, not a successful kernel run.
No previous-version coverage is transferred. No manuscript text is reproduced.

Generated from `results/prose-review-20261003.json`.

## main.tex:172 — gap

Author-held frozen main issue: the introductory diagonal-group finiteness claim needs the fixed-product-basis and single-site detection hypotheses used by the actual theorem.


## main.tex:269 — gap

Author-held frozen main issue: probability moment rows implement diagonal Z detection; full X/Y KL conditions also involve complex phases.


## main.tex:274 — gap

Author-held frozen main issue: the unrestricted Singleton statement includes rank one and is false there. The repository carries both the corrected rank-at-least-two theorem and a kernel counterexample. A proof of a corrected statement cannot certify this frozen wording.


## main.tex:684 — gap

Author-held frozen main issue: rational homogeneous replacement preserves the specified image/kernel information; this must not be read as equality of the entire homogeneous component.


## main.tex:1825 — gap

Author-held frozen main issue: physical-order minimization in this sentence has a broader representative scope than the reduced diagonal definition used by its corresponding result.


## supplementary.tex:4369 — covered

The literal cat coefficients give two orthonormal actual physical columns under the printed real quadratic parameter constraint.

- `MainTheory.PrimitiveOrderTwoCatEncoder.encoder_apply`
- `MainTheory.PrimitiveOrderTwoCatEncoder.encoder_isometry`

## supplementary.tex:4373 — covered

The actual five-cat embedding kills all nonidentity single-site Paulis. The only nonzero two-site types are ZZ and equal XX/YY; constructive support classification exhausts all weight-at-most-two labels.

- `MainTheory.PrimitiveOrderTwoCatCompression.cats`
- `MainTheory.PrimitiveOrderTwoCatCompression.single_zero`
- `MainTheory.PrimitiveOrderTwoCatCompression.ZZ`
- `MainTheory.PrimitiveOrderTwoCatCompression.XX_YY`
- `MainTheory.PrimitiveOrderTwoCatCompression.mixed_zero`
- `MainTheory.PrimitiveOrderTwoCatKL.small_label`

## supplementary.tex:4406 — covered

Tail-only, first-site-only and first/tail Pauli factors exhaust the actual weight-at-most-two matrix compressions. The constructive proof retains all real normalized parameters and uses no nonzero individual amplitude premise or division by an amplitude.

- `MainTheory.PrimitiveOrderTwoCatKL.real_tail_KL`
- `MainTheory.PrimitiveOrderTwoCatKL.first_pauli_KL`
- `MainTheory.PrimitiveOrderTwoCatKL.one_tail_zero`
- `MainTheory.PrimitiveOrderTwoCatKL.weight_split`
- `MainTheory.PrimitiveOrderTwoCatKL.full_KL`

## supplementary.tex:4440 — covered

The actual six-qubit code projector is orthogonal to its conjugate six-Y spin flip and their product has zero trace. The subsequent enumerator conclusion is outside this reviewed prose block.

- `MainTheory.PrimitiveOrderTwoCatSpinFlip.overlap_zero`
- `MainTheory.PrimitiveOrderTwoCatSpinFlip.projectors_orthogonal`
- `MainTheory.PrimitiveOrderTwoCatSpinFlip.spin_trace_zero`

## supplementary.tex:5607 — covered

The target identity retains arbitrary raw amplitudes and only divides by the positive common column norm. No amplitude or Schmidt coefficient is required to be nonzero.

- `MainTheory.Orbit3PrintedHomogeneousTarget.raw_expectation`
- `MainTheory.Orbit3PrintedHomogeneousTarget.homogeneous_target`

## supplementary.tex:5594 — covered

The actual six-Y bilinear is symmetric. Its same-parity terms vanish under the actual odd orbit-three involution, including zero amplitudes. The preceding shadow-saturation sentence is outside this narrowly reviewed block.

- `MainTheory.Orbit3PrintedSpinTrace.pairing_symmetric`
- `MainTheory.Orbit3PrintedSpinTrace.pairing_diagonal_zero`
- `MainTheory.Orbit3PrintedSpinTrace.raw_parity`
- `MainTheory.Orbit3PrintedSpinTrace.orbit3_odd`

## supplementary.tex:16129 — covered

The three final table stages still count the actual primitive angle records. Distinct records mapped to the same pair remain distinct in these actual survivor sets.

- `MainTheory.SupplementarySectorCountBase.recordCount`
- `MainTheory.Generated.SupplementarySectorWitnesses.coarseRecords_complete`
- `MainTheory.Generated.SupplementarySectorWitnesses.feasibleRecords_complete`
- `MainTheory.Generated.SupplementarySectorWitnesses.compatibleRecords_complete`
- `MainTheory.SupplementarySectorCounts.angle_table`

## supplementary.tex:16164 — covered

The second table counts distinct actual full labelled fibre-pair payloads after hashing, and inequivalent actual directory keys in its final column. Both q and m are retained throughout.

- `MainTheory.SupplementarySectorCountBase.pairCount`
- `MainTheory.Generated.FinitePairDistinctness.pairAtId_injective`
- `MainTheory.Generated.FiniteOrbitCertificate.directory_valid`
- `MainTheory.SupplementarySectorCounts.pair_table`

## supplementary.tex:10743 — covered

The literal two-normalization, five-first-moment and ten-second-moment matrix is checked against the actual bottom/top tail-bit coordinates. Its rational kernel is linearly equivalent to two free parameters; rank-nullity therefore proves rank fourteen. An independent affine equivalence proves that every rational solution, and only those solutions, has the printed two-parameter form. Physical real probabilities are connected separately by physical_probabilities; they are not assumed to be rational.

- `MainTheory.Orbit26PrintedMoments.actual`
- `MainTheory.Orbit26PrintedMoments.rows`
- `MainTheory.Orbit26PrintedMoments.actual_rows`
- `MainTheory.Orbit26PrintedMoments.M`
- `MainTheory.Orbit26PrintedMoments.kernel_iff`
- `MainTheory.Orbit26PrintedMoments.affine_iff`
- `MainTheory.Orbit26PrintedMoments.kernel_dimension`
- `MainTheory.Orbit26PrintedMoments.rank_fourteen`

## supplementary.tex:5925 — covered

The literal four commuting standard generators have sixteen distinct stabilizer words. Their actual common +1 eigenspace equals the range of the actual two standard seed words, whose Gram matrix is 16 I. Its complex dimension is exactly two; the low-weight syndrome argument and both actual logical Pauli actions are separately proved.

- `MainTheory.StandardFiveSyndromeDisplays.all_nonzero_unique`
- `MainTheory.StandardFiveSyndromeDisplays.low_weight_anticommutes`
- `MainTheory.StandardFiveSyndromeDisplays.generators_commute`
- `MainTheory.StandardFiveSyndromeDisplays.logical_X`
- `MainTheory.StandardFiveSyndromeDisplays.logical_anticommute`
- `MainTheory.StandardFiveJointSpace.independent_generators`
- `MainTheory.StandardFiveJointSpace.projector_checked`
- `MainTheory.StandardFiveJointSpace.seed_gram`
- `MainTheory.StandardFiveJointSpace.joint_range`
- `MainTheory.StandardFiveJointSpace.joint_dimension`

## supplementary.tex:4246 — covered

The universal complex-isometry construction, full low-weight physical KL, zero unsplit scalars and both literal trace formulas are proved for the actual normalized standard five-qubit seed.

- `MainTheory.ArbitrarySplitPerfectCode.split_pair_compression`
- `MainTheory.ArbitrarySplitPerfectCode.split_trace`
- `MainTheory.ArbitrarySplitSixQubit.code_isometry`
- `MainTheory.ArbitrarySplitSixQubit.code_KL`
- `MainTheory.ArbitrarySplitSixQubit.projector_KL`
- `MainTheory.ArbitrarySplitSixQubit.unsplit_scalar_zero`
- `MainTheory.ArbitrarySplitSixQubit.hilbert_distance_three`

## supplementary.tex:5952 — covered

All low-weight six-qubit Pauli errors are covered by the universal split-isometry proof, including the stated zero unsplit coefficients and the split-pair trace formula in this output order.

- `MainTheory.ArbitrarySplitSixQubit.code_isometry`
- `MainTheory.ArbitrarySplitSixQubit.code_KL`
- `MainTheory.ArbitrarySplitSixQubit.projector_KL`
- `MainTheory.ArbitrarySplitSixQubit.unsplit_scalar_zero`
- `MainTheory.ArbitrarySplitSixQubit.hilbert_distance_three`
- `MainTheory.ArbitrarySplitPerfectCode.split_pair_compression`
- `MainTheory.Orbit3PrintedSplitMatrices.trace_identity`

## supplementary.tex:12026 — covered

The specified minor and full moment rank are independently proved.

- `MainTheory.Orbit31PrintedMinor.real_determinant_abs`
- `SixQubit.Orbit31.momentMatrix_rank`

## supplementary.tex:12115 — covered

All actual real extreme points, and only those points, are the 204 checked primal vertices, with support counts 108 and 96.

- `MainTheory.Orbit31SupportBase.actual_rows`
- `MainTheory.Orbit31MomentVertices.extreme_points`
- `MainTheory.Orbit31MomentVertices.vertex_count`
- `MainTheory.Orbit31MomentVertices.vertex_support_counts`

## supplementary.tex:12122 — covered

Every coordinate face is the convex hull of the actual supported vertices.

- `MainTheory.Orbit31MomentFaces.convex_hull_supported_vertices`

## supplementary.tex:12124 — gap

The stated iff needs a nonempty-mask or nonempty-face hypothesis. For the empty mask the vertex union is empty, but normalization excludes an exact empty support. The repository proves the corrected iff and this boundary obstruction; the authoritative SI source is unchanged.

- `MainTheory.Orbit31RelativeInterior.relative_interior_iff_vertexUnion`
- `MainTheory.Orbit31RelativeInterior.empty_vertexUnion`
- `MainTheory.Orbit31RelativeInterior.empty_mask_no_support`

## supplementary.tex:12277 — covered

Actual synchronized phases prove the literal type-14 and type-16 exclusions. Together with the other checked literal branches only type two remains at this stage.

- `MainTheory.Orbit31ResidualTriangles.column_rectangle`
- `MainTheory.Orbit31ResidualTriangles.column_opposition`
- `MainTheory.Orbit31ResidualTriangles.three_column_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type03.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type04.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type05.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type06.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type07.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type08.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type10.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type11.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type12.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type13.physical_no_go`
- `MainTheory.Generated.Orbit31DirectTriangles.Type15.physical_no_go`
- `MainTheory.Orbit31FinalCross.Type01.no_go`
- `MainTheory.Orbit31FinalSameState.final_no_go`
- `MainTheory.Orbit31ResidualTriangles.physical_type9_no_go`
- `MainTheory.Orbit31ResidualTriangles.physical_type14_no_go`
- `MainTheory.Orbit31ResidualTriangles.physical_type16_no_go`

## supplementary.tex:12469 — covered

The printed signed minor is checked in the actual lexicographic matrix, and proves rank twenty-three.

- `MainTheory.Orbit32PrintedMinor.actual_matrix`
- `MainTheory.Orbit32PrintedMinor.real_determinant`
- `MainTheory.Orbit32PrintedMinor.full_rank`

## supplementary.tex:12513 — covered

Both directions of the complete nonnegative real normal form are proved. The twelve displayed parameters determine the entire probability vector injectively, the actual moment kernel has dimension nine, and the literal reflection squares to identity.

- `MainTheory.Orbit32PrintedMomentNormal.complete_normal_form`
- `MainTheory.Orbit32PrintedMomentNormal.parameter_injectivity`
- `MainTheory.Orbit32PrintedMinor.kernel_dimension`
- `MainTheory.Orbit32PrintedLocalAlgebra.reflection_involution`

## supplementary.tex:10265 — covered

All twelve positive block norms and nonzero vectors are proved in physical coordinates.

- `MainTheory.Orbit33PrintedBlocks.physical_norms_and_reflection`
- `MainTheory.Orbit33PrintedBlocks.physical_blocks_nonzero`

## supplementary.tex:10274 — covered

The actual character matrix, arbitrary-F quadratic forms, common reduced state and full six-block matrix reflection are checked.

- `MainTheory.Orbit33PrintedBlocks.actual_characters`
- `MainTheory.Orbit33PrintedBlocks.evaluation_formula`
- `MainTheory.Orbit33PrintedBlocks.matrix_reflection_iff`
- `MainTheory.Orbit33PhysicalReflection.physical_character_reflection`
- `MainTheory.Orbit33PhysicalReflection.physical_common_reduced_state`
- `MainTheory.Orbit33PrintedBlocks.physical_norms_and_reflection`

## supplementary.tex:10318 — covered

Both directions of the literal matrix-pair reduction, unit-vector factorization, nonzero factors and phase signs are proved.

- `MainTheory.Orbit33PrintedBlocks.rankone_rows_iff_1`
- `MainTheory.Orbit33PrintedBlocks.rankone_rows_iff_2`
- `MainTheory.Orbit33PrintedBlocks.physical_rankone_pairs`
- `MainTheory.Orbit33NormalizedPairs.physical_normalized_pairs`

## supplementary.tex:10348 — covered

All nine actual reciprocal pairs and both far-block orthogonality relations are derived from physical cross KL.

- `MainTheory.Orbit33PrintedBlocks.cross_incidence`
- `MainTheory.Orbit33PrintedBlocks.cross_weight`
- `MainTheory.Orbit33PrintedBlocks.physical_complete_cross`
- `MainTheory.Orbit33NormalizedPairs.divided_cross`
- `MainTheory.Orbit33NormalizedPairs.physical_far_orthogonal`

## supplementary.tex:10385 — covered

The two projector sums, half-identity reduced state, perpendicular unit vectors, rank-one reduced state and final contradiction are separately exposed.

- `MainTheory.Orbit33ProjectorArgument.physical_near_and_far_sums`
- `MainTheory.Orbit33ProjectorArgument.physical_projector_sums`
- `MainTheory.Orbit33ProjectorArgument.physical_unit_orthogonality`
- `MainTheory.Orbit33ProjectorArgument.physical_all_bottom_outers`
- `MainTheory.Orbit33ProjectorArgument.physical_rho_projector`
- `MainTheory.Orbit33ProjectorArgument.physical_no_go`

## supplementary.tex:10079 — covered

The physical star-to-grid rows, common active phase and rectangle permanent reduction retain all zero-amplitude boundaries.

- `MainTheory.OrderFiveGridRemainingDisplays.Orbit38.physical_hub`
- `MainTheory.OrderFiveGridRemainingDisplays.Orbit38.physical_common_phase`
- `MainTheory.OrderFiveGridRemainingDisplays.Orbit38.physical_rectangle`
- `MainTheory.OrderFiveGridRemainingDisplays.Orbit38.physical_permanents`

## supplementary.tex:10106 — covered

Actual positive row and column masses and all permanents force full support in both grid rows.

- `MainTheory.GridSupportAlgebra.full_support`
- `MainTheory.OrderFiveGridRemainingDisplays.Orbit38.physical_supports_full`

## supplementary.tex:11191 — covered

The exact masses, actual six-edge rows and every physical coordinate version give the complete Walsh exclusion.

- `MainTheory.OrderFourWalshRemainingDisplays.Orbit27.physical_probabilities`
- `MainTheory.OrderFourWalshRemainingDisplays.Orbit27.determinant`
- `MainTheory.OrderFourWalshRemainingDisplays.Orbit27.AllCoordinates.physical_weight_one_zero`

## supplementary.tex:12647 — covered

All complementary probability pins and the literal SI three-mask odd cycle are separately proved.

- `MainTheory.OrderFourWalshRemainingDisplays.Orbit62.physical_probabilities`
- `MainTheory.OrderFourWalshRemainingDisplays.Orbit62.actual_complements`
- `MainTheory.OrderFourWalshRemainingDisplays.Orbit62.physical_all_nonzero`
- `MainTheory.OrderFourWalshRemainingDisplays.Orbit62.physical_phase_triangle`

## supplementary.tex:13927 — covered

The literal orbit-50 incidence and reciprocal route is checked, including the native top reversal and global Z4 row sign; one active index suffices for the unit-modulus odd triangle.

- `MainTheory.Orbit50PhysicalTriangle.physical_active`
- `MainTheory.Orbit50PhysicalTriangle.physical_reciprocals`
- `MainTheory.Orbit50PhysicalTriangle.physical_triangle`
- `MainTheory.Orbit50PhysicalTriangle.physical_no_go`
- `MainTheory.Orbit50PrintedRows.Row04.actual_characters`
- `MainTheory.Orbit50PrintedRows.Row04.rowSign`

## supplementary.tex:14050 — covered

Both actual printed kernels and the exact norm-product parameter pinning give all six fixed positive probabilities.

- `MainTheory.Orbit51PrintedRows.Row00.kernel_span`
- `MainTheory.Orbit51PrintedRows.Row01.kernel_span`
- `MainTheory.Orbit51PrintedAlgebra.printed_pin_identities`
- `MainTheory.Orbit51PrintedAlgebra.linear_pin`
- `MainTheory.Orbit51PrintedAlgebra.pin_parameters`
- `MainTheory.Orbit51PhysicalCompletion.physical_pinned_point`

## supplementary.tex:14106 — covered

The two actual synchronization systems identify both anchors even when alpha is at either boundary endpoint.

- `MainTheory.Orbit51PrintedAlgebra.partial_sync`
- `MainTheory.Orbit51PrintedAlgebra.boundary_active`
- `MainTheory.Orbit51PrintedAlgebra.anchor_sync`
- `MainTheory.Orbit51PrintedAlgebra.full_sync`
- `MainTheory.Orbit51PhysicalCompletion.physical_sync_rows`
- `MainTheory.Orbit51PhysicalCompletion.physical_full_sync`

## supplementary.tex:14149 — covered

All three physical quadrics, the explicitly nonzero ratio denominators and the literal odd-triangle contradiction are proved.

- `MainTheory.Orbit51PhysicalCompletion.quadrics_of_sync`
- `MainTheory.Orbit51PhysicalCompletion.physical_quadrics`
- `MainTheory.Orbit51PhysicalCompletion.physical_ratios`
- `MainTheory.Orbit51PrintedAlgebra.fixed_nonzero`
- `MainTheory.Orbit51PhysicalCompletion.physical_no_go`

## supplementary.tex:13750 — covered

The literal twelve mask reductions, common anchor phase and four quadrics are physically derived, including the whole closed boundary.

- `MainTheory.Orbit49PrintedAlgebra.reciprocal_rows`
- `MainTheory.Orbit49PhysicalCompletion.physical_uniform_phase`
- `MainTheory.Orbit49PhysicalCompletion.physical_four_rows`
- `MainTheory.Orbit49PhysicalCompletion.physical_quadrics`

## supplementary.tex:13821 — covered

Both parameter pinning identities, all physical pinned probabilities and the exact nonzero-ratio triangle and final contradiction are proved.

- `MainTheory.Orbit49PrintedAlgebra.norm_product`
- `MainTheory.Orbit49PrintedAlgebra.pin_parameters`
- `MainTheory.Orbit49PhysicalCompletion.physical_pinned_point`
- `MainTheory.Orbit49PrintedAlgebra.triangle_equations`
- `MainTheory.Orbit49PrintedAlgebra.triangle_determinant`
- `MainTheory.Orbit49PhysicalCompletion.physical_no_go`

## supplementary.tex:13506 — covered

The complete real two-parameter probability family and its exact domain are proved in both directions.

- `MainTheory.OrderThreePrintedMoments.Orbit47.complete_iff`
- `MainTheory.OrderThreePrintedMoments.Orbit47.physical_normal_form`

## supplementary.tex:13587 — covered

The complete real two-parameter probability family and nonnegative domain are proved; rank/minor prose is reviewed separately.

- `MainTheory.OrderThreePrintedMoments.Orbit48.complete_iff`
- `MainTheory.OrderThreePrintedMoments.Orbit48.physical_normal_form`

## supplementary.tex:13719 — covered

The complete real three-parameter probability family and all facets of its exact domain are proved.

- `MainTheory.OrderThreePrintedMoments.Orbit49.complete_iff`
- `MainTheory.OrderThreePrintedMoments.Orbit49.physical_normal_form`

## supplementary.tex:13892 — covered

The complete real four-parameter probability family and its exact nonnegative domain are proved, including the top-order reversal.

- `MainTheory.OrderThreePrintedMoments.Orbit50.complete_iff`
- `MainTheory.OrderThreePrintedMoments.Orbit50.physical_normal_form`
- `MainTheory.OrderThreePrintedMoments.Orbit50.actual_complements`

## supplementary.tex:14029 — covered

The complete real three-parameter moment cube, with every boundary, is proved in both directions.

- `MainTheory.OrderThreePrintedMoments.Orbit51.complete_iff`
- `MainTheory.OrderThreePrintedMoments.Orbit51.physical_normal_form`

## supplementary.tex:14215 — covered

The complete real two-parameter probability rectangle and its exact nonnegative domain are proved.

- `MainTheory.OrderThreePrintedMoments.Orbit52.complete_iff`
- `MainTheory.OrderThreePrintedMoments.Orbit52.physical_normal_form`

## supplementary.tex:13530 — covered

The actual X5 and X5Z1 rows, their individual zero products and the positive probability product 1/18 give the literal exclusion.

- `MainTheory.OrderThreePrintedCrossRows.Orbit47.actual_incidence`
- `MainTheory.OrderThreePrintedCrossRows.Orbit47.physical_rows`
- `MainTheory.OrderThreePrintedCrossRows.Orbit47.physical_products_zero`
- `MainTheory.OrderThreePrintedCrossRows.Orbit47.physical_first_product_positive`
- `MainTheory.OrderThreePrintedCrossRows.Orbit47.physical_no_go`

## supplementary.tex:13616 — covered

The actual X4 four-incidence Hadamard system and positive first product give the literal exclusion.

- `MainTheory.OrderThreePrintedCrossRows.Orbit48.actual_incidence`
- `MainTheory.OrderThreePrintedCrossRows.Orbit48.physical_rows`
- `MainTheory.OrderThreePrintedCrossRows.Orbit48.determinant`
- `MainTheory.OrderThreePrintedCrossRows.Orbit48.physical_products_zero`
- `MainTheory.OrderThreePrintedCrossRows.Orbit48.physical_first_product_positive`
- `MainTheory.OrderThreePrintedCrossRows.Orbit48.physical_no_go`

## supplementary.tex:14243 — covered

The actual X2 Hadamard system, two half-probability identities and positive total give a boundary-inclusive literal exclusion.

- `MainTheory.OrderThreePrintedCrossRows.Orbit52.actual_incidence`
- `MainTheory.OrderThreePrintedCrossRows.Orbit52.physical_rows`
- `MainTheory.OrderThreePrintedCrossRows.Orbit52.physical_half_relations`
- `MainTheory.OrderThreePrintedCrossRows.Orbit52.physical_squared_products`
- `MainTheory.OrderThreePrintedCrossRows.Orbit52.physical_no_go`

## supplementary.tex:13525 — covered

The actual orbit-47 23-row occupation matrix has the printed exact rank and an explicitly selected maximal minor with the printed signed determinant. Kernel-checked rectangular factors give the rank upper bound; the real nonzero minor gives the lower bound, independently of any phase exclusion.

- `MainTheory.OrderThreePrintedRanks.Orbit47.actual_matrix`
- `MainTheory.OrderThreePrintedRanks.Orbit47.rows`
- `MainTheory.OrderThreePrintedRanks.Orbit47.columns`
- `MainTheory.OrderThreePrintedRanks.Orbit47.determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit47.real_determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit47.rank_exact`
- `MainTheory.OrderThreePrintedRanks.Orbit47.kernel_dimension`
- `MainTheory.OrderThreePrintedMoments.Orbit47.complete_iff`

## supplementary.tex:13613 — covered

The actual orbit-48 23-row occupation matrix has the printed exact rank and an explicitly selected maximal minor with the printed signed determinant. Kernel-checked rectangular factors give the rank upper bound; the real nonzero minor gives the lower bound, independently of any phase exclusion.

- `MainTheory.OrderThreePrintedRanks.Orbit48.actual_matrix`
- `MainTheory.OrderThreePrintedRanks.Orbit48.rows`
- `MainTheory.OrderThreePrintedRanks.Orbit48.columns`
- `MainTheory.OrderThreePrintedRanks.Orbit48.determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit48.real_determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit48.rank_exact`
- `MainTheory.OrderThreePrintedRanks.Orbit48.kernel_dimension`
- `MainTheory.OrderThreePrintedMoments.Orbit48.complete_iff`

## supplementary.tex:13739 — covered

The actual orbit-49 23-row occupation matrix has the printed exact rank and an explicitly selected maximal minor with the printed signed determinant. Kernel-checked rectangular factors give the rank upper bound; the real nonzero minor gives the lower bound, independently of any phase exclusion.

- `MainTheory.OrderThreePrintedRanks.Orbit49.actual_matrix`
- `MainTheory.OrderThreePrintedRanks.Orbit49.rows`
- `MainTheory.OrderThreePrintedRanks.Orbit49.columns`
- `MainTheory.OrderThreePrintedRanks.Orbit49.determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit49.real_determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit49.rank_exact`
- `MainTheory.OrderThreePrintedRanks.Orbit49.kernel_dimension`
- `MainTheory.OrderThreePrintedMoments.Orbit49.complete_iff`

## supplementary.tex:13920 — covered

The actual orbit-50 23-row occupation matrix has the printed exact rank and an explicitly selected maximal minor with the printed signed determinant. Kernel-checked rectangular factors give the rank upper bound; the real nonzero minor gives the lower bound, independently of any phase exclusion.

- `MainTheory.OrderThreePrintedRanks.Orbit50.actual_matrix`
- `MainTheory.OrderThreePrintedRanks.Orbit50.rows`
- `MainTheory.OrderThreePrintedRanks.Orbit50.columns`
- `MainTheory.OrderThreePrintedRanks.Orbit50.determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit50.real_determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit50.rank_exact`
- `MainTheory.OrderThreePrintedRanks.Orbit50.kernel_dimension`
- `MainTheory.OrderThreePrintedMoments.Orbit50.complete_iff`

## supplementary.tex:14047 — covered

The actual orbit-51 23-row occupation matrix has the printed exact rank and an explicitly selected maximal minor with the printed signed determinant. Kernel-checked rectangular factors give the rank upper bound; the real nonzero minor gives the lower bound, independently of any phase exclusion.

- `MainTheory.OrderThreePrintedRanks.Orbit51.actual_matrix`
- `MainTheory.OrderThreePrintedRanks.Orbit51.rows`
- `MainTheory.OrderThreePrintedRanks.Orbit51.columns`
- `MainTheory.OrderThreePrintedRanks.Orbit51.determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit51.real_determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit51.rank_exact`
- `MainTheory.OrderThreePrintedRanks.Orbit51.kernel_dimension`
- `MainTheory.OrderThreePrintedMoments.Orbit51.complete_iff`

## supplementary.tex:14241 — covered

The actual orbit-52 23-row occupation matrix has the printed exact rank and an explicitly selected maximal minor with the printed signed determinant. Kernel-checked rectangular factors give the rank upper bound; the real nonzero minor gives the lower bound, independently of any phase exclusion.

- `MainTheory.OrderThreePrintedRanks.Orbit52.actual_matrix`
- `MainTheory.OrderThreePrintedRanks.Orbit52.rows`
- `MainTheory.OrderThreePrintedRanks.Orbit52.columns`
- `MainTheory.OrderThreePrintedRanks.Orbit52.determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit52.real_determinant`
- `MainTheory.OrderThreePrintedRanks.Orbit52.rank_exact`
- `MainTheory.OrderThreePrintedRanks.Orbit52.kernel_dimension`
- `MainTheory.OrderThreePrintedMoments.Orbit52.complete_iff`

## supplementary.tex:14475 — covered

The actual 23-row occupation matrix, explicitly selected signed maximal minor, exact real rank and kernel dimension are independently proved.

- `MainTheory.OrderTwoPrintedRanks.Orbit18.bottom`
- `MainTheory.OrderTwoPrintedRanks.Orbit18.top`
- `MainTheory.OrderTwoPrintedRanks.Orbit18.actual_matrix`
- `MainTheory.OrderTwoPrintedRanks.Orbit18.rows`
- `MainTheory.OrderTwoPrintedRanks.Orbit18.columns`
- `MainTheory.OrderTwoPrintedRanks.Orbit18.determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit18.real_determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit18.rank_exact`
- `MainTheory.OrderTwoPrintedRanks.Orbit18.kernel_dimension`

## supplementary.tex:14582 — covered

The actual 23-row occupation matrix, explicitly selected signed maximal minor, exact real rank and kernel dimension are independently proved.

- `MainTheory.OrderTwoPrintedRanks.Orbit41.bottom`
- `MainTheory.OrderTwoPrintedRanks.Orbit41.top`
- `MainTheory.OrderTwoPrintedRanks.Orbit41.actual_matrix`
- `MainTheory.OrderTwoPrintedRanks.Orbit41.rows`
- `MainTheory.OrderTwoPrintedRanks.Orbit41.columns`
- `MainTheory.OrderTwoPrintedRanks.Orbit41.determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit41.real_determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit41.rank_exact`
- `MainTheory.OrderTwoPrintedRanks.Orbit41.kernel_dimension`

## supplementary.tex:14720 — covered

The actual 23-row occupation matrix, explicitly selected signed maximal minor, exact real rank and kernel dimension are independently proved.

- `MainTheory.OrderTwoPrintedRanks.Orbit42.bottom`
- `MainTheory.OrderTwoPrintedRanks.Orbit42.top`
- `MainTheory.OrderTwoPrintedRanks.Orbit42.actual_matrix`
- `MainTheory.OrderTwoPrintedRanks.Orbit42.rows`
- `MainTheory.OrderTwoPrintedRanks.Orbit42.columns`
- `MainTheory.OrderTwoPrintedRanks.Orbit42.determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit42.real_determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit42.rank_exact`
- `MainTheory.OrderTwoPrintedRanks.Orbit42.kernel_dimension`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.bottom`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.top`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.actual_matrix`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.rows`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.columns`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.real_determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.rank_exact`
- `MainTheory.OrderTwoPrintedRanks.Orbit43.kernel_dimension`

## supplementary.tex:14791 — covered

The actual 23-row occupation matrix, explicitly selected signed maximal minor, exact real rank and kernel dimension are independently proved.

- `MainTheory.OrderTwoPrintedRanks.Orbit44.bottom`
- `MainTheory.OrderTwoPrintedRanks.Orbit44.top`
- `MainTheory.OrderTwoPrintedRanks.Orbit44.actual_matrix`
- `MainTheory.OrderTwoPrintedRanks.Orbit44.rows`
- `MainTheory.OrderTwoPrintedRanks.Orbit44.columns`
- `MainTheory.OrderTwoPrintedRanks.Orbit44.determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit44.real_determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit44.rank_exact`
- `MainTheory.OrderTwoPrintedRanks.Orbit44.kernel_dimension`

## supplementary.tex:14865 — covered

The actual 23-row occupation matrix, explicitly selected signed maximal minor, exact real rank and kernel dimension are independently proved.

- `MainTheory.OrderTwoPrintedRanks.Orbit46.bottom`
- `MainTheory.OrderTwoPrintedRanks.Orbit46.top`
- `MainTheory.OrderTwoPrintedRanks.Orbit46.actual_matrix`
- `MainTheory.OrderTwoPrintedRanks.Orbit46.rows`
- `MainTheory.OrderTwoPrintedRanks.Orbit46.columns`
- `MainTheory.OrderTwoPrintedRanks.Orbit46.determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit46.real_determinant`
- `MainTheory.OrderTwoPrintedRanks.Orbit46.rank_exact`
- `MainTheory.OrderTwoPrintedRanks.Orbit46.kernel_dimension`

## supplementary.tex:14423 — covered

The complete literal orbit-18 shell and restricted-projector proof is checked from the actual physical diagonal and cross KL equations.

- `MainTheory.OrderTwoShellProjectors.Orbit18.shell_types`
- `MainTheory.OrderTwoShellProjectors.Orbit18.actual_shell_masses`
- `MainTheory.OrderTwoShellProjectors.Orbit18.shell_system`
- `MainTheory.OrderTwoShellProjectors.Orbit18.shell_solution`
- `MainTheory.OrderTwoShellProjectors.Orbit18.point_projector`
- `MainTheory.OrderTwoShellProjectors.Orbit18.physical_anchor_zero`
- `MainTheory.OrderTwoShellProjectors.Orbit18.physical_anchor_norm`
- `MainTheory.OrderTwoShellProjectors.Orbit18.physical_no_go`

## supplementary.tex:14527 — covered

The complete literal orbit-41 shell chain and four-character anchor projector are checked from the actual physical KL equations.

- `MainTheory.OrderTwoShellProjectors.Orbit41.shell_types`
- `MainTheory.OrderTwoShellProjectors.Orbit41.actual_shell_masses`
- `MainTheory.OrderTwoShellProjectors.Orbit41.shell_system`
- `MainTheory.OrderTwoShellProjectors.Orbit41.shell_chain`
- `MainTheory.OrderTwoShellProjectors.Orbit41.shell_solution`
- `MainTheory.OrderTwoShellProjectors.Orbit41.point_projector`
- `MainTheory.OrderTwoShellProjectors.Orbit41.physical_anchor_zero`
- `MainTheory.OrderTwoShellProjectors.Orbit41.physical_anchor_norm`
- `MainTheory.OrderTwoShellProjectors.Orbit41.physical_no_go`

## supplementary.tex:14700 — covered

The complete real moment normal form and literal signed ten-character system give the physical matched-flip exclusion at every boundary.

- `MainTheory.OrderTwoPrintedMoments.Orbit42.complete_iff`
- `MainTheory.OrderTwoPrintedMoments.Orbit43.complete_iff`
- `MainTheory.OrderTwoPrintedWalsh.Orbit42.determinant`
- `MainTheory.OrderTwoPrintedWalsh.Orbit42.physical_product_norm`
- `MainTheory.OrderTwoPrintedWalsh.Orbit42.physical_products_zero`
- `MainTheory.OrderTwoPrintedWalsh.Orbit42.physical_no_go`
- `MainTheory.OrderTwoPrintedWalsh.Orbit43.determinant`
- `MainTheory.OrderTwoPrintedWalsh.Orbit43.physical_product_norm`
- `MainTheory.OrderTwoPrintedWalsh.Orbit43.physical_products_zero`
- `MainTheory.OrderTwoPrintedWalsh.Orbit43.physical_no_go`

## supplementary.tex:14767 — covered

The complete real moment normal form and literal signed ten-character system give the physical matched-flip exclusion at every boundary.

- `MainTheory.OrderTwoPrintedMoments.Orbit44.complete_iff`
- `MainTheory.OrderTwoPrintedWalsh.Orbit44.determinant`
- `MainTheory.OrderTwoPrintedWalsh.Orbit44.physical_product_norm`
- `MainTheory.OrderTwoPrintedWalsh.Orbit44.physical_products_zero`
- `MainTheory.OrderTwoPrintedWalsh.Orbit44.physical_no_go`

## supplementary.tex:14843 — covered

The complete real moment normal form and literal signed ten-character system give the physical matched-flip exclusion at every boundary.

- `MainTheory.OrderTwoPrintedMoments.Orbit46.complete_iff`
- `MainTheory.OrderTwoPrintedWalsh.Orbit46.determinant`
- `MainTheory.OrderTwoPrintedWalsh.Orbit46.physical_product_norm`
- `MainTheory.OrderTwoPrintedWalsh.Orbit46.physical_products_zero`
- `MainTheory.OrderTwoPrintedWalsh.Orbit46.physical_no_go`

## supplementary.tex:6532 — covered

The printed general logical words are the actual complete-fiber indexed ket expansions.

- `MainTheory.Orbit45PhysicalPrintedRows.codewords`

## supplementary.tex:6599 — covered

The actual half-angle rows have rank seven and the literal selected seven-column minor has absolute determinant 256. Nonzero physical/printed row signs are explicitly checked.

- `MainTheory.Orbit45PrintedWalsh.rank_seven`
- `MainTheory.Orbit45PrintedWalsh.selectedRows`
- `MainTheory.Orbit45PrintedWalsh.selectedCols`
- `MainTheory.Orbit45PrintedWalsh.minor_absolute_determinant`
- `MainTheory.Orbit45PhysicalPrintedRows.physical_walsh`

## supplementary.tex:6695 — covered

The actual spin flip, complementary index pairing, zero-overlap trace and A2+A3=1 are proved for arbitrary supported physical codes, including all zero-amplitude boundaries.

- `MainTheory.Orbit45PhysicalSpinFlip.general_shadow_trace`
- `MainTheory.Orbit45PhysicalSpinFlip.physical_overlaps_zero`
- `MainTheory.Orbit45PhysicalSpinFlip.physical_spin_trace_zero`
- `MainTheory.Orbit45PhysicalSpinFlip.physical_A1_zero`
- `MainTheory.Orbit45PhysicalSpinFlip.physical_A2_A3_line`

## supplementary.tex:6783 — covered

The exact seven affine phase rows are invertible over the reals and yield the claimed physical/global phase normalization, preserving actual supports, probabilities, normalization and every physical KL equation.

- `MainTheory.Orbit45AffineGauge.actual_rows`
- `MainTheory.Orbit45AffineGauge.determinant`
- `MainTheory.Orbit45AffineGauge.solve_angles`
- `MainTheory.Orbit45AffineGauge.anchors_positive`
- `MainTheory.Orbit45PhysicalGauge.diagonal_fullKL`
- `MainTheory.Orbit45PhysicalGauge.rephase_fullKL`
- `MainTheory.Orbit45PhysicalGauge.phaseAction_fullKL`
- `MainTheory.Orbit45PhysicalGauge.physical_anchor_gauge`

## supplementary.tex:6794 — covered

Both literal gauges are constructed for every actual positive-stratum code. The top amplitudes follow from actual half-angle and paired-product equations after a unit relative logical phase; no displayed gauge is assumed.

- `MainTheory.Orbit45BottomGauge.physical_bottom_gauge`
- `MainTheory.Orbit45TopGauge.top_canonical`
- `MainTheory.Orbit45PhysicalPhaseNormalForm.physical_phase_normal_form`

## supplementary.tex:6832 — covered

Given the preceding displayed positive-stratum gauges, every actual remaining cross-KL row has the printed factorization and forces precisely the stated phases. Coverage here is conditional on those gauges; their complete arbitrary-code construction is reviewed separately.

- `MainTheory.Orbit45CrossFactors.all_cross_masks`
- `MainTheory.Orbit45CrossFactors.forced_phases`
- `MainTheory.Orbit45CrossFactors.triangle_after_gauge`
- `MainTheory.Orbit45CrossFactors.remaining_factors_zero`
- `MainTheory.Orbit45CrossFactors.Row0.substitution`
- `MainTheory.Orbit45CrossFactors.Row1.substitution`
- `MainTheory.Orbit45CrossFactors.Row2.substitution`
- `MainTheory.Orbit45CrossFactors.Row3.substitution`
- `MainTheory.Orbit45CrossFactors.Row4.substitution`
- `MainTheory.Orbit45CrossFactors.Row5.substitution`
- `MainTheory.Orbit45CrossFactors.Row0.physical_factors`
- `MainTheory.Orbit45CrossFactors.Row1.physical_factors`
- `MainTheory.Orbit45CrossFactors.Row2.physical_factors`
- `MainTheory.Orbit45CrossFactors.Row3.physical_factors`
- `MainTheory.Orbit45CrossFactors.Row4.physical_factors`
- `MainTheory.Orbit45CrossFactors.Row5.physical_factors`

## supplementary.tex:6890 — covered

The final printed canonical words are available for every actual positive-stratum solution, with the complete physical KL predicate, unchanged probabilities and literal vector triangle retained.

- `MainTheory.Orbit45PhysicalCanonicalForm.physical_canonical_form`
- `MainTheory.Orbit45PrintedAttainment.canonical_bottom`
- `MainTheory.Orbit45PrintedAttainment.canonical_top`

## supplementary.tex:6926 — covered

The complete within-fiber incidence classification, unique occupied channels and identical literal coherences on both words are proved. The printed family independently satisfies every physical distance-three KL equation.

- `MainTheory.Orbit45OrientedCoherences.all_within_masks`
- `MainTheory.Orbit45OrientedCoherences.unique_channel`
- `MainTheory.Orbit45OrientedCoherences.physical_printed_table`
- `MainTheory.Orbit45PrintedAttainment.full_kl`

## supplementary.tex:6958 — covered

Every triple in the printed triangle domain admits explicit unit phases and actual canonical logical words with full fiber support conditions, normalization, orthogonality, distance-three KL and the claimed diagonal logical action. All boundary triples are included.

- `MainTheory.Orbit45TriangleExistence.domain_phases`
- `MainTheory.Orbit45TriangleExistence.canonical_fullKL`
- `MainTheory.Orbit45TriangleExistence.every_triple_completion`
- `MainTheory.Orbit45PrintedAttainment.canonical_bottom`
- `MainTheory.Orbit45PrintedAttainment.canonical_top`
- `MainTheory.Orbit45PrintedLogicalAction.physical_logical_action`

## supplementary.tex:7018 — covered

The complete actual Pauli dressings give the stated Parseval coefficient eight and the printed off-diagonal enumerator contribution; the displayed vector triangle gives its exact polynomial reduction.

- `MainTheory.Orbit45DressingParseval.dressing_exhaustion`
- `MainTheory.Orbit45DressingParseval.parseval`
- `MainTheory.Orbit45DressingParseval.actual_bottom_value`
- `MainTheory.Orbit45DressingParseval.physical_parseval`
- `MainTheory.Orbit45PrintedOffContribution.physical_off_contribution`
- `MainTheory.Orbit45PrintedOffContribution.physical_off_reduction`

## supplementary.tex:7062 — covered

The printed probability coordinates determine the actual normalized enumerators. Every zero-product boundary is one of the three literal triples and has the actual coefficients A2=1, A3=0.

- `MainTheory.Orbit45PrintedEnumerator.printed_block_masses`
- `MainTheory.Orbit45PrintedEnumerator.physical_A2`
- `MainTheory.Orbit45PrintedEnumerator.physical_A3`
- `MainTheory.Orbit45PrintedEnumerator.physical_full_enumerators`
- `MainTheory.Orbit45PrintedEnumerator.boundary_permutations`
- `MainTheory.Orbit45PrintedEnumerator.boundary_R`
- `MainTheory.Orbit45PrintedEnumerator.physical_boundary`

## supplementary.tex:11289 — covered

The full 32-coordinate nonnegative diagonal-moment polytope has actual affine dimension eight. A checked dual certificate forces the first two bottom coordinates to zero; the remaining 30 columns have rank 22 with signed minor minus 384 and a strictly positive feasible witness. The rank calculation is explicitly tied to the native physical bit strings.

- `MainTheory.Orbit29MomentRank.Orbit29.actual_matrix`
- `MainTheory.Orbit29MomentRank.Orbit29.rank_exact`
- `MainTheory.Orbit29MomentRank.Orbit29.kernel_dimension`
- `MainTheory.Orbit29MomentPolytope.full_actual_matrix`
- `MainTheory.Orbit29MomentPolytope.real_dual`
- `MainTheory.Orbit29MomentPolytope.forced_zero`
- `MainTheory.Orbit29MomentPolytope.full_center_feasible`
- `MainTheory.Orbit29MomentPolytope.full_center_positive`
- `MainTheory.Orbit29MomentPolytope.restricted_rank`
- `MainTheory.Orbit29MomentPolytope.full_diagonal_polytope_dimension`

## supplementary.tex:11291 — covered

The printed pair reduction and every equal-probability assertion follow from the actual physical moment and non-diagonal constraints, including zero pairs.

- `MainTheory.Orbit29PhysicalPairReduction.high_parallel`
- `MainTheory.Orbit29PhysicalPairReduction.high_balanced`
- `MainTheory.Orbit29PhysicalPairReduction.bottom_balanced`
- `MainTheory.Orbit29PrintedSimplex.physical_printed_probabilities`
- `MainTheory.Orbit29PrintedSimplex.physical_domain`
- `MainTheory.Orbit29PrintedSimplex.physical_omitted_amplitudes`

## supplementary.tex:11335 — covered

The barycentric three-simplex, all fifteen exact relative interiors and the complete literal face table are checked with actual affine dimensions and signed connectivity.

- `MainTheory.Orbit29PrintedFaceAudit.literal_counts`
- `MainTheory.Orbit29PrintedFaceAudit.vertex_positive_iff`
- `MainTheory.Orbit29PrintedFaceAudit.checked_walks`
- `MainTheory.Orbit29SimplexRelativeInterior.relative_interior_iff`
- `MainTheory.Orbit29SimplexRelativeInterior.exhaustive_relative_interiors`
- `MainTheory.Orbit29SimplexDimensions.literal_face_dimensions`

## supplementary.tex:11394 — covered

Every active internal ratio has unit modulus. Physical orthogonality gives signed graph propagation, and an actual single-qubit diagonal phase normalizes all active bottom and high-top ratios with complete KL retained.

- `MainTheory.Orbit29PhysicalRatios.physical_assignment`
- `MainTheory.Orbit29PhysicalRatios.common_unit_phase`
- `MainTheory.Orbit29PhysicalPairGauge.diagonal_fullKL`
- `MainTheory.Orbit29PhysicalPairGauge.physical_pair_gauge`

## supplementary.tex:11403 — covered

The pinned anchor, positive high target and every one of the final printed Walsh equations are derived; the eta contradiction excludes all fifteen support strata.

- `MainTheory.Orbit29PrintedEta.literal_target_errors`
- `MainTheory.Orbit29PrintedEta.pinned_probability`
- `MainTheory.Orbit29PrintedEta.actual_rows`
- `MainTheory.Orbit29PrintedEta.printed_eta_equations`
- `MainTheory.Orbit29PrintedEta.active_product_nonzero`
- `MainTheory.Orbit29PrintedEta.eta_contradiction`
- `MainTheory.Orbit29PrintedEta.physical_no_go`

## Remaining review

Complete other current mathematical/prose correspondence; preserve five frozen main issues and the SI empty-mask qualification.
