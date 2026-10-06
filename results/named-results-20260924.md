# Named results of the 20260924 manuscripts

Generated from `results/paper-claims-20260924.json`; no manuscript text is reproduced.

Statuses are semantic-review judgements. Kernel execution and whole-manuscript acceptance
are separate checks. Partial entries list related declarations and the uncovered clauses.
Unreviewed entries have no accepted correspondence; a missing correspondence is not
by itself evidence that no proof exists. Conjectures are not proved results.

Named environments: 145. covered=16, partial=3, unreviewed=126

To regenerate: `python tools/named_results_doc.py --paper-version 20260924`.

## main.tex

### `main.tex:thm:finite-projective-group` — covered

theorem, line 677.

- `MainTheory.ZDetection.finite_intrinsicGroup_of_zDetects`
- `MainTheory.ZDetection.quantitative_projective_group_of_zDetects`
- `MainTheory.BetaExists.betaBound_betaOf`
- `MainTheory.IntrinsicAbelian.intrinsicGroup_mul_comm`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. The hypotheses are detection of each pure Z operator, not all weight-one errors. ZDetectionHypothesis supplies finite_intrinsicGroup_of_zDetects and the nonidentity primitive-lift package under exactly this hypothesis; BetaExists supplies its finite bound. The abelian quotient holds independently. The lift package carries m dividing q, and HasPrimitiveLift retains a primitive numerator and the physical representative. The older whole_of_finite requires d >= 2 and is deliberately not used as the sole justification.

### `main.tex:ex:seven-qubit-rationalization` — unreviewed

example, line 813.


_No review recorded._

### `main.tex:thm:general-sslp-normal-form` — covered

theorem, line 962.

- `MainTheory.PaperGeneralSSLP.general_sslp_normal_form`
- `MainTheory.PaperGeneralSSLP.general_sslp_converse`
- `MainTheory.SubspaceCode.codeSpan_frame`
- `MainTheory.SubspaceCode.hasDistance_iff`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.independent`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.sectorSpace_eq`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.codeSpan_eq`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.sslp_converse`

2026-09-26 arbitrary-subspace semantic review of the unchanged 20260924 source. The existing forward theorem retains the original projective class and the actual local-X/physical-permutation frame transport, sorted primitive angles, colors, multiplicities, fibers and distance. The new paper-facing converse takes arbitrary subspaces with the manuscript dimensions and full computational-basis fiber containments. Euclidean orthonormal bases are transported back to the original state type; each chosen sector spans exactly the supplied subspace. Distinct colors imply orthogonality and independence, not additional assumptions. The assembled frame spans their supremum, has dimension K, and satisfies the full KL predicate from basis-independent scalar compression for all Pauli weights strictly below d. The d=0 boundary follows from the identity Pauli and frame orthonormality, avoiding a hidden positive-distance restriction. The final ExactCode retains that same span, the literal finite diagonal gate with angle a, and an intrinsic class of exact order m. The zero color is a designated finite index; including it in the gcd does not change the gcd of the other colors. No supplied frame or assumed directness remains.

### `main.tex:cor:rank-two-sslp` — covered

corollary, line 1086.

- `MainTheory.PaperGeneralSSLP.rank_two_sslp`
- `MainTheory.PaperGeneralSSLP.rank_two_sslp_converse`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. rank_two_sslp assumes precisely a nontrivial intrinsic diagonal group and d >= 2. It gives cyclicity, finiteness and a sorted normal form with m equal to the full group cardinality, both residues, primitivity, and explicit X/permutation transport of the code. rank_two_sslp_converse supplies the reverse implication for the actual orthonormal supported pair at arbitrary length. This normal form selects the generator after the allowed unit-power normalization; zero amplitudes are allowed by the support predicate.

### `main.tex:lem:phase-sectors` — covered

lemma, line 1227.

- `MainTheory.ZDetection.phaseSectors_of_zDetects`
- `MainTheory.SectorMeanValue.sectorMean_eq_klScalar`
- `MainTheory.PhaseSectorFull.phaseSectorFull_package`
- `MainTheory.SectionTwoGeneral.phaseSectors`
- `MainTheory.SectionTwoGeneral.phaseSectors_mean`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. phaseSectors_of_zDetects and PhaseSectorFull use Z detection alone. sectorProbability is the diagonal sector projector divided by positive rank; its support is the strictly-positive locus. The package proves total mass one and common first moments. SectorMeanValue.sectorMean_eq_klScalar identifies that mean with (1-lambda_j)/2. No X/Y detection or distance assumption is imported from the stronger SectionTwoGeneral variants.

### `main.tex:lem:denominator-clearing` — covered

lemma, line 1287.

- `MainTheory.PivotSmithNormalForm.clearing_smithLastFactor`
- `MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. The preceding paragraph fixes an invertible integer pivot and its final Smith factor. clearing_smithLastFactor proves both integral scaled coordinates and divisibility of their least common denominator. nonempty_smithWitness_of_det supplies the witness from nonsingularity, with inverseDenominator_eq_smithLastFactor identifying the factor independently of the witness. This covers the added least-common-denominator sentence as well as the display.

### `main.tex:thm:colored-finite-lift` — covered

theorem, line 1319.

- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`
- `MainTheory.BinaryPivotLift.binarySolution_solves`
- `MainTheory.BinaryPivotLift.rationalLift_augmented_eq_binarySolution`
- `MainTheory.BinaryPivotLift.rationalLift_order_dvd_smithLastFactor`
- `MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det`

2026-09-26 common binary-pivot/physical-lift semantic review. The single combined theorem assumes only single-site Z detection, an actual diagonal symmetry, its real-angle representative and nontrivial intrinsic class. Its spectral resolution is the canonical one, so ell is the actual number of distinct logical eigenvalues, not an unrelated existential sector count. It chooses one nonsingular pivot P of the colored matrix and uses L=P.rationalLift throughout. Its zero-one partner uses the same rows and columns. The literal binary solution solves the selected integral-right-hand-side system, and undoing column signs and extending by zero gives exactly L.augmented. An actual normalized Smith witness W is constructed for that binary matrix, with L.order dividing W.lastFactor. The same L gives the primitive modular angle and actual symmetry in the original intrinsic class; its projective order divides L.order. The bound s<=n+ell-1, the Smith-factor beta bound and ell<=K all occur in the same conclusion. An attained minimum over HasPrimitiveLift is bounded by this very L.order and hence beta_(n+ell-1). There is no supplied pivot/Smith witness, stronger distance assumption, or separately chosen physical lift. The root uses the existing repository constructions rather than re-proving Smith existence or rationalization.

### `main.tex:def:six-sslp-orbits` — partial

definition, line 1674.

- `MainTheory.ClassificationLevels.SSLPMomentDatum`
- `MainTheory.ClassificationLevels.SSLPMomentDatum.geometry`
- `MainTheory.ClassificationLevels.actSSLPDatum`
- `MainTheory.ClassificationLevels.SSLPMomentEquivalent`
- `MainTheory.ClassificationLevels.sslpMomentSetoid`
- `MainTheory.ClassificationLevels.SSLPMomentOrbit`
- `MainTheory.ClassificationLevels.labels_eq_of_sslpMomentEquivalent`
- `MainTheory.SSLPOrbitLevels.MomentOrbit`
- `MainTheory.SSLPOrbitLevels.KSet`
- `MainTheory.SSLPOrbitLevels.IsRealizationOrbit`
- `MainTheory.SSLPOrbitLevels.RealizationOrbit`
- `MainTheory.SSLPOrbitLevels.degreeTwoFeasible_of_fiberEquivalent`
- `MainTheory.SSLPOrbitLevels.activeAffineRank_of_fiberEquivalent`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. SSLPMomentDatum/SSLPMomentEquivalent retain q,m and full fibers under the cube action; SSLPOrbitLevels.KSet is an actual normalized KL completion. The new support-dimension-bound clause is more specific than the previous geometry/active-rank wording. Its existential choice of feasible supports with a common shifted span and q <= beta_rho must be connected to the precise acceptance predicate used by the 66-key enumeration. The older quotient definitions alone do not certify that new clause.

### `main.tex:def:six-classification-levels` — partial

definition, line 1708.

- `MainTheory.ClassificationLevels.IntrinsicProjectiveDiagonalLogicalGroup`
- `MainTheory.ClassificationLevels.IntrinsicEquivalent`
- `MainTheory.SSLPOrbitLevels.RealizationOrbit`
- `MainTheory.SSLPOrbitLevels.MomentOrbit`
- `MainTheory.ClassificationLevels.WeightEnumeratorObject`
- `MainTheory.ClassificationLevels.weightEnumeratorImage`
- `MainTheory.ClassificationLevels.WeightEnumeratorEquivalent`
- `MainTheory.ClassificationLevels.LUEquivalent`
- `MainTheory.ClassificationLevels.LocalUnitaryCodeClass`
- `MainTheory.ClassificationLevelsSix.level_one_intrinsic_group`
- `MainTheory.ClassificationLevelsSix.level_two_realization_orbits`
- `MainTheory.ClassificationLevelsSix.level_three_weight_enumerators`
- `MainTheory.ClassificationLevelsSix.level_four_lu_class`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. The intrinsic group, realization objects, enumerator images and LU quotient are defined. The updated text also refers explicitly to the more restrictive bit-flip/diagonal/permutation relation and to the B-enumerator transform. The former has CodeEquiv semantics and the latter MacWilliams theorems, but their exact links to this version of eq:LU-equivalence and the stated four-level objects are not fully checked in this pass. The four level_* wrappers alone do not cover these additions.

### `main.tex:six:thm:global-status` — unreviewed

theorem, line 1794.


_No review recorded._

### `main.tex:thm:six-15-sslp-realization-orbits` — covered

theorem, line 1819.

- `MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys`
- `MainTheory.RealizationOrbits15.card_realization_orbits`
- `MainTheory.RealizationOrbits15.realizationKeys_paperIds`
- `MainTheory.RealizationOrbits15.realizationKeys_orderDistribution`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. The 66-key semantic completion predicate is normalized full distance-three KL on the actual fibers. hasCompletion_iff_mem_realizationKeys supplies both implications; realizationKeys_paperIds identifies the displayed paper IDs; card_realization_orbits and realizationKeys_orderDistribution give 15 and 11:3:1. The renamed candidate-class terminology does not assert LU classification. This checks the named conclusion on the enumerated keys; the separate general definition/support-bound correspondence remains recorded under def:six-sslp-orbits.

### `main.tex:tab:six-realizable-classes` — unreviewed

table, line 1874.


_No review recorded._

### `main.tex:thm:six-WE-status` — covered

theorem, line 1958.

- `MainTheory.WImageSettled62.all_11_realized_WImages`
- `MainTheory.ProvedWEUnion.provedImages_eq`
- `MainTheory.OpenOrbitsRealized.openKeys_hasCompletion`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. Realized11Statement explicitly contains each of the eleven displayed exact WImage equalities at the paper representatives. FI and FII unfold to the displayed L and M vectors; provedImages_eq proves their union. OpenOrbitsRealized proves nonemptiness for keys 0..3, while the text correctly leaves equality descriptions of those four sets open. No global enumerator conjecture or LU classification is being asserted or marked proved.

### `main.tex:rem:four-open-orbits` — unreviewed

remark, line 2019.


_No review recorded._

### `main.tex:thm:unique-C5-LU` — covered

theorem, line 2136.

- `MainTheory.OrderFiveOrbitMembership.exists_cubeParameter_orbit36`
- `MainTheory.OrderFiveOrbitMembership.unique_C5_LU`
- `SixQubit.Orbit36Certified.original_equivalent_canonical`
- `MainTheory.OrderFiveCodeRigidity.luEquivalent_of_orderFive`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. exists_cubeParameter_orbit36 proves membership of the source code normal form in paper class 36. original_equivalent_canonical supplies the stronger amplitude-level CodeEquiv.Equivalent on the actual representative; its generators are physical permutations, bit flips and diagonal unitaries, together with logical phases/interchange that leave the projector unchanged. unique_C5_LU and luEquivalent_of_orderFive supply the resulting LU projector statement. The code is six-qubit throughout; this does not imply a length lower bound.

### `main.tex:cor:six-C5-minimum-length` — covered

corollary, line 2149.

- `MainTheory.MinimumLengthOrderFive.minimum_length`
- `MainTheory.MinimumLengthOrderFive.canonical_attains`
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`

2026-09-26 minimum-length semantic review against the unchanged 20260924 manuscripts. All three clauses now have actual matrix-level theorems. minimum_length quantifies over arbitrary n, ExactCode n 2 d with d >= 3, arbitrary local U(2) matrices and their literal tensor-kernel action on the orthonormal encoding. Projective order five is orderOf of the faithful adjoint representation of the logical unitary; its kernel consists exactly of scalar matrices. KL-preserving ancilla padding and the exact A1 recurrence give positive A1 when n < 6. The local eigenbasis construction preserves the full distance and LU class and changes the logical matrix only by a unit scalar; the quotient/matrix bridge supplies an actual intrinsic element of order five. Six-qubit rigidity therefore forces A1 = 0. canonical_attains uses the explicit c36,d36 states, with the same logical matrix/projective-order interface; six_qubit_lu_unique_of_distance_ge_three supplies uniqueness under the actual LU relation including physical permutations. This does not certify the following full-transversal-group/Clifford prose consequence or the unqualified Singleton display.

### `main.tex:six:rem:global-family-caveat` — unreviewed

remark, line 2170.


_No review recorded._

## supplementary.tex

### `supplementary.tex:thm:six-66-orbits` — unreviewed

theorem, line 126.


_No review recorded._

### `supplementary.tex:lem:six-raw-outer-count` — unreviewed

lemma, line 196.


_No review recorded._

### `supplementary.tex:remark@281` — unreviewed

remark, line 281.


_No review recorded._

### `supplementary.tex:proposition@297` — unreviewed

proposition, line 297.


_No review recorded._

### `supplementary.tex:lem:six-primitivity-reduction` — unreviewed

lemma, line 326.


_No review recorded._

### `supplementary.tex:lem:six-nonempty-fiber-reduction` — unreviewed

lemma, line 345.


_No review recorded._

### `supplementary.tex:lem:six-fiber-hashing` — unreviewed

lemma, line 363.


_No review recorded._

### `supplementary.tex:lem:six-affine-smith-reduction` — unreviewed

lemma, line 392.


_No review recorded._

### `supplementary.tex:lem:six-moment-lp-reduction` — unreviewed

lemma, line 493.


_No review recorded._

### `supplementary.tex:lemma@612` — unreviewed

lemma, line 612.


_No review recorded._

### `supplementary.tex:lem:six-active-rank-reduction` — unreviewed

lemma, line 659.


_No review recorded._

### `supplementary.tex:lem:six-orbit-reduction` — unreviewed

lemma, line 709.


_No review recorded._

### `supplementary.tex:remark@805` — unreviewed

remark, line 805.


_No review recorded._

### `supplementary.tex:tab:66orbits` — unreviewed

longtable, line 947.


_No review recorded._

### `supplementary.tex:lem:o36allractive` — unreviewed

lemma, line 1455.


_No review recorded._

### `supplementary.tex:thm:o36rigidity` — unreviewed

theorem, line 1830.


_No review recorded._

### `supplementary.tex:thm:o7weightimage` — unreviewed

theorem, line 2001.


_No review recorded._

### `supplementary.tex:lem:o7scalarmoments` — unreviewed

lemma, line 2059.


_No review recorded._

### `supplementary.tex:lem:o7boundaryreduction` — unreviewed

lemma, line 2335.


_No review recorded._

### `supplementary.tex:lem:o7pairsum` — unreviewed

lemma, line 2524.


_No review recorded._

### `supplementary.tex:remark@2844` — unreviewed

remark, line 2844.


_No review recorded._

### `supplementary.tex:thm:o8weightimage` — unreviewed

theorem, line 2880.


_No review recorded._

### `supplementary.tex:lem:o8shells` — unreviewed

lemma, line 2920.


_No review recorded._

### `supplementary.tex:lem:o8ladder` — unreviewed

lemma, line 3050.


_No review recorded._

### `supplementary.tex:lem:o8supporttwo` — unreviewed

lemma, line 3296.


_No review recorded._

### `supplementary.tex:cor:o8raisinggram` — unreviewed

corollary, line 3494.


_No review recorded._

### `supplementary.tex:thm:o9weightimage` — unreviewed

theorem, line 3556.


_No review recorded._

### `supplementary.tex:lem:o9momentnormalform` — unreviewed

lemma, line 3611.


_No review recorded._

### `supplementary.tex:lem:o9pqequal` — unreviewed

lemma, line 3727.


_No review recorded._

### `supplementary.tex:lem:o9components` — unreviewed

lemma, line 3816.


_No review recorded._

### `supplementary.tex:lem:o9supportfour` — unreviewed

lemma, line 3910.


_No review recorded._

### `supplementary.tex:cor:o9magnitudes` — unreviewed

corollary, line 4147.


_No review recorded._

### `supplementary.tex:thm:m2-five-stabilizer-orbits` — unreviewed

theorem, line 4213.


_No review recorded._

### `supplementary.tex:thm:o21-enumerator` — unreviewed

theorem, line 4582.


_No review recorded._

### `supplementary.tex:thm:o45-weightimage` — partial

theorem, line 4617.

- `MainTheory.PaperSupplementaryImages.o45_weight_image`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. PaperSupplementaryImages.o45_weight_image proves the exact A-enumerator interval. The revised theorem now also includes a B-enumerator vector and the beta/gamma/sigma triangle parametrization. The old single declaration does not state those clauses. Their MacWilliams and full moment/phase parametrization bridges require separate checking before this expanded named theorem can be covered.

### `supplementary.tex:rem:o45-enumerator-not-LU` — unreviewed

remark, line 5324.


_No review recorded._

### `supplementary.tex:cor:m2-current-status` — unreviewed

corollary, line 5333.


_No review recorded._

### `supplementary.tex:q2fam:thm:inclusions` — covered

theorem, line 5402.

- `MainTheory.WImageOpenL.FI_subset_orbit1`
- `MainTheory.WImageOpenL.FI_subset_orbit2`
- `MainTheory.WImageOpenL.FI_subset_orbit3`
- `MainTheory.WImageOpenL.FI_subset_orbit4`
- `MainTheory.WImageOrbit4M.FII_subset_WImage_orbit1_inter_orbit4`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. The four FI inclusions target the literal mod-two angles 000111, 001111, 011111 and 111111, residues 0 and 1, matching q2fam:eq:records. Their proofs use ParityCircleImage and exact supported normalized distance-three words. WImageOrbit4M supplies the complete FII intersection for classes 1 and 4. Closed Icc intervals include both endpoints. These statements prove the inclusions and attainment by an alternative certified construction; they do not certify every step of the subsequent split-qubit narrative.

### `supplementary.tex:thm:main-result-I` — covered

theorem, line 5754.

- `MainTheory.IntrinsicOrderAudit.natCard_mem`
- `MainTheory.GeneralFiniteness.isCyclic`
- `MainTheory.SixQubitIntrinsicOrderSet.including_identity`
- `MainTheory.IntrinsicOrderAudit.orderOf_le_five`
- `MainTheory.SixQubitIntrinsicAttainment.order_five_attained`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. IntrinsicOrderAudit.natCard_mem and GeneralFiniteness.isCyclic classify each nontrivial intrinsic diagonal group. SixQubitIntrinsicOrderSet.including_identity states equality of attained element orders with {1,2,3,5}, including all lower-bound witnesses, not only a restriction. orderOf_le_five and order_five_attained establish the maximum. All refer to actual ExactCode 6 2 3 projectors and their intrinsic groups.

### `supplementary.tex:thm:main-result-II` — covered

theorem, line 5784.

- `MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys`
- `MainTheory.RealizationOrbits15.card_realization_orbits`
- `MainTheory.RealizationOrbits15.realizationKeys_paperIds`
- `MainTheory.RealizationOrbits15.realizationKeys_orderDistribution`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. The 66-key semantic completion predicate is normalized full distance-three KL on the actual fibers. hasCompletion_iff_mem_realizationKeys supplies both implications; realizationKeys_paperIds identifies the displayed paper IDs; card_realization_orbits and realizationKeys_orderDistribution give 15 and 11:3:1. The renamed candidate-class terminology does not assert LU classification. This checks the named conclusion on the enumerated keys; the separate general definition/support-bound correspondence remains recorded under def:six-sslp-orbits.

### `supplementary.tex:thm:main-result-III` — covered

theorem, line 5873.

- `MainTheory.WImageSettled62.all_11_realized_WImages`
- `MainTheory.ProvedWEUnion.provedImages_eq`
- `MainTheory.OpenOrbitsRealized.openKeys_hasCompletion`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. Realized11Statement explicitly contains each of the eleven displayed exact WImage equalities at the paper representatives. FI and FII unfold to the displayed L and M vectors; provedImages_eq proves their union. OpenOrbitsRealized proves nonemptiness for keys 0..3, while the text correctly leaves equality descriptions of those four sets open. No global enumerator conjecture or LU classification is being asserted or marked proved.

### `supplementary.tex:thm:main-result-IV` — covered

theorem, line 5955.

- `MainTheory.OrderFiveOrbitMembership.exists_cubeParameter_orbit36`
- `MainTheory.OrderFiveOrbitMembership.unique_C5_LU`
- `SixQubit.Orbit36Certified.original_equivalent_canonical`
- `MainTheory.OrderFiveCodeRigidity.luEquivalent_of_orderFive`

2026-09-26 semantic review of the 20260924 source and its surrounding definitions. exists_cubeParameter_orbit36 proves membership of the source code normal form in paper class 36. original_equivalent_canonical supplies the stronger amplitude-level CodeEquiv.Equivalent on the actual representative; its generators are physical permutations, bit flips and diagonal unitaries, together with logical phases/interchange that leave the projector unchanged. unique_C5_LU and luEquivalent_of_orderFive supply the resulting LU projector statement. The code is six-qubit throughout; this does not imply a length lower bound.

### `supplementary.tex:cor:main-order-five-minimum-length` — covered

corollary, line 5992.

- `MainTheory.MinimumLengthOrderFive.minimum_length`
- `MainTheory.MinimumLengthOrderFive.canonical_attains`
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`

2026-09-26 minimum-length semantic review against the unchanged 20260924 manuscripts. All three clauses now have actual matrix-level theorems. minimum_length quantifies over arbitrary n, ExactCode n 2 d with d >= 3, arbitrary local U(2) matrices and their literal tensor-kernel action on the orthonormal encoding. Projective order five is orderOf of the faithful adjoint representation of the logical unitary; its kernel consists exactly of scalar matrices. KL-preserving ancilla padding and the exact A1 recurrence give positive A1 when n < 6. The local eigenbasis construction preserves the full distance and LU class and changes the logical matrix only by a unit scalar; the quotient/matrix bridge supplies an actual intrinsic element of order five. Six-qubit rigidity therefore forces A1 = 0. canonical_attains uses the explicit c36,d36 states, with the same logical matrix/projective-order interface; six_qubit_lu_unique_of_distance_ge_three supplies uniqueness under the actual LU relation including physical permutations. This does not certify the following full-transversal-group/Clifford prose consequence or the unqualified Singleton display.

### `supplementary.tex:lem:twoedge` — unreviewed

lemma, line 6080.


_No review recorded._

### `supplementary.tex:thm:q9nogo` — unreviewed

theorem, line 6130.


_No review recorded._

### `supplementary.tex:cor:q9range` — unreviewed

corollary, line 6217.


_No review recorded._

### `supplementary.tex:remark@6226` — unreviewed

remark, line 6226.


_No review recorded._

### `supplementary.tex:prop:q8Ano` — unreviewed

proposition, line 6405.


_No review recorded._

### `supplementary.tex:prop:q8Bno` — unreviewed

proposition, line 6591.


_No review recorded._

### `supplementary.tex:thm:q8nogo` — unreviewed

theorem, line 6606.


_No review recorded._

### `supplementary.tex:cor:q8range` — unreviewed

corollary, line 6620.


_No review recorded._

### `supplementary.tex:remark@6633` — unreviewed

remark, line 6633.


_No review recorded._

### `supplementary.tex:prop:q7no57` — unreviewed

proposition, line 6850.


_No review recorded._

### `supplementary.tex:prop:q7no58` — unreviewed

proposition, line 7074.


_No review recorded._

### `supplementary.tex:prop:q7no59` — unreviewed

proposition, line 7136.


_No review recorded._

### `supplementary.tex:prop:q7no60` — unreviewed

proposition, line 7219.


_No review recorded._

### `supplementary.tex:prop:q7no61` — unreviewed

proposition, line 7317.


_No review recorded._

### `supplementary.tex:thm:q7nogo` — unreviewed

theorem, line 7329.


_No review recorded._

### `supplementary.tex:cor:q7range` — unreviewed

corollary, line 7343.


_No review recorded._

### `supplementary.tex:remark@7354` — unreviewed

remark, line 7354.


_No review recorded._

### `supplementary.tex:prop:q6no53` — unreviewed

proposition, line 7678.


_No review recorded._

### `supplementary.tex:prop:q6no54` — unreviewed

proposition, line 7826.


_No review recorded._

### `supplementary.tex:prop:q6no55` — unreviewed

proposition, line 8035.


_No review recorded._

### `supplementary.tex:prop:q6no56` — unreviewed

proposition, line 8237.


_No review recorded._

### `supplementary.tex:thm:q6nogo` — unreviewed

theorem, line 8249.


_No review recorded._

### `supplementary.tex:cor:q6range` — unreviewed

corollary, line 8263.


_No review recorded._

### `supplementary.tex:remark@8276` — unreviewed

remark, line 8276.


_No review recorded._

### `supplementary.tex:tab:q4status` — unreviewed

table, line 8307.


_No review recorded._

### `supplementary.tex:remark@8335` — unreviewed

remark, line 8335.


_No review recorded._

### `supplementary.tex:proposition@8503` — unreviewed

proposition, line 8503.


_No review recorded._

### `supplementary.tex:lem:q4o26Jorth` — unreviewed

lemma, line 8749.


_No review recorded._

### `supplementary.tex:lem:q4o26anchorsingular` — unreviewed

lemma, line 8770.


_No review recorded._

### `supplementary.tex:thm:q4o26nogo` — unreviewed

theorem, line 9024.


_No review recorded._

### `supplementary.tex:proposition@9094` — unreviewed

proposition, line 9094.


_No review recorded._

### `supplementary.tex:proposition@9139` — unreviewed

proposition, line 9139.


_No review recorded._

### `supplementary.tex:tab:q4o29faces` — unreviewed

table, line 9223.


_No review recorded._

### `supplementary.tex:proposition@9290` — unreviewed

proposition, line 9290.


_No review recorded._

### `supplementary.tex:lem:q4o30threepoints` — unreviewed

lemma, line 9495.


_No review recorded._

### `supplementary.tex:lem:q4o30exceptional` — unreviewed

lemma, line 9538.


_No review recorded._

### `supplementary.tex:lem:q4o30mindegree` — unreviewed

lemma, line 9596.


_No review recorded._

### `supplementary.tex:thm:q4o30nogo` — unreviewed

theorem, line 9777.


_No review recorded._

### `supplementary.tex:remark@9797` — unreviewed

remark, line 9797.


_No review recorded._

### `supplementary.tex:prop:q4o31momentnormal` — unreviewed

proposition, line 9872.


_No review recorded._

### `supplementary.tex:tab:q4o31supportorbits` — unreviewed

table, line 10018.


_No review recorded._

### `supplementary.tex:lem:q4o31permanenttriangle` — unreviewed

lemma, line 10058.


_No review recorded._

### `supplementary.tex:thm:q4o31nogo` — unreviewed

theorem, line 10235.


_No review recorded._

### `supplementary.tex:remark@10256` — unreviewed

remark, line 10256.


_No review recorded._

### `supplementary.tex:thm:q4o32nogo` — unreviewed

theorem, line 10489.


_No review recorded._

### `supplementary.tex:remark@10498` — unreviewed

remark, line 10498.


_No review recorded._

### `supplementary.tex:proposition@10563` — unreviewed

proposition, line 10563.


_No review recorded._

### `supplementary.tex:proposition@10598` — unreviewed

proposition, line 10598.


_No review recorded._

### `supplementary.tex:thm:q4nogo` — unreviewed

theorem, line 10613.


_No review recorded._

### `supplementary.tex:cor:completeorderclassification` — unreviewed

corollary, line 10627.


_No review recorded._

### `supplementary.tex:thm:m5-other-seven` — unreviewed

theorem, line 10687.


_No review recorded._

### `supplementary.tex:cor:m5-unique-unconditional` — unreviewed

corollary, line 11205.


_No review recorded._

### `supplementary.tex:prop:o5-nogo` — unreviewed

proposition, line 11247.


_No review recorded._

### `supplementary.tex:prop:o6-nogo` — unreviewed

proposition, line 11579.


_No review recorded._

### `supplementary.tex:lem:m3lift-fullrank` — unreviewed

lemma, line 11886.


_No review recorded._

### `supplementary.tex:prop:o47-nogo` — unreviewed

proposition, line 11918.


_No review recorded._

### `supplementary.tex:prop:o48-nogo` — unreviewed

proposition, line 12002.


_No review recorded._

### `supplementary.tex:prop:o49-nogo` — unreviewed

proposition, line 12136.


_No review recorded._

### `supplementary.tex:prop:o50-nogo` — unreviewed

proposition, line 12308.


_No review recorded._

### `supplementary.tex:prop:o51-nogo` — unreviewed

proposition, line 12447.


_No review recorded._

### `supplementary.tex:prop:o52-nogo` — unreviewed

proposition, line 12631.


_No review recorded._

### `supplementary.tex:thm:m3-complete-nogos` — unreviewed

theorem, line 12735.


_No review recorded._

### `supplementary.tex:cor:m3-complete-status` — unreviewed

corollary, line 12753.


_No review recorded._

### `supplementary.tex:prop:o18-nogo` — unreviewed

proposition, line 12852.


_No review recorded._

### `supplementary.tex:prop:o41-nogo` — unreviewed

proposition, line 12956.


_No review recorded._

### `supplementary.tex:lem:m2-fullrank-matching` — unreviewed

lemma, line 13058.


_No review recorded._

### `supplementary.tex:prop:o42o43-nogo` — unreviewed

proposition, line 13104.


_No review recorded._

### `supplementary.tex:prop:o44-nogo` — unreviewed

proposition, line 13182.


_No review recorded._

### `supplementary.tex:prop:o46-nogo` — unreviewed

proposition, line 13256.


_No review recorded._

### `supplementary.tex:prop:o19-nogo` — unreviewed

proposition, line 13325.


_No review recorded._

### `supplementary.tex:prop:o17-nogo` — unreviewed

proposition, line 13518.


_No review recorded._

### `supplementary.tex:prop:o20-nogo` — unreviewed

proposition, line 13714.


_No review recorded._

### `supplementary.tex:prop:o12-nogo` — unreviewed

proposition, line 13889.


_No review recorded._

### `supplementary.tex:prop:o13-nogo` — unreviewed

proposition, line 14064.


_No review recorded._

### `supplementary.tex:lem:parity4-moment` — unreviewed

lemma, line 14186.


_No review recorded._

### `supplementary.tex:lem:parity4-connectivity` — unreviewed

lemma, line 14233.


_No review recorded._

### `supplementary.tex:lem:parity4-edgeisolation` — unreviewed

lemma, line 14261.


_No review recorded._

### `supplementary.tex:lem:connected-orthogonality` — unreviewed

lemma, line 14301.


_No review recorded._

### `supplementary.tex:prop:o15-nogo` — unreviewed

proposition, line 14323.


_No review recorded._

### `supplementary.tex:prop:o24-nogo` — unreviewed

proposition, line 14375.


_No review recorded._

### `supplementary.tex:prop:o14-nogo` — unreviewed

proposition, line 14441.


_No review recorded._

### `supplementary.tex:thm:m2-fourteen-nogos` — unreviewed

theorem, line 14525.


_No review recorded._

### `supplementary.tex:cor:m2-eleven-remaining` — unreviewed

corollary, line 14546.


_No review recorded._

### `supplementary.tex:tab:angle-record-counts` — unreviewed

table, line 14569.


_No review recorded._

### `supplementary.tex:tab:fiber-pair-counts` — unreviewed

table, line 14603.


_No review recorded._

## Scope

Displayed equations and running prose require their own review.
See `results/prose-review-20260924.md` and `results/errata-20260924.json`.
