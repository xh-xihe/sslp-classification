# Named results of the 20261003 manuscripts

Generated from `results/paper-claims-20261003.json`; no manuscript text is reproduced.

Statuses are semantic-review judgements. Kernel execution and whole-manuscript acceptance
are separate checks. Partial entries list related declarations and the uncovered clauses.
Unreviewed entries have no accepted correspondence; a missing correspondence is not
by itself evidence that no proof exists. Conjectures are not proved results.

Named environments: 161. covered=8, unreviewed=153

To regenerate: `python tools/named_results_doc.py --paper-version 20261003`.

## main.tex

### `main.tex:lem:uniform-rational-section` — covered

lemma, line 688.

- `QECC.integerMatrix_uniform_rational_lift`

20261003 current-source review (2026-10-04): The universal denominator is selected before the real solution t and its integral image b. The arbitrary finite rectangular integer-matrix theorem returns an integer a with exactly A(t-a/Q)=0, including singular and empty-dimensional cases. The separate author-held prose about the homogeneous component is not certified here.

### `main.tex:thm:finite-projective-group` — covered

theorem, line 732.

- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`
- `QECC.CodeProjector.FiniteDiagonalLogicalGroupConclusion`
- `QECC.CodeProjector.detects_real_of_hermitian`
- `QECC.PauliString.operator_hermitian`
- `QECC.PauliString.operator_singleZ`

20261003 current-source review (2026-10-04): Read the current complete theorem against its actual conclusion structure: finite group, commutativity, and for every nonidentity class a reduced code-preserving physical representative of exact q, literal common gcd one and logical order dividing q. Detection of Hermitian Z admits real scalars, so the real-vector predicate introduces no stronger manuscript hypothesis. No Lie-group premise is assumed.

### `main.tex:ex:seven-qubit-rationalization` — covered

example, line 880.

- `MainTheory.SevenQubitPrintedStates.state0_printed`
- `MainTheory.SevenQubitPrintedStates.state1_printed`
- `MainTheory.SevenQubitExampleStates.hasDistance_two`
- `MainTheory.SevenQubitExampleStates.not_hasDistance_three`
- `MainTheory.SevenQubitExampleProjector.preserving_phases`
- `MainTheory.SevenQubitExampleProjector.real_kernel`
- `MainTheory.SevenQubitLogicalCharacter.projectiveEquiv`
- `MainTheory.SevenQubitRationalFamily.family_infinite_order`
- `MainTheory.SevenQubitLogicalAction.family_eigenvalues`
- `MainTheory.SevenQubitMinimumOrder.minimum_physical_order`

20261003 current-source review (2026-10-04): The complete current example is attached to its actual seven-qubit complex states and orthogonal projector. Their displayed coefficients, full distance-two KL, distance-three obstruction, preserving circle phases, real edge kernel, projective group ZMod 6, literal family eigenvalues, irrational infinite physical order and exact minimum physical order 12 are proved for this code. The older five-qubit example is not used as a substitute.

### `main.tex:thm:general-sslp-normal-form` — covered

theorem, line 1068.

- `QECC.CodeProjector.general_sslp_canonical_normal_form`
- `QECC.CodeProjector.HasCanonicalGeneralSSLPData`
- `QECC.general_sslp_directSum_converse`

20261003 current-source review (2026-10-04): Read both directions against the current statement. The forward theorem retains the chosen projective element, produces a reduced physical representative, sorted local-X/permutation transport, all positive active-sector ranks, distinct primitive colors and the full colored fiber inclusions. The direct-sum converse constructs the actual sum projector and proves its rank, exact logical order and the supplied full target KL distance.

### `main.tex:cor:rank-two-sslp` — covered

corollary, line 1293.

- `QECC.CodeProjector.rankTwo_sslp_canonical_normal_form`
- `QECC.CodeProjector.HasCanonicalRankTwoSSLPNormalForm`
- `MainTheory.PaperGeneralSSLP.rank_two_sslp_converse`

20261003 current-source review (2026-10-04): Read the current generator normalization against the actual rank-two theorem: the fixed-basis group is finite cyclic, a reduced representative has m dividing q, and the permitted unit power/local-X/permutation/interchange operations produce orthonormal states in full fibers 0 and q/m. The converse uses full KL, not moments alone.

### `main.tex:lem:phase-sectors` — covered

lemma, line 1465.

- `MainTheory.PhaseSectorFull.phaseSectorFull_package`
- `MainTheory.SectorMeanValue.sectorMean_eq_klScalar`
- `MainTheory.NumberDetectionBridge.single_site_iff`

20261003 current-source review (2026-10-04): The rank-normalized actual projector diagonal is positive exactly on its intrinsic support and has mass one. Single-Z compression gives every coordinate mean (1-lambda_j)/2. The result applies to sectors of arbitrary positive rank.

### `main.tex:lem:common-mean-rational-replacement` — covered

lemma, line 1501.

- `MainTheory.CommonMeanReplacement.support_value`
- `MainTheory.CommonMeanReplacement.replacement_on_direct_sum`

20261003 current-source review (2026-10-04): New generic proof matches the current arbitrary supports/distributions and subspaces. A within-support constant is its probability average and equals delta dot mu. Actual physical matrix action on the full sum of supported subspaces differs by exactly exp(2*pi*i*delta dot mu); no rationality of probabilities or KL hypothesis is added.

### `main.tex:lem:denominator-clearing` — unreviewed

lemma, line 1583.


_No review recorded._

### `main.tex:thm:colored-finite-lift` — unreviewed

theorem, line 1617.


_No review recorded._

### `main.tex:lem:positive-affine-moments` — covered

lemma, line 1871.

- `MainTheory.PositiveAffineMoments.zero_transfer`
- `MainTheory.PositiveAffineMoments.affineSpan_eq`

20261003 current-source review (2026-10-04): New theorem covers arbitrary finite real point sets, of different cardinalities, with strictly positive weights. Equality of all affine squared expectations transfers their zero sets and gives equality of affine spans through the dual annihilator. It is not restricted to binary code supports.

### `main.tex:cor:d3-physical-order-bound` — unreviewed

corollary, line 1901.


_No review recorded._

### `main.tex:def:six-sslp-orbits` — unreviewed

definition, line 2145.


_No review recorded._

### `main.tex:def:six-classification-levels` — unreviewed

definition, line 2179.


_No review recorded._

### `main.tex:six:thm:global-status` — unreviewed

theorem, line 2265.


_No review recorded._

### `main.tex:thm:six-15-sslp-realization-orbits` — unreviewed

theorem, line 2290.


_No review recorded._

### `main.tex:tab:six-realizable-classes` — unreviewed

table, line 2345.


_No review recorded._

### `main.tex:thm:six-WE-status` — unreviewed

theorem, line 2429.


_No review recorded._

### `main.tex:rem:four-open-orbits` — unreviewed

remark, line 2490.


_No review recorded._

### `main.tex:thm:unique-C5-LU` — unreviewed

theorem, line 2607.


_No review recorded._

### `main.tex:cor:six-C5-minimum-length` — unreviewed

corollary, line 2620.


_No review recorded._

### `main.tex:six:rem:global-family-caveat` — unreviewed

remark, line 2641.


_No review recorded._

## supplementary.tex

### `supplementary.tex:thm:six-66-orbits` — unreviewed

theorem, line 135.


_No review recorded._

### `supplementary.tex:lem:six-raw-outer-count` — unreviewed

lemma, line 205.


_No review recorded._

### `supplementary.tex:remark@290` — unreviewed

remark, line 290.


_No review recorded._

### `supplementary.tex:proposition@306` — unreviewed

proposition, line 306.


_No review recorded._

### `supplementary.tex:lem:six-primitivity-reduction` — unreviewed

lemma, line 335.


_No review recorded._

### `supplementary.tex:lem:six-nonempty-fiber-reduction` — unreviewed

lemma, line 354.


_No review recorded._

### `supplementary.tex:lem:six-fiber-hashing` — unreviewed

lemma, line 372.


_No review recorded._

### `supplementary.tex:lem:six-affine-smith-reduction` — unreviewed

lemma, line 401.


_No review recorded._

### `supplementary.tex:lem:six-moment-lp-reduction` — unreviewed

lemma, line 502.


_No review recorded._

### `supplementary.tex:lemma@621` — unreviewed

lemma, line 621.


_No review recorded._

### `supplementary.tex:lem:six-active-rank-reduction` — unreviewed

lemma, line 668.


_No review recorded._

### `supplementary.tex:lem:six-orbit-reduction` — unreviewed

lemma, line 718.


_No review recorded._

### `supplementary.tex:remark@814` — unreviewed

remark, line 814.


_No review recorded._

### `supplementary.tex:tab:66orbits` — unreviewed

longtable, line 956.


_No review recorded._

### `supplementary.tex:lem:o36allractive` — unreviewed

lemma, line 1464.


_No review recorded._

### `supplementary.tex:thm:o36rigidity` — unreviewed

theorem, line 1839.


_No review recorded._

### `supplementary.tex:thm:o7weightimage` — unreviewed

theorem, line 2010.


_No review recorded._

### `supplementary.tex:lem:o7scalarmoments` — unreviewed

lemma, line 2068.


_No review recorded._

### `supplementary.tex:lem:o7boundaryreduction` — unreviewed

lemma, line 2344.


_No review recorded._

### `supplementary.tex:lem:o7pairsum` — unreviewed

lemma, line 2533.


_No review recorded._

### `supplementary.tex:remark@2864` — unreviewed

remark, line 2864.


_No review recorded._

### `supplementary.tex:thm:o8weightimage` — unreviewed

theorem, line 2900.


_No review recorded._

### `supplementary.tex:lem:o8shells` — unreviewed

lemma, line 2940.


_No review recorded._

### `supplementary.tex:lem:o8ladder` — unreviewed

lemma, line 3070.


_No review recorded._

### `supplementary.tex:lem:o8supporttwo` — unreviewed

lemma, line 3316.


_No review recorded._

### `supplementary.tex:cor:o8raisinggram` — unreviewed

corollary, line 3514.


_No review recorded._

### `supplementary.tex:thm:o9weightimage` — unreviewed

theorem, line 3576.


_No review recorded._

### `supplementary.tex:lem:o9momentnormalform` — unreviewed

lemma, line 3631.


_No review recorded._

### `supplementary.tex:lem:o9pqequal` — unreviewed

lemma, line 3747.


_No review recorded._

### `supplementary.tex:lem:o9components` — unreviewed

lemma, line 3836.


_No review recorded._

### `supplementary.tex:lem:o9supportfour` — unreviewed

lemma, line 3930.


_No review recorded._

### `supplementary.tex:cor:o9magnitudes` — unreviewed

corollary, line 4171.


_No review recorded._

### `supplementary.tex:thm:m2-five-stabilizer-orbits` — unreviewed

theorem, line 4238.


_No review recorded._

### `supplementary.tex:thm:o21-enumerator` — unreviewed

theorem, line 4607.


_No review recorded._

### `supplementary.tex:thm:o45-weightimage` — unreviewed

theorem, line 4642.


_No review recorded._

### `supplementary.tex:rem:o45-enumerator-not-LU` — unreviewed

remark, line 5349.


_No review recorded._

### `supplementary.tex:cor:m2-current-status` — unreviewed

corollary, line 5358.


_No review recorded._

### `supplementary.tex:o2gc:thm-image` — unreviewed

theorem, line 5418.


_No review recorded._

### `supplementary.tex:o2gc:lem-flatness` — unreviewed

lemma, line 5465.


_No review recorded._

### `supplementary.tex:o2gc:lem-commonJ` — unreviewed

lemma, line 5663.


_No review recorded._

### `supplementary.tex:o2gc:lem-edges` — unreviewed

lemma, line 5750.


_No review recorded._

### `supplementary.tex:o2gc:prop-rigidity` — unreviewed

proposition, line 5873.


_No review recorded._

### `supplementary.tex:o2gc:lem-matrix` — unreviewed

lemma, line 5958.


_No review recorded._

### `supplementary.tex:o2gc:tab-blocks` — unreviewed

table, line 6043.


_No review recorded._

### `supplementary.tex:remark@6162` — unreviewed

remark, line 6162.


_No review recorded._

### `supplementary.tex:o3gc:main` — unreviewed

theorem, line 6302.


_No review recorded._

### `supplementary.tex:o3gc:scalarlemma` — unreviewed

lemma, line 6348.


_No review recorded._

### `supplementary.tex:o3gc:cubictable` — unreviewed

table, line 6758.


_No review recorded._

### `supplementary.tex:o3gc:certlemma` — unreviewed

lemma, line 6789.


_No review recorded._

### `supplementary.tex:q2fam:thm:inclusions` — unreviewed

theorem, line 7086.


_No review recorded._

### `supplementary.tex:thm:main-result-I` — unreviewed

theorem, line 7436.


_No review recorded._

### `supplementary.tex:thm:main-result-II` — unreviewed

theorem, line 7466.


_No review recorded._

### `supplementary.tex:thm:main-result-III` — unreviewed

theorem, line 7555.


_No review recorded._

### `supplementary.tex:thm:main-result-IV` — unreviewed

theorem, line 7643.


_No review recorded._

### `supplementary.tex:cor:main-order-five-minimum-length` — unreviewed

corollary, line 7680.


_No review recorded._

### `supplementary.tex:lem:twoedge` — unreviewed

lemma, line 7768.


_No review recorded._

### `supplementary.tex:thm:q9nogo` — unreviewed

theorem, line 7818.


_No review recorded._

### `supplementary.tex:cor:q9range` — unreviewed

corollary, line 7905.


_No review recorded._

### `supplementary.tex:remark@7914` — unreviewed

remark, line 7914.


_No review recorded._

### `supplementary.tex:prop:q8Ano` — unreviewed

proposition, line 8093.


_No review recorded._

### `supplementary.tex:prop:q8Bno` — unreviewed

proposition, line 8279.


_No review recorded._

### `supplementary.tex:thm:q8nogo` — unreviewed

theorem, line 8294.


_No review recorded._

### `supplementary.tex:cor:q8range` — unreviewed

corollary, line 8308.


_No review recorded._

### `supplementary.tex:remark@8321` — unreviewed

remark, line 8321.


_No review recorded._

### `supplementary.tex:prop:q7no57` — unreviewed

proposition, line 8538.


_No review recorded._

### `supplementary.tex:prop:q7no58` — unreviewed

proposition, line 8762.


_No review recorded._

### `supplementary.tex:prop:q7no59` — unreviewed

proposition, line 8824.


_No review recorded._

### `supplementary.tex:prop:q7no60` — unreviewed

proposition, line 8907.


_No review recorded._

### `supplementary.tex:prop:q7no61` — unreviewed

proposition, line 9005.


_No review recorded._

### `supplementary.tex:thm:q7nogo` — unreviewed

theorem, line 9017.


_No review recorded._

### `supplementary.tex:cor:q7range` — unreviewed

corollary, line 9031.


_No review recorded._

### `supplementary.tex:remark@9042` — unreviewed

remark, line 9042.


_No review recorded._

### `supplementary.tex:prop:q6no53` — unreviewed

proposition, line 9366.


_No review recorded._

### `supplementary.tex:prop:q6no54` — unreviewed

proposition, line 9514.


_No review recorded._

### `supplementary.tex:prop:q6no55` — unreviewed

proposition, line 9723.


_No review recorded._

### `supplementary.tex:prop:q6no56` — unreviewed

proposition, line 9925.


_No review recorded._

### `supplementary.tex:thm:q6nogo` — unreviewed

theorem, line 9937.


_No review recorded._

### `supplementary.tex:cor:q6range` — unreviewed

corollary, line 9951.


_No review recorded._

### `supplementary.tex:remark@9964` — unreviewed

remark, line 9964.


_No review recorded._

### `supplementary.tex:tab:q4status` — unreviewed

table, line 9995.


_No review recorded._

### `supplementary.tex:remark@10023` — unreviewed

remark, line 10023.


_No review recorded._

### `supplementary.tex:proposition@10191` — unreviewed

proposition, line 10191.


_No review recorded._

### `supplementary.tex:lem:q4o26Jorth` — unreviewed

lemma, line 10437.


_No review recorded._

### `supplementary.tex:lem:q4o26anchorsingular` — unreviewed

lemma, line 10458.


_No review recorded._

### `supplementary.tex:thm:q4o26nogo` — unreviewed

theorem, line 10712.


_No review recorded._

### `supplementary.tex:proposition@10782` — unreviewed

proposition, line 10782.


_No review recorded._

### `supplementary.tex:proposition@10827` — unreviewed

proposition, line 10827.


_No review recorded._

### `supplementary.tex:tab:q4o29faces` — unreviewed

table, line 10911.


_No review recorded._

### `supplementary.tex:proposition@10978` — unreviewed

proposition, line 10978.


_No review recorded._

### `supplementary.tex:lem:q4o30threepoints` — unreviewed

lemma, line 11183.


_No review recorded._

### `supplementary.tex:lem:q4o30exceptional` — unreviewed

lemma, line 11226.


_No review recorded._

### `supplementary.tex:lem:q4o30mindegree` — unreviewed

lemma, line 11284.


_No review recorded._

### `supplementary.tex:thm:q4o30nogo` — unreviewed

theorem, line 11465.


_No review recorded._

### `supplementary.tex:remark@11485` — unreviewed

remark, line 11485.


_No review recorded._

### `supplementary.tex:prop:q4o31momentnormal` — unreviewed

proposition, line 11560.


_No review recorded._

### `supplementary.tex:tab:q4o31supportorbits` — unreviewed

table, line 11706.


_No review recorded._

### `supplementary.tex:lem:q4o31permanenttriangle` — unreviewed

lemma, line 11746.


_No review recorded._

### `supplementary.tex:thm:q4o31nogo` — unreviewed

theorem, line 11923.


_No review recorded._

### `supplementary.tex:remark@11944` — unreviewed

remark, line 11944.


_No review recorded._

### `supplementary.tex:thm:q4o32nogo` — unreviewed

theorem, line 12177.


_No review recorded._

### `supplementary.tex:remark@12186` — unreviewed

remark, line 12186.


_No review recorded._

### `supplementary.tex:proposition@12251` — unreviewed

proposition, line 12251.


_No review recorded._

### `supplementary.tex:proposition@12286` — unreviewed

proposition, line 12286.


_No review recorded._

### `supplementary.tex:thm:q4nogo` — unreviewed

theorem, line 12301.


_No review recorded._

### `supplementary.tex:cor:completeorderclassification` — unreviewed

corollary, line 12315.


_No review recorded._

### `supplementary.tex:thm:m5-other-seven` — unreviewed

theorem, line 12375.


_No review recorded._

### `supplementary.tex:cor:m5-unique-unconditional` — unreviewed

corollary, line 12893.


_No review recorded._

### `supplementary.tex:prop:o5-nogo` — unreviewed

proposition, line 12935.


_No review recorded._

### `supplementary.tex:prop:o6-nogo` — unreviewed

proposition, line 13267.


_No review recorded._

### `supplementary.tex:lem:m3lift-fullrank` — unreviewed

lemma, line 13574.


_No review recorded._

### `supplementary.tex:prop:o47-nogo` — unreviewed

proposition, line 13606.


_No review recorded._

### `supplementary.tex:prop:o48-nogo` — unreviewed

proposition, line 13690.


_No review recorded._

### `supplementary.tex:prop:o49-nogo` — unreviewed

proposition, line 13824.


_No review recorded._

### `supplementary.tex:prop:o50-nogo` — unreviewed

proposition, line 13996.


_No review recorded._

### `supplementary.tex:prop:o51-nogo` — unreviewed

proposition, line 14135.


_No review recorded._

### `supplementary.tex:prop:o52-nogo` — unreviewed

proposition, line 14319.


_No review recorded._

### `supplementary.tex:thm:m3-complete-nogos` — unreviewed

theorem, line 14423.


_No review recorded._

### `supplementary.tex:cor:m3-complete-status` — unreviewed

corollary, line 14441.


_No review recorded._

### `supplementary.tex:prop:o18-nogo` — unreviewed

proposition, line 14540.


_No review recorded._

### `supplementary.tex:prop:o41-nogo` — unreviewed

proposition, line 14644.


_No review recorded._

### `supplementary.tex:lem:m2-fullrank-matching` — unreviewed

lemma, line 14746.


_No review recorded._

### `supplementary.tex:prop:o42o43-nogo` — unreviewed

proposition, line 14792.


_No review recorded._

### `supplementary.tex:prop:o44-nogo` — unreviewed

proposition, line 14870.


_No review recorded._

### `supplementary.tex:prop:o46-nogo` — unreviewed

proposition, line 14944.


_No review recorded._

### `supplementary.tex:prop:o19-nogo` — unreviewed

proposition, line 15013.


_No review recorded._

### `supplementary.tex:prop:o17-nogo` — unreviewed

proposition, line 15206.


_No review recorded._

### `supplementary.tex:prop:o20-nogo` — unreviewed

proposition, line 15402.


_No review recorded._

### `supplementary.tex:prop:o12-nogo` — unreviewed

proposition, line 15577.


_No review recorded._

### `supplementary.tex:prop:o13-nogo` — unreviewed

proposition, line 15752.


_No review recorded._

### `supplementary.tex:lem:parity4-moment` — unreviewed

lemma, line 15874.


_No review recorded._

### `supplementary.tex:lem:parity4-connectivity` — unreviewed

lemma, line 15921.


_No review recorded._

### `supplementary.tex:lem:parity4-edgeisolation` — unreviewed

lemma, line 15949.


_No review recorded._

### `supplementary.tex:lem:connected-orthogonality` — unreviewed

lemma, line 15989.


_No review recorded._

### `supplementary.tex:prop:o15-nogo` — unreviewed

proposition, line 16011.


_No review recorded._

### `supplementary.tex:prop:o24-nogo` — unreviewed

proposition, line 16063.


_No review recorded._

### `supplementary.tex:prop:o14-nogo` — unreviewed

proposition, line 16129.


_No review recorded._

### `supplementary.tex:thm:m2-fourteen-nogos` — unreviewed

theorem, line 16213.


_No review recorded._

### `supplementary.tex:cor:m2-eleven-remaining` — unreviewed

corollary, line 16234.


_No review recorded._

### `supplementary.tex:tab:angle-record-counts` — unreviewed

table, line 16258.


_No review recorded._

### `supplementary.tex:tab:fiber-pair-counts` — unreviewed

table, line 16292.


_No review recorded._

## Scope

Displayed equations and running prose require their own review.
See `results/prose-review-20261003.md` and `results/errata-20261003.json`.
