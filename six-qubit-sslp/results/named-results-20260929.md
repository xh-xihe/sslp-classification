# Named results of the 20260929 manuscripts

Generated from `results/paper-claims-20260929.json`; no manuscript text is reproduced.

Statuses are semantic-review judgements. Kernel execution and whole-manuscript acceptance
are separate checks. Partial entries list related declarations and the uncovered clauses.
Unreviewed entries have no accepted correspondence; a missing correspondence is not
by itself evidence that no proof exists. Conjectures are not proved results.

Named environments: 149. covered=13, partial=11, unreviewed=125

To regenerate: `python tools/named_results_doc.py --paper-version 20260929`.

## main.tex

### `main.tex:lem:uniform-rational-section` — covered

lemma, line 688.

- `QECC.integerMatrix_uniform_rational_lift`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. For an integer s-by-n matrix A, the lemma gives one positive integer Q_A, depending only on A, such that every real t with integral image At can be moved into the real kernel of A by subtracting a/Q_A for some integer vector a. QECC.integerMatrix_uniform_rational_lift states this for an integer matrix with arbitrary finite row and column index types: there is a natural number Q > 0 such that for every real t and integer vector b with At = b there is an integer a with A(t - a/Q) = 0. The quantifier order matches, since Q is fixed before t, and integrality of At is expressed through b. The Lean proof follows the paper's route: a rational generalized inverse of the transpose of A times A, clearing its denominators with Matrix.den, and equality of kernels over the reals. The docstring describes the conclusion loosely (it says the image is unchanged), but the statement itself is correct.

### `main.tex:thm:finite-projective-group` — covered

theorem, line 732.

- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`
- `QECC.CodeProjector.FiniteDiagonalLogicalGroupConclusion`
- `QECC.CodeProjector.DetectsSingleZ`
- `QECC.CodeProjector.detects_real_of_hermitian`
- `QECC.PauliString.operator_hermitian`
- `QECC.PauliString.operator_singleZ`
- `QECC.ReducedDiagonalRepresentative`
- `QECC.ReducedDiagonalRepresentative.commonGCD`
- `QECC.CodeProjector.ProjectiveDiagonalGroup`
- `QECC.CodeProjector.projectiveClassMap`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The theorem assumes that a rank-K projector detects every single-site Z_j and concludes that G_diag(P) is finite and abelian, and that each nonidentity element of projective order m has a code-preserving physical representative D(a;q) in reduced form (q >= 2, gcd(q,a) = 1) of exact physical order q, with m dividing q. QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives assumes only C.DetectsSingleZ for C : CodeProjector n K and returns FiniteDiagonalLogicalGroupConclusion, whose fields groupFinite, commutes and representative carry the three claims. For U nonzero, representative gives a ReducedDiagonalRepresentative R (q >= 2, residue vector of exact additive order q) with R.phase preserving the code, projectiveClassMap of it equal to U, R.commonGCD = 1 (gcd of q and the canonical numerators in [0,q)), orderOf (diagonalGate R.phase) = R.q, and addOrderOf U dividing R.q. Notation: m is addOrderOf U, q is R.q, D(a;q) is diagonalGate R.phase, and G_diag(P) is the quotient model checked under eq:Gdiag. DetectsSingleZ asks for real lambda_j while the paper leaves them as scalars; this is not a stronger hypothesis, and the reduction is proved in Lean. QECC.CodeProjector.detects_real_of_hermitian turns a complex detection scalar of a Hermitian operator into a real one (P = 0 included), and Z_j is Hermitian by QECC.PauliString.operator_hermitian with QECC.PauliString.operator_singleZ; choosing a real scalar for each j gives DetectsSingleZ, the same argument as in detectsSingleZ_of_hasDistanceAtLeast_two. Lean works in the computational basis, which is the paper's fixed product basis after relabelling.

### `main.tex:ex:seven-qubit-rationalization` — partial

example, line 880.

- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`
- `QECC.CodeProjector.actsAsScalar_of_edgeMatrix_mulVec_eq_zero`
- `MainTheory.DiagonalInfinitesimal.one_parameter_scalar`
- `QECC.CodeProjector.minimalPhysicalOrder`
- `QECC.CodeProjector.projectiveOrder_dvd_minimalPhysicalOrder`
- `MainTheory.FiveQubitRationalization.fully_certified`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. Example III.3 builds a rank-two seven-qubit code from two logical states with disjoint computational supports T0 and T1. It verifies the Z_j detection hypothesis of thm:finite-projective-group through a common first moment, shows distance exactly two, and computes T_P, ker_R A_P = R v and G_diag isomorphic to Z_6. It shows that the order-six action (m = 6) has q_min = 12, and that the irrational-t members of the family have infinite physical order. No Lean module defines this code or anything computed from it. There is no CodeProjector 7 2 built from these states, no detection or distance proof for it, and no evaluation of preservingPhases, the edgeMatrix kernel, ProjectiveDiagonalGroup or minimalPhysicalOrder for it. I searched every .lean file in the repository for the support strings, the vectors v and theta_0, Z_6 or ZMod 12 models and q_min = 12, and found none. The cited declarations are only the generic machinery the example illustrates. They are the III.A theorem; the kernel-direction step, where QECC exports only that some scalar exists and MainTheory.DiagonalInfinitesimal.one_parameter_scalar exports the explicit scalar exp(2 pi i t h.mu) for MainTheory's projector type; q_min as minimalPhysicalOrder U; and the generic m | q_min. The closest concrete counterpart is MainTheory.FiveQubitRationalization.fully_certified, for the five-qubit example of an older draft. It witnesses an infinite-order preserving family with finite projective order, but there q_min = 3 = m, so it carries no clause of this example and does not show a strict gap. No Lean statement for any code proves q_min > m; Lean has only m | q_min and q_min >= 2. I re-derived all the arithmetic and it is correct. One phrase is loose: subtracting tv from theta(t) gives theta_0, but the generic rational section in the theorem's proof need not land exactly on theta_0, and no conclusion depends on that. The status is partial because the status set has no 'uncovered' value. Not carried: Every example-specific clause: the code itself; mu and the resulting Z_j detection; PX_jP = PY_jP = 0 and distance exactly two; the reduction of preservation to constancy on T0 and T1; T_P; v.x = 0 and ker_R A_P = R v; D(uv)P = P; the logical action of theta_{alpha,beta}; chi and G_diag isomorphic to Z_6; theta_0 reduced with exact order 12; the action of theta(t) with m = 6 and infinite order for irrational t; the congruence 3a+4b = 1 mod 6 and 12 | q; q_min = 12 > 6 = m; and the closing remark that a search at q = m misses this action.

### `main.tex:thm:general-sslp-normal-form` — covered

theorem, line 1068.

- `QECC.CodeProjector.general_sslp_canonical_normal_form`
- `QECC.CodeProjector.HasCanonicalGeneralSSLPData`
- `QECC.CodeProjector.general_sslp_normal_form`
- `QECC.CodeProjector.GeneralSSLPData`
- `QECC.CodeProjector.two_le_card_activeResidue_of_projectiveClass_ne_zero`
- `QECC.reindexOperator_xor_diagonalGate_phaseHom`
- `QECC.reindexOperator_coordinate_diagonalGate_phaseHom`
- `MainTheory.PaperGeneralSSLP.general_sslp_normal_form`
- `MainTheory.GeneralColoredConverse.ColoredFrame.two_le_sectorCount`
- `MainTheory.PaperGeneralSSLP.general_sslp_converse`
- `QECC.general_sslp_directSum_converse`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The forward half says that a distance-at-least-2 code with a nonzero projective diagonal class of order m>1 is, after an X^t conjugation, a qubit permutation and removal of a scalar, presented by reduced data (q,a) with ell>=2 distinct labels in Z_m (first label 0, gcd one), positive multiplicities summing to K, and eigenspaces of those dimensions inside the fibers at (q/m)gamma. QECC.CodeProjector.general_sslp_canonical_normal_form returns, for one common witness, a reduced representative R together with GeneralSSLPData (class_eq ties R's gate to the given U; m = addOrderOf U divides R.q; R.q>=2; colors gamma on C.ActiveResidue R.a that are injective, zero at the anchor and have colorGCD 1; positive sector finranks summing to K) and one pair (t, sigma) with t in the anchor fiber. For that pair it records the canonical vector permuteCoefficient sigma (xorCoefficient t R.a), whose vals are monotone (and lie in [0,q) by ZMod.val) with gcd one and physical order q. It also records canonical sectors at colorEmbed(gamma b) = (q/m)gamma with the original dimensions, exhaustive labels, primitive transported colors, and preserved projective order and distance. Here ell = Fintype.card (C.ActiveResidue R.a). ell>=2 is not a packaged field, but two_le_card_activeResidue_of_projectiveClass_ne_zero states it for the same R; its hypothesis follows from class_eq and U != 0. The conjugation and the discarded scalar are explicit in reindexOperator_xor_diagonalGate_phaseHom and reindexOperator_coordinate_diagonalGate_phaseHom, applied to the same t and sigma. MainTheory.PaperGeneralSSLP.general_sslp_normal_form independently carries the forward half, with T.intrinsic = g, explicit frame transport and 2<=m; ColoredFrame.two_le_sectorCount then gives ell>=2. For the converse, MainTheory.PaperGeneralSSLP.general_sslp_converse takes exactly the paper's data on arbitrary subspaces (dimension k_alpha, literal span-of-fiber inclusion) plus basis-independent KL on their supremum below d. It returns independence, finrank K, an ExactCode spanning the sum, and the literal D(a;q) at omega = exp(2 pi i/q) whose induced class has order exactly m. Its extra hypothesis 2<=m follows from the ell>=2 distinct labels in Z_m, which belong to the theorem's data; QECC.general_sslp_directSum_converse is an operator-level variant that takes orthogonality as an input field.

### `main.tex:cor:rank-two-sslp` — covered

corollary, line 1293.

- `QECC.CodeProjector.rankTwo_sslp_canonical_normal_form`
- `QECC.CodeProjector.HasCanonicalRankTwoSSLPNormalForm`
- `QECC.CodeProjector.HasRankTwoCanonicalNormalization`
- `QECC.CodeProjector.rankTwo_sslp_normal_form`
- `QECC.natCard_eq_addOrderOf_of_generator`
- `QECC.CodeProjector.projectiveDiagonalGroup_finite`
- `QECC.CodeProjector.exists_projectiveDiagonalGroup_zmod_model`
- `QECC.CodeProjector.phaseSectorDecomposition`
- `QECC.CodeProjector.sum_finrank_activeResidue`
- `MainTheory.PaperGeneralSSLP.rank_two_sslp`
- `MainTheory.SSLPConverse.codeOfPair`
- `MainTheory.SSLPConverse.orderOf_intrinsicClass_resolutionOfPair`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The corollary concerns a two-dimensional code of distance at least two whose projective diagonal group is nontrivial. It asserts four things. The group is cyclic of order m. A generator has a reduced finite-order representative D(a;q) with q >= 2 and m | q. After X conjugation, a qubit permutation and a unit power (the scalar and state-swap freedoms are also allowed), the code has an orthonormal eigenbasis supported in the fibers at residues 0 and q/m, with a sorted and primitive. Conversely, an orthonormal fiber-supported pair that satisfies the full KL system spans a code on which D(a;q) has projective order m. QECC.CodeProjector.rankTwo_sslp_canonical_normal_form takes exactly the paper's hypotheses (CodeProjector n 2, HasDistanceAtLeast d, 2 <= d, a nonzero class). It returns IsAddCyclic, a generating class U, m = addOrderOf U with 2 <= m, a ReducedDiagonalRepresentative R of U with m | R.q, and HasRankTwoCanonicalNormalization for R.a. The paper's m = |G| follows from natCard_eq_addOrderOf_of_generator, applied to this U with finiteness from projectiveDiagonalGroup_finite, and exists_projectiveDiagonalGroup_zmod_model gives G ≅ ZMod m. The canonical record fixes the normalized vector rankTwoCanonicalCoefficient u t sigma R.a (a unit u mod q, an X string t and a permutation sigma) and the transported code rankTwoCanonicalCode t sigma. It states sorted residues, gcd one, exact physical order q, preservation, one-dimensional transported sectors at residues 0 and q/m that exhaust the active residues, projective order m, and preservation of every distance bound. phaseSector is the code intersected with the fiber subspace, and the code is the direct sum of its sectors (phaseSectorDecomposition, sum_finrank_activeResidue). So unit vectors in the two lines form the orthonormal eigenbasis, with zero amplitudes allowed; MainTheory.PaperGeneralSSLP.rank_two_sslp also states such a frame literally. For the converse, MainTheory.SSLPConverse.codeOfPair turns an orthonormal pair with SS.HasDistance into an ExactCode n 2 d. orderOf_intrinsicClass_resolutionOfPair then shows that the class of the gate with angle a has order exactly m, assuming m | q, 2 <= m and Gate.Primitive; the last is the gcd clause of eq:a-canonical, which is part of the displayed form. The scalar and state-swap freedoms are never used, so the Lean form is stronger.

### `main.tex:lem:phase-sectors` — covered

lemma, line 1465.

- `MainTheory.ZDetection.phaseSectors_of_zDetects`
- `MainTheory.PhaseSectorFull.phaseSectorFull_package`
- `MainTheory.ZDetection.resolution_zDetects`
- `MainTheory.ZDetection.ZDetectsFrame`
- `MainTheory.SectorMeanValue.sectorMean_eq_klScalar`
- `QECC.CodeProjector.phaseSectors_positive_probability_commonFirstMoments`
- `QECC.CodeProjector.detectsNumberOps_of_detectsSingleZ`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The lemma assumes single-site Z detection for a code preserved by a real D(theta). It asserts that p_alpha has positive entries summing to one on T_alpha and that all sectors share the mean vector mu, with mu_j = (1 - lambda_j)/2. MainTheory.ZDetection.phaseSectors_of_zDetects takes an ExactCode with arbitrary d; for d <= 1 the bundled distance predicate is only orthonormality. Its other hypotheses are ZDetectsFrame (the Z_j Knill-Laflamme equation on the frame, equivalent to P Z_j P = lambda_j P) and forward preservation of the code by the real gate, which is weaker than the paper's D P D^dagger = P. On the code's resolution it proves nonnegativity, total mass one, nonempty and disjoint supports, the phase congruence and a common mean vector. Strict positivity on T_alpha holds by the definition of sectorSupport. Because sectorProbability vanishes off the support, its whole-cube sums equal the paper's sums over T_alpha. SectorMeanValue.sectorMean_eq_klScalar, applied to the same decomposition with hZ from ZDetection.resolution_zDetects, gives every sector mean as (1 - klScalar_j)/2. Here klScalar_j is the Z_j constant of an orthonormal basis of the code, which is the paper's lambda_j, so mu is explicit. QECC proves the same clauses only for sectors of a modular gate D(a;q); its mu is the number-operator constant, which detectsNumberOps_of_detectsSingleZ produces as (1 - lambda_j)/2.

### `main.tex:lem:common-mean-rational-replacement` — partial

lemma, line 1501.

- `QECC.weighted_sum_eq_of_constant_on_positive_support`
- `QECC.weighted_realSupportWeight`
- `QECC.realSupportWeightLinear`
- `QECC.realSupportWeightLinear_bitVector`
- `MainTheory.WithinSectorCodeAction.code_action`
- `MainTheory.WithinSectorCodeAction.sector_action`
- `MainTheory.WithinSectorCodeAction.commonShift`
- `MainTheory.PhaseSectorFull.sectorMean_eq_of_ZDetects`
- `MainTheory.WithinSectorRationalization.common_phase_shift`
- `MainTheory.WithinSectorRationalization.same_projective_action`
- `QECC.CodeProjector.sectorConstants_eq_of_commonFirstMoments`
- `QECC.CodeProjector.actsAsScalar_realVectorPhase_sub_of_sameSectorEquations_of_commonFirstMoments`
- `QECC.CodeProjector.rationalVectorPhase_same_projectiveClass_of_sameSectorEquations_of_commonFirstMoments`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. The lemma takes sets T_alpha of bit strings carrying distributions with a common mean mu, spaces E_alpha whose vectors are supported on T_alpha, and arbitrary real theta and theta'. The lemma does not introduce E_alpha itself; its proof calls them the logical eigenspaces. Under either reading, T_alpha, p_alpha and theta are arbitrary and no detection is assumed. It concludes three things: Delta.x = Delta.mu on the union; D(theta') = e^{2 pi i Delta.mu} D(theta) on the direct sum; and preservation with the same projective action. First conclusion. Carried in the abstract setting by the chain spelled out at displaymath@1516. Second conclusion. Lean states it with the explicit scalar, but only for code sectors. MainTheory.WithinSectorCodeAction.code_action gives realGateEnd theta' f = phaseExp(commonShift) realGateEnd theta f for every f in an exact code's span. It assumes a LogicalSectorResolution, ZDetects of its sectors and the within-sector system. sector_action gives the same on each frame vector of any sector decomposition. commonShift is sum_j Delta_j times the base-sector first moment, which sectorMean_eq_of_ZDetects makes the common mean, and phaseExp phi is exp(2 pi i phi). same_projective_action and the QECC actsAsScalar and rationalVectorPhase theorems are weaker or modular-sector forms: an unnamed scalar, or preservation and equal projective class for rational solutions. The abstract clause is not carried by any declaration. QECC.CodeProjector.actsAsScalar_of_exact_edges is generic in the projector, but it assumes number-operator detection on the whole projector, gives only an existential circle scalar, and works with circle-valued diagonal gates. Every carrier requires Z detection, with T_alpha the actual sector supports and p_alpha the projector distributions. Those hypotheses are stronger than the lemma's. Not carried: Two clauses are not carried. (1) The restricted-gate identity D(theta') = e^{2 pi i Delta.mu} D(theta) on the sum of the E_alpha, as the lemma states it: for spaces E_alpha supported on arbitrary T_alpha carrying arbitrary distributions with a common mean, arbitrary theta, and no detection hypothesis. Lean states it, with the explicit scalar, only for the sectors of a sector decomposition of D(theta) under single-site Z detection, with T_alpha the actual sector supports and p_alpha the normalized projector diagonals: on frame vectors via sector_action, and on the whole exact code via code_action. (2) The final clause (D(theta') preserves the sum and induces the same projective action) in that abstract setting. Lean has it only for a code with its own sector data, with an existential scalar or in the modular QECC form.

### `main.tex:lem:denominator-clearing` — covered

lemma, line 1583.

- `MainTheory.PivotSmithNormalForm.clearing_smithLastFactor`
- `MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det`
- `MainTheory.SharpClearing.inverseDenominator_eq_smithLastFactor`
- `QECC.NonsingularBinaryMatrix.exists_integral_finalSmithInvariant_smul`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. The lemma says that if C z = h with h integral, then d_s(C) z is integral, so the least common denominator of z divides d_s(C). MainTheory.PivotSmithNormalForm.clearing_smithLastFactor states both clauses for any nonsingular square integer matrix (binary matrices are a special case), any rational z with C z = h integral, and any Smith witness w. Its first conjunct is the integrality of lastFactor times z. Its second says that Denominator.lcmDen z, the lcm of the coordinate denominators, divides w.lastFactor. Lean takes z rational, which loses nothing here: the denominator clause presupposes rational z, and both later uses solve with an integral inverse. nonempty_smithWitness_of_det supplies a witness, and inverseDenominator_eq_smithLastFactor shows that every witness has the same last factor. QECC states the first clause for finalSmithInvariant, the integer-cokernel exponent, which no declaration identifies with d_s(C); it is supporting evidence only.

### `main.tex:thm:colored-finite-lift` — covered

theorem, line 1617.

- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`
- `MainTheory.SymmetryToEntrance.codePreserving_of_symmetry`
- `MainTheory.BinaryPivotLift.rationalLift_order_dvd_smithLastFactor`
- `MainTheory.GeneralLiftOrder.HasPrimitiveLift`
- `MainTheory.GeneralSpectral.sectorCount`
- `MainTheory.ClassificationLevels.diagonalSymmetryGroup`
- `MainTheory.SharpClearing.inverseDenominator_eq_smithLastFactor`
- `MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det`
- `MainTheory.BinaryBeta.BetaExact`
- `MainTheory.BetaExactValue.betaOf_eq_of_exact`
- `QECC.CodeProjector.general_physicalOrder_bound`
- `QECC.CodeProjector.GeneralPhysicalOrderBoundConclusion`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. Hypotheses: a rank-K code with P Z_j P = lambda_j P, and a real D(theta) with D P D-dagger = P inducing a nontrivial projective action of order m with ell distinct logical eigenvalues. Claims: a reduced representative D(a;q) of that action with m | q and q <= beta_{n+ell-1} <= beta_{n+K-1}, built from an invertible zero-one s x s matrix C with q | d_s(C) and 1 <= s <= n+ell-1, and q_min <= beta_{n+ell-1}. MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects assumes an ExactCode with ZDetectsFrame; a code symmetry v in ClassificationLevels.diagonalSymmetryGroup (two-sided range preservation, the manuscript's D P D-dagger = P) with exp(2 pi i theta_j) = v_j; forward preservation by the real gate; and intrinsicClass v != 1. The forward-preservation hypothesis adds nothing, since SymmetryToEntrance.codePreserving_of_symmetry derives it from v's membership and the angle match. Its ell is GeneralSpectral.sectorCount, the number of eigenvalues of the given gate on the code, and its m is the order of the intrinsic class. From one pivot P and lift L it returns 2 <= ell <= K; s with NeZero s and s <= n+ell-1; the zero-one nonsingular binMatrix P with a Smith witness W; Gate.Primitive for L's modular angle, with liftSymmetry in the original class; m | L.order, 2 <= L.order, L.order | W.lastFactor and L.order <= betaOf(n+ell-1) <= betaOf(n+K-1); and an attained minimum qmin over GeneralLiftOrder.HasPrimitiveLift with qmin <= betaOf(n+ell-1). BinaryPivotLift.rationalLift_order_dvd_smithLastFactor gives the divisibility for every witness, and inverseDenominator_eq_smithLastFactor makes the last factor witness-independent, so the divisor is d_s(C). For N >= 1, nonempty_smithWitness_of_det and that equality turn the manuscript's beta_N into a BinaryBeta.BetaExact N beta_N certificate, and BetaExactValue.betaOf_eq_of_exact gives betaOf N = beta_N; since ell >= 2, every betaOf bound above is the manuscript's. QECC.CodeProjector.general_physicalOrder_bound carries a parallel certificate, but its ell is the active-sector count of an internally chosen representative, and its d_s and beta are finalSmithInvariant and smithBeta, which no declaration identifies with the last Smith factor and beta; it is supporting evidence only.

### `main.tex:lem:positive-affine-moments` — partial

lemma, line 1871.

- `QECC.affineSpan_positiveSupportImage_eq_of_affineSquareExpectation`
- `QECC.positiveSupportImage`
- `QECC.affineSquareExpectation`
- `MainTheory.Covariance.affineSpan_eq_of_cov_eq₂`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The lemma says that two finite nonempty point sets in R^n with strictly positive probability weights have the same affine span whenever the weights give every real affine function the same mean square. QECC.affineSpan_positiveSupportImage_eq_of_affineSquareExpectation proves this when both sets lie in {0,1}^n. There the weights are functions p, r on BitString n, nonnegative with total mass one, and the sets are their positive supports embedded by bitVector (QECC.positiveSupportImage). The hypothesis is equality of QECC.affineSquareExpectation for every affine map (Fin n → ℝ) →ᵃ[ℝ] ℝ, and these maps are exactly the functions c + w·x. A strictly positive distribution on T ⊆ {0,1}^n extends by zero to such a weight whose positive support is T, and Lean derives nonemptiness from the unit mass, so the zero-one case is carried in full. No declaration carries the lemma for finite sets in R^n off the cube. MainTheory.Covariance.affineSpan_eq_of_cov_eq₂ handles arbitrary finite weighted point families, but it assumes a common mean and equal covariance matrices, and the step from equal affine mean squares to those hypotheses is not formalized. The manuscript only applies the lemma to zero-one supports, in the distance-three corollary. Not carried: The lemma for finite T_0, T_1 in R^n that are not subsets of {0,1}^n. Lean proves only the zero-one case, and MainTheory's version for general points assumes equal mean and covariance rather than equal affine mean squares.

### `main.tex:cor:d3-physical-order-bound` — partial

corollary, line 1901.

- `MainTheory.D3AffineRankBound.d3_bound_same_class_at_affineRank`
- `MainTheory.SymmetryToEntrance.codePreserving_of_symmetry`
- `MainTheory.CodeAffineSpanBridge.commonAffineSpan_of_exactCodeFrame`
- `MainTheory.SectionTwoGeneral.sectorCount_eq_two`
- `MainTheory.PhaseSectorFull.sectorSupport`
- `MainTheory.SmallBetaValues.betaOf_zero`
- `MainTheory.RealSupportAffineRank.supportAffineRank_le`
- `MainTheory.GeneralLiftOrder.qMin_le`
- `MainTheory.BetaExists.betaOf`
- `MainTheory.BinaryBeta.BetaExact`
- `MainTheory.SharpClearing.inverseDenominator_eq_smithLastFactor`
- `MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det`
- `MainTheory.QECCSmithBridge.smithBeta_betaExact`
- `MainTheory.QECCSmithBridge.smithBeta_eq_betaOf`
- `MainTheory.QECCSmithBridge.finalSmithInvariant_eq_lastFactor`
- `MainTheory.QECCSmithBridge.nonempty_smithWitness`
- `QECC.CodeProjector.distanceThree_physicalOrder_bound`
- `QECC.CodeProjector.DistanceThreePhysicalOrderBoundConclusion`
- `QECC.NonsingularBinaryMatrix.finalSmithInvariant`
- `QECC.smithBeta`
- `QECC.CodeProjector.minimalPhysicalOrder`
- `MainTheory.SparseSmithDisplays.sparse_smith_beta_chain`
- `MainTheory.D3AffineNormalForm.exists_normalForm_affinePivot_of_generator`

2026-10-02 re-review after MainTheory.QECCSmithBridge (resolver and two adversarial verifiers) of the 20260929 source. For the given real gate, MainTheory.D3AffineRankBound.d3_bound_same_class_at_affineRank (its forward-preservation hypothesis supplied by SymmetryToEntrance.codePreserving_of_symmetry) returns an orthonormal eigenframe F of the code with distinct eigenvalues, equal affine ranks r' of the supports of F.vec 0 and F.vec 1, whose affine spans agree by CodeAffineSpanBridge.commonAffineSpan_of_exactCodeFrame, and a primitive lift of the given class with m | q and 2 <= q <= betaOf r' <= betaOf n; SectionTwoGeneral.sectorCount_eq_two gives exactly two sectors. Here 1 <= r' <= n, because r' = 0 would force q <= betaOf 0 = 1 (SmallBetaValues.betaOf_zero) and supportAffineRank_le bounds r' by n, and GeneralLiftOrder.qMin_le with le_trans gives q_min <= betaOf r' <= betaOf n. For nu >= 1, MainTheory.QECCSmithBridge.smithBeta_betaExact rewritten with smithBeta_eq_betaOf says betaOf nu bounds, and is attained by, inverseDenominator over nonsingular zero-one matrices of sizes 1 to nu, and inverseDenominator_eq_smithLastFactor at a witness from nonempty_smithWitness_of_det makes each such inverseDenominator the last Smith factor, so betaOf nu is the manuscript's beta_nu. QECC.CodeProjector.distanceThree_physicalOrder_bound, applied to the class U of the given gate, returns two exhaustive sectors with equal affine spans and common dimension r with 1 <= r <= n, a reduced representative of U of exact order q with m | q and q >= 2, and an r x r nonsingular binary matrix equal to a coordinate minor of the X-normalized support matrix whose pivot rows are independent and span the first support's direction. The bridge makes its Smith fields the manuscript's: matrixSize = r >= 1 gives a nonempty index type (core lemma Fin.pos_iff_nonempty), so QECCSmithBridge.finalSmithInvariant_eq_lastFactor, with a witness from QECCSmithBridge.nonempty_smithWitness, equates binaryMatrix.finalSmithInvariant with d_r(C) for every Smith decomposition, and smithBeta_betaExact at r and at n (n >= r >= 1) identifies smithBeta r and smithBeta n with beta_r and beta_n; hence q | d_r(C), 2 <= q <= d_r(C) <= beta_r <= beta_n and q_min <= beta_r <= beta_n hold for this C, with q_min given by QECC.CodeProjector.minimalPhysicalOrder, the least order of a reduced representative of U. The bridge does not reach the given gate: QECC's sectors, r, support basis and minor are those of sourceRepresentative, a reduced representative chosen inside the proof, and no declaration identifies its fibre-projector supports with the T_k built from the given gate's eigenspace projectors. On the MainTheory side, PhaseSectorFull.sectorSupport defines the given gate's projector-diagonal supports, but no declaration states the rank-one identity equating them with eigenvector supports, and the given-gate statement attaches no minor: SparseSmithDisplays.sparse_smith_beta_chain bounds a generic sparse theta' with no stated link to the given action, and D3AffineNormalForm.exists_normalForm_affinePivot_of_generator records no minor provenance or same-class link. Not carried: (1) The Smith-minor clauses and the beta_r bound with r and C taken from the given gate's T_k: QECC proves q | d_r(C) and q <= d_r(C) <= beta_r <= beta_n, now with the manuscript's d_r and beta, only for the supports of an internally chosen source representative, which no declaration identifies with the given gate's T_k, and MainTheory's given-gate statement has no minor. (2) The rank-one identity tying T_k as defined to eigenvector supports, so aff(T_0) = aff(T_1), 1 <= r <= n, q <= beta_r and q_min <= beta_r are carried for the given gate only with r read as the affine dimension of an eigenvector support.

### `main.tex:def:six-sslp-orbits` — partial

definition, line 2145.

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
- `MainTheory.SSLPOrbitLevels.degreeTwoFeasible_of_fiberEquivalent`
- `MainTheory.SSLPOrbitLevels.activeAffineRank_of_fiberEquivalent`
- `MainTheory.CubeCompletionTransport.Completion`
- `MainTheory.CubeCompletionTransport.completion_of_fiberEquivalent`
- `MainTheory.FiniteRankPipeline.RankRow.CompatibilityCondition`
- `MainTheory.FiniteMomentSupportRank.rank_threshold_iff`
- `MainTheory.ActiveFace.active_affineSpan_eq`
- `MainTheory.ActiveFace.rank_threshold_iff`
- `MainTheory.PaperReductionChain.six_66_orbits`
- `MainTheory.Generated.FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries`
- `MainTheory.Generated.OrbitTableActiveRanks.all_rank_thresholds`
- `MainTheory.CodeOrbitKey.code_reaches_orbit_key`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. The definition, unchanged in substance from 20260924, starts from a reduced representative inside six:eq:qcutoff and takes its two full fibres S_0 and S_{q/m}, with q and m attached. It keeps the pairs that carry distributions with equal first and second moments and quotients them by bit flips, coordinate permutations and label interchange, with q and m kept. It then adds a support-dimension clause (one feasible choice whose two supports share a shifted subspace of dimension rho, with q <= beta_rho), and calls a class realizable when its K_r, the weight<=2 KL completions of the two-fibre form, is nonempty. On the Lean side, SSLPMomentDatum, actSSLPDatum, SSLPMomentEquivalent, sslpMomentSetoid and SSLPMomentOrbit give the labelled quotient (labels_eq_of_sslpMomentEquivalent), SSLPMomentDatum.geometry attaches the degree-two polytope, and degreeTwoFeasible_of_fiberEquivalent and activeAffineRank_of_fiberEquivalent make feasibility and active rank invariant along CubeAction.FiberEquivalent. K_r is SSLPOrbitLevels.KSet, a CubeCompletionTransport.Completion on the fibres of keyAt r (normalized, supported, SS.HasDistance 3); IsRealizationOrbit is its nonemptiness, and completion_of_fiberEquivalent transports it within a class. KSet is indexed by MomentOrbit, which is Fin 66, and nothing relates Fin 66 to the quotient SSLPMomentOrbit, which has no users. Lean's 66 is PaperReductionChain.six_66_orbits: the generated directory has exactly 66 labelled cube classes, and FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries makes its 215 inputs, pair for pair, the certified rank rows that pass RankRow.CompatibilityCondition (q <= beta of the smaller certified active-face rank). FiniteMomentSupportRank.rank_threshold_iff, ActiveFace.active_affineSpan_eq, ActiveFace.rank_threshold_iff and, per printed row, Generated.OrbitTableActiveRanks.all_rank_thresholds describe the largest attainable support rank. But no declaration states that the clause as worded is equivalent to CompatibilityCondition, and composing these with the beta-table lemmas needs further steps, among them a common span at one point of the finite LP polytope and rank rows, which exist only for the 291 certified pairs. Nor does any declaration carry an arbitrary admissible datum through the affine-Smith prefilter and both LP stages into the 215; the only end-to-end route to a key, CodeOrbitKey.code_reaches_orbit_key, starts from an exact code. So the identification of the 66 keys with the classes as defined is not carried. SSLPMomentDatum also accepts any fibre pair, with no reduced-form, cutoff or feasibility field. The 20260929 change to the cutoff citation leaves q <= 9 and eq:beta as they were, so the clause reads as before. Not carried: (1) The support-dimension clause as worded: a feasible choice of distributions whose supports span one common shifted subspace of dimension rho, with q <= beta_rho. Also uncovered are its equivalence with RankRow.CompatibilityCondition and hence the identification of the 66 directory keys (SSLPOrbitLevels.MomentOrbit = Fin 66, the classes of the 215 certified rank-compatible inputs in PaperReductionChain.six_66_orbits) with the paper's candidate classes as defined, including the fact that no admissible datum is discarded by the affine-Smith prefilter or the LP stages. (2) The requirement that the data be the full subset-sum fibres S_0(a;q) and S_{q/m}(a;q) of a reduced representative inside six:eq:qcutoff that admit moment-matched distributions; SSLPMomentDatum takes an arbitrary fibre pair with no reduced-form, cutoff or feasibility field. (3) The literal K_r, which omits normalization, so that the zero pair qualifies; Lean follows the intended normalized reading.

### `main.tex:def:six-classification-levels` — partial

definition, line 2179.

- `MainTheory.ClassificationLevels.IntrinsicProjectiveDiagonalLogicalGroup`
- `MainTheory.GeneralFiniteness.isCyclic`
- `MainTheory.SSLPOrbitLevels.RealizationOrbit`
- `MainTheory.SSLPOrbitLevels.KSet`
- `MainTheory.ClassificationLevels.weightEnumeratorImage`
- `MainTheory.Levels.WImage`
- `MainTheory.MacWilliamsPolynomial.quantum_macwilliams`
- `MainTheory.ClassificationLevels.LUEquivalent`
- `MainTheory.ClassificationLevels.LocalUnitaryCodeClass`
- `SixQubit.CodeEquiv.Equivalent`
- `MainTheory.LocalMonomialSixBridge.luEquivalent_of_codeEquivalent`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. The definition fixes one reduced representative and names four objects. (i) Level (i) is the full cyclic projective diagonal group in the fixed basis; m is only the order of a chosen element. Lean has ClassificationLevels.IntrinsicProjectiveDiagonalLogicalGroup: the code-preserving diagonal phase symmetries modulo those that act as a scalar. GeneralFiniteness.isCyclic proves it cyclic for every ExactCode n 2 3. (ii) Level (ii) is the realizable candidate classes. Lean has SSLPOrbitLevels.RealizationOrbit, built on KSet (the exact distance-three completions on a directory key's fibres). It inherits the unresolved support-dimension clause of def:six-sslp-orbits. (iii) Level (iii) is the enumerator sets W_r. Lean has weightEnumeratorImage, an abbreviation of Levels.WImage: normalized, supported distance-three pairs on two residue fibres of one angle vector, with A_j = Aco/4 (the 1/K^2 normalization at K = 2). MacWilliamsPolynomial.quantum_macwilliams gives the B side. (iv) Level (iv) is projector classes under the local-unitary-permutation relation, together with a stricter bit-flip, diagonal-phase and permutation relation. Lean has LUEquivalent, the equivalence closure of single-qubit unitary and qubit-permutation conjugations of projector kernels, with quotient LocalUnitaryCodeClass. The stricter relation exists only on logical frames, as SixQubit.CodeEquiv.Equivalent, and luEquivalent_of_codeEquivalent shows it implies LU. No projector-level version is defined. W_r is a class-level set in the definition. It collects the vectors of exact completions on every fibre pair reachable from the representative's pair by a common flip mask, a qubit permutation and a label interchange. WImage looks only at the representative's own pair. The transport pieces exist and reach the whole class: - CubeAction.Parameter carries an arbitrary permutation, flip mask and swap bit. - With the labels fixed, CubeAction.FiberEquivalent (CubeAction.lean:206) is the class relation; ClassificationLevels.SSLPMomentEquivalent adds the label equality. - CubeCompletionTransport.pushCompletion (CubeCompletionTransport.lean:100) moves a completion along any parameter. - CubeAction.actFibers_inv_left (CubeAction.lean:169) returns it to the representative. - SixQubit.CodeEquiv.Aco_fixed_perm_flip_swap (SixQubit/CodeEquivEnum.lean:426) leaves the A-coefficients unchanged under exactly that move. No public declaration assembles them: - The step that turns a completion into membership of its normalized enumerator in WImage occurs only inside the proof of CubeCompletionTransport.not_completion_of_WImage_empty. - CubeCompletionTransport.completion_of_mem_WImage returns bare existence and drops the vector. - No Lean object states the class-level set or its equality with WImage at the representative. Under the composition rule, representative independence is therefore not carried. Separately, the literal set-builder in eq:Wr-definition does not tie the vector to the completion; Lean follows the intended reading. Not carried: (1) A projector-level definition of the bit-flip/diagonal-phase/permutation relation. Only the frame-level SixQubit.CodeEquiv.Equivalent exists. (2) Equality of the class-level W_r with Levels.WImage at the table representative (representative independence). The transport pieces pushCompletion, actFibers_inv_left and Aco_fixed_perm_flip_swap exist, but no declaration turns a transported completion into WImage membership or states the equality. (3) The literal set-builder of eq:Wr-definition. (4) The support-dimension clause inherited at level (ii).

### `main.tex:six:thm:global-status` — unreviewed

theorem, line 2265.


_No review recorded._

### `main.tex:thm:six-15-sslp-realization-orbits` — partial

theorem, line 2290.

- `MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys`
- `MainTheory.RealizationOrbits15.card_realization_orbits`
- `MainTheory.RealizationOrbits15.realizationKeys_paperIds`
- `MainTheory.RealizationOrbits15.realizationKeys_orderDistribution`
- `MainTheory.PaperSupplementaryNoGo.hasCompletion_iff_paperOrbitId`
- `MainTheory.PaperSupplementaryNoGo.paperOrbitId_injective`
- `MainTheory.PaperSupplementaryNoGo.paperOrbitId_range`
- `MainTheory.CubeCompletionTransport.Completion`
- `MainTheory.CubeCompletionTransport.completion_of_fiberEquivalent`
- `MainTheory.WImageIntrinsicBridge.exactCodeOfPair`
- `MainTheory.PaperReductionChain.six_66_orbits`
- `MainTheory.Generated.FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries`
- `MainTheory.Generated.OrbitTableRecords.paperKey`
- `MainTheory.Generated.OrbitTableNumericData.all_rows`
- `MainTheory.Generated.OrbitTableNumeric.all_labeled_equivalences`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. Over the 66 candidate classes of def:six-sslp-orbits that meet the support-dimension bound, the theorem says the classes with an exact weight<=2 KL completion are exactly the fifteen displayed table numbers. It then counts fifteen, splits them 11, 3, 1 over m = 2, 3, 5, says each holds an exact ((6,2,3)) code, and disclaims any classification of projectors. Per key the equivalence is carried: RealizationOrbits15.hasCompletion_iff_mem_realizationKeys proves both directions for every k : Fin 66, and completion_of_fiberEquivalent makes existence a property of the whole class. HasCompletion is a CubeCompletionTransport.Completion, a normalized pair supported on the key's two fibres with SS.HasDistance 3, which is a member of K_r as the definition words it; WImageIntrinsicBridge.exactCodeOfPair packages such a pair, written as ![c, d], as a CodeSpec.ExactCode 6 2 3. card_realization_orbits gives fifteen completable keys, and realizationKeys_orderDistribution gives the 11:3:1 split through the retained label (keyAt k).m. The displayed numbers enter only through the generated numbering paperOrbitId: hasCompletion_iff_paperOrbitId and realizationKeys_paperIds state the equivalence and the fifteen-element image, and paperOrbitId_injective and paperOrbitId_range make it a bijection onto 1..66. The printed table rows are tied to keys separately: OrbitTableNumericData.all_rows says row i's fibres are the residue fibres of its printed angle vector, and OrbitTableNumeric.all_labeled_equivalences makes row i labelled-equivalent to keyAt (OrbitTableRecords.paperKey i). No declaration relates paperKey to paperOrbitId, although reading the generated sources shows paperOrbitId (paperKey i) = i + 1 for every row. All these counts are counts of directory keys: by PaperReductionChain.six_66_orbits and FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries, the keys are the labelled cube classes of the 215 certified pairs passing RankRow.CompatibilityCondition, and no declaration identifies them with the classes def:six-sslp-orbits defines, which that entry records. So the count of fifteen and the split, read as counts of the paper's classes, rest on an identification the development does not state; the statement itself is unchanged from 20260924. Not carried: (1) Identification of the 66 directory keys with the paper's candidate classes as defined in def:six-sslp-orbits: full-fibre data of reduced representatives within the cutoff that are moment-feasible and meet the support-dimension clause as worded. The count 15 and the 11:3:1 split, as counts of paper classes, depend on it. (2) The tie between the generated numbering paperOrbitId, through which the displayed set is stated, and the printed table rows that OrbitTableRecords.paperKey, OrbitTableNumericData.all_rows and OrbitTableNumeric.all_labeled_equivalences attach to keys: no declaration states paperOrbitId (paperKey i) = i + 1. The per-key equivalence (hasCompletion_iff_mem_realizationKeys) and its restatement in the paperOrbitId numbering are carried.

### `main.tex:tab:six-realizable-classes` — unreviewed

table, line 2345.


_No review recorded._

### `main.tex:thm:six-WE-status` — partial

theorem, line 2429.

- `MainTheory.WImageSettled62.all_11_realized_WImages`
- `MainTheory.ProvedWEUnion.provedImages_eq`
- `MainTheory.Levels.WImage`
- `MainTheory.WImageOpenL.FI_subset_orbit1`
- `MainTheory.WImageOpenL.FI_subset_orbit2`
- `MainTheory.WImageOpenL.FI_subset_orbit3`
- `MainTheory.WImageOpenL.FI_subset_orbit4`
- `MainTheory.OpenOrbitsRealized.openKeys_hasCompletion`
- `MainTheory.CubeAction.fiberEquivalent_refl`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. The theorem gives eleven exact enumerator sets for the realizable classes: - W_36 = {R_5^A}; - W_7 and W_8 are segments of the L-line; - W_9, W_10, W_16, W_21 and W_22 equal {E_2^A}; - W_11 and W_23 equal {E_1^A}; - W_45 is the M-segment on [2/3,1]. It also says W_1..W_4 are nonempty but open, states the boxed union, and disclaims both a 15-class result and the global conjecture. WImageSettled62.all_11_realized_WImages inhabits Realized11Statement. Its eleven fields are equalities of Levels.WImage at the printed table representatives, with residues 0 and q/m. The angle vectors agree with the table rows modulo 3, 4, 5 and 6, and FI, FII, R5A, E1A and E2A unfold to L(alpha), M(t), R_5^A, E_1^A and E_2^A. ProvedWEUnion.provedImages_eq proves the union identity over the same eleven images. In this theorem W_r is the class-level set of def:six-classification-levels. Each equality therefore also needs every completion on every member of the class to give a vector already in the representative's image. The pieces needed for that cover the whole class: pushCompletion (CubeCompletionTransport.lean:100) works for every cube parameter, together with actFibers_inv_left (CubeAction.lean:169) and Aco_fixed_perm_flip_swap (SixQubit/CodeEquivEnum.lean:426). But they are not assembled: - no public declaration turns a transported completion into a WImage member with its enumerator; - completion_of_mem_WImage keeps only existence; - the module note of WImageSettled62 limits that file to the paper-representative images. By the composition rule, the eleven equalities and the boxed union are carried only for completions on the representative's own fibre pair. Nonemptiness of W_1..W_4 is carried. FI_subset_orbit1..4 put the L-interval inside WImage at the printed representatives, and a representative's pair lies in its own class (CubeAction.fiberEquivalent_refl), so that image sits inside the class-level set. openKeys_hasCompletion also gives completions on the four directory keys. The scoping and disclaimer sentences assert nothing further. The statement is unchanged from 20260924 and does not depend on the rewritten Section III. Not carried: Equality of the class-level W_r with Levels.WImage at the table representative. The eleven set equalities and the boxed union eq:proved-WE-union are proved only for completions on the representative's own fibre pair. No declaration shows that completions on the other members of the class (reached by flips, permutations and label interchange) give no further vectors.

### `main.tex:rem:four-open-orbits` — unreviewed

remark, line 2490.


_No review recorded._

### `main.tex:thm:unique-C5-LU` — covered

theorem, line 2607.

- `MainTheory.OrderFiveOrbitMembership.orbit36_of_orderFive`
- `MainTheory.OrderFiveOrbitMembership.exists_cubeParameter_orbit36`
- `MainTheory.OrderFiveOrbitMembership.unique_C5_LU`
- `MainTheory.OrderFivePaperIdentification.paper36_equivalent_directoryKey34`
- `SixQubit.Orbit36Certified.original_equivalent_canonical`
- `SixQubit.CodeEquiv.Equivalent.symm`
- `SixQubit.CodeEquiv.Equivalent.trans`
- `MainTheory.OrderFiveCodeRigidity.luEquivalent_of_orderFive`
- `MainTheory.SixQubitIntrinsicAttainment.order_five_attained`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The theorem has three clauses. First, an exact ((6,2,3)) code with a projective diagonal element of order five lies in class 36. Second, all exact completions of class 36 are related by permutations, bit flips and diagonal phases. Third, the order-five sector is one LU class with permutations allowed. For the first clause, orbit36_of_orderFive and exists_cubeParameter_orbit36 take any ExactCode 6 2 3 with an element g of order 5 in its fixed-basis intrinsic group and produce a sorted normal form of that code with S.m = 5. Its fiber record is carried by a cube parameter onto directory key 34, and paperOrbitId 34 = 36. paper36_equivalent_directoryKey34 ties key 34 to the printed class-36 fibers of (1,1,1,2,2,4) mod 5. For the second clause, original_equivalent_canonical shows that every normalized distance-3 pair on those printed fibers is CodeEquiv.Equivalent to the canonical pair (c36,d36). That relation is generated by permutations, bit flips and per-qubit diagonal phases, together with logical phases or interchange that leave the projector fixed, and Equivalent.symm and Equivalent.trans then relate any two completions. For the third clause, unique_C5_LU and luEquivalent_of_orderFive give LUEquivalent projectors for any two order-five codes, and order_five_attained shows the sector is nonempty. eq:Gdiag and eq:LU-equivalence are unchanged in 20260929.

### `main.tex:cor:six-C5-minimum-length` — covered

corollary, line 2620.

- `MainTheory.MinimumLengthOrderFive.minimum_length`
- `MainTheory.MinimumLengthOrderFive.canonical_attains`
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The corollary has three parts. Any exact ((n,2,d)) code with d>=3 that admits a transversal gate made of one block, acting with projective order five has n>=6. The displayed six-qubit code attains n=6. Every six-qubit code with the property is LU-and-permutation equivalent to it. minimum_length takes arbitrary n, an ExactCode n 2 d with 3<=d, arbitrary one-qubit unitary matrices U_j, and a 2x2 unitary Q with tensorKernel U times the frame equal to the frame times Q. Its order hypothesis is orderOf (adjoint Q) = 5, which is the projective order because the adjoint kernel is the scalars, and it concludes 6<=n. No diagonal or finite-order assumption on the physical gate is made. canonical_attains uses canonicalFrame = (c36,d36), which is exhibited with a diagonal transversal gate and a logical matrix of projective order 5. The generated SixQubit.Orbit36Code data reproduce the displayed psi_0 and psi_1, with a* = (1,1,1,1,2,3) mod 5 and supports in the residue-0 and residue-4 fibers; I checked that applying Z5 Z6, the all-X string and conjugation to psi_0 gives psi_1 term by term. six_qubit_lu_unique_of_distance_ge_three gives uniqueness for any ExactCode 6 2 d with d>=3 under ClassificationLevels.LUEquivalent, permutations included. The statement is unchanged, and the Lean route uses neither the rewritten Section III nor tabulated beta values.

### `main.tex:six:rem:global-family-caveat` — unreviewed

remark, line 2641.


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
- `MainTheory.WImages.WImage_orbit45`
- `SixQubit.Orbit45Final.fully_certified`
- `SixQubit.Orbit45Universal.universal_converse`
- `SixQubit.Orbit45Phase.phase_relations`
- `SixQubit.Orbit45A2.Aco_two_value`
- `SixQubit.Orbit45Gram.simplex_of_masses`
- `SixQubit.Orbit45Gram.simplex_interval`
- `SixQubit.Orbit45Gram.a2_change_of_variables`
- `SixQubit.Orbit45Attain.direct_families`
- `SixQubit.Orbit45Attain.direct_certificate`
- `SixQubit.Orbit45Attain.direct_block_masses`

2026-10-02 two-agent semantic review (reader, adversarial checker and judge) of the 20260929 source. The theorem (supplementary.tex 4617-4662) concerns the record (q,m,a)=(6,2,(1,1,2,3,4,4)) on residues 0 and 3, and makes four claims. Exact completions exist. The normalized A-image is the family M(t) for 2/3<=t<=1. Each code's B-vector is the stated one at the same t. Finally, the exact solutions are parametrized by triples beta,gamma,sigma >= 0 with sum 1/4 and each at most 1/8, with t = 32(beta^2+gamma^2+sigma^2). MainTheory.PaperSupplementaryImages.o45_weight_image, proved by MainTheory.WImages.WImage_orbit45, states the A-image as a set equality between Levels.WImage at SixQubit.Orbit45Support.av (literally ![1,1,2,3,4,4] in ZMod 6, words on fibres 0 and 3, A normalized as Aco/4) and WImages.FII on Icc (2/3) 1. Nonemptiness follows from that equality. SixQubit.Orbit45Final.fully_certified gives both directions with IsFamilyA and IsFamilyB at one common t. Since Bco is K times the sum of frob, which is K^2 times the paper's B_j of eq:o36Bjdef, IsFamilyB is exactly four times the stated B-vector. For the triangle clause, the forward half comes from composing three theorems. Orbit45Universal.universal_converse extracts the code's own block masses g_i, and each amplitude of block i has squared modulus g_i/4, so beta,gamma,sigma are the g_i/4 up to relabelling (the Lean xor-55 blocks are the paper's pairs {r,9-r}). Its ConverseData gives g_i>=0, sum 1 and 1-2g_i>=0, which is the stated domain. Aco_two_value is universal over BlockMasses; with phase_relations it gives raw A_2 = 8 times the sum of g_i^2, which is normalized A_2 = 32R. The Gram lemmas send every domain triple to a t in [2/3,1], and fully_certified attains every such t. What is missing is the converse the proof proves at 5138-5151: that every domain triple is the pair-probability data of some exact completion. direct_certificate and direct_block_masses realize a triple only when unit phases closing the triangle are supplied as a Params hypothesis. The only theorems that produce Params are the low chart (isosceles triples) and the high chart (one side equal to 1/8). Not carried: Surjectivity of the triangle parametrization: no declaration proves that every triple in the stated domain (nonnegative, summing to 1/4, each at most 1/8) arises as the pair probabilities of an exact orbit-45 completion. Equivalently, nothing proves that unit phases closing the vector triangle exist for an arbitrary domain triple. Lean constructs Params, and so realizes triples, only along two one-parameter charts (isosceles triples, and triples with one side equal to 1/8), which suffices to attain every t but not every triple. The forward half (each code's triple lies in the domain and gives A_2 = 32R) is carried only by composing universal_converse, phase_relations and Aco_two_value, not by a single declaration.

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

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The theorem puts the whole L(alpha) interval, 0<=alpha<=1, inside each of W_1..W_4, and the M(t) segment, 2/3<=t<=1, inside W_1 and W_4. It also says every such point, endpoints included, is realized by some exact ((6,2,3)) code. MainTheory.WImageOpenL.FI_subset_orbit1..4 state FI '' Icc 0 1 is contained in Levels.WImage at SixQubit.OpenLOrbit1..4.angle with residues 0 and 1. Those angles are literally 000111, 001111, 011111 and 111111 in ZMod 2, which are the q=m=2 records of q2fam:eq:records. MainTheory.WImageOrbit4M.FII_subset_WImage_orbit1_inter_orbit4 states FII '' Icc (2/3) 1 lies in the intersection of the WImage at WImageOrbit1.orbit1Av (000111) and at SixQubit.OpenMParity.angle (111111). WImages.FI and WImages.FII unfold to the L and M vectors. Membership in WImage means a normalized pair supported on the two fibres with SS.HasDistance 3 and that A-vector, so attainment by an exact code is carried, and the closed intervals include the endpoints. The only main-text dependency is the L/M notation, which 20260929 main.tex still defines identically (eq:Lalpha and eq:Mt-main, lines 2327-2331, Section IV unchanged apart from one citation). The supplement also repeats it locally. The Lean proof uses a certified parity-circle construction rather than the split-qubit route; that changes the proof, not the statement.

### `supplementary.tex:thm:main-result-I` — covered

theorem, line 5754.

- `MainTheory.GeneralFiniteness.isCyclic`
- `MainTheory.IntrinsicOrderAudit.natCard_mem`
- `MainTheory.SixQubitIntrinsicOrderSet.including_identity`
- `MainTheory.IntrinsicOrderAudit.orderOf_le_five`
- `MainTheory.SixQubitIntrinsicAttainment.order_five_attained`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. Given an exact ((6,2,3)) code with a nontrivial projective diagonal group, the theorem asserts three things: the group is C_m with m in {2,3,5}; the attained element orders, identity included, are exactly {1,2,3,5}; and M_3(6)=5. The Lean group IntrinsicGroup C is the quotient of all code-preserving local diagonal phases (diag(1,u_j) on each qubit) by those acting as a nonzero scalar on the code. Since a general diagonal product gate differs from such a phase by a global scalar, this is the paper's G_diag(P) for the projector of an actual ExactCode 6 2 3. MainTheory.GeneralFiniteness.isCyclic gives cyclicity for every ExactCode n 2 3. MainTheory.IntrinsicOrderAudit.natCard_mem puts Nat.card in {1,2,3,5}, which also forces finiteness. Nontriviality excludes card 1, so the group is cyclic of order m in {2,3,5}. MainTheory.SixQubitIntrinsicOrderSet.including_identity is the set equality of attained element orders with {1,2,3,5} over all such codes. orderOf_le_five together with order_five_attained gives the maximum M_3(6)=5. The statement does not depend on any main-text number. Its proof cites a hard-coded Corollary III.4 that no longer resolves in 20260929; that is recorded as a separate low-severity prose gap and does not affect these carriers.

### `supplementary.tex:thm:main-result-II` — partial

theorem, line 5784.

- `MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys`
- `MainTheory.RealizationOrbits15.card_realization_orbits`
- `MainTheory.RealizationOrbits15.realizationKeys_paperIds`
- `MainTheory.RealizationOrbits15.realizationKeys_orderDistribution`
- `MainTheory.PaperSupplementaryNoGo.hasCompletion_iff_paperOrbitId`
- `MainTheory.PaperSupplementaryNoGo.paperOrbitId_injective`
- `MainTheory.PaperSupplementaryNoGo.paperOrbitId_range`
- `MainTheory.CubeCompletionTransport.Completion`
- `MainTheory.CubeCompletionTransport.completion_of_fiberEquivalent`
- `MainTheory.WImageIntrinsicBridge.exactCodeOfPair`
- `MainTheory.PaperReductionChain.six_66_orbits`
- `MainTheory.Generated.FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries`
- `MainTheory.Generated.OrbitTableRecords.paperKey`
- `MainTheory.Generated.OrbitTableNumericData.all_rows`
- `MainTheory.Generated.OrbitTableNumeric.all_labeled_equivalences`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. The supplementary restatement of Result II has the same content as thm:six-15-sslp-realization-orbits. Over the 66 candidate classes meeting the support-dimension bound, an exact weight<=2 KL completion exists precisely for the fifteen displayed indices; these split 11, 3, 1 over m = 2, 3, 5 and each carries an exact ((6,2,3)) code, and a disclaimer follows. RealizationOrbits15.hasCompletion_iff_mem_realizationKeys proves both directions for every key k : Fin 66, and completion_of_fiberEquivalent spreads existence over the class. A completion is a CubeCompletionTransport.Completion, a normalized pair supported on the key's fibres with SS.HasDistance 3, which is a member of K_r as defined; WImageIntrinsicBridge.exactCodeOfPair packages such a pair as a CodeSpec.ExactCode 6 2 3. card_realization_orbits, realizationKeys_paperIds and realizationKeys_orderDistribution give fifteen keys, their image under paperOrbitId, and the 11:3:1 split by the retained label m. hasCompletion_iff_paperOrbitId, paperOrbitId_injective and paperOrbitId_range state the equivalence in that generated numbering. But the printed table rows reach keys only through OrbitTableRecords.paperKey, by OrbitTableNumericData.all_rows and OrbitTableNumeric.all_labeled_equivalences, and no declaration relates paperKey to paperOrbitId. All these are counts of directory keys, which by PaperReductionChain.six_66_orbits and FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries are the labelled cube classes of the 215 certified pairs passing RankRow.CompatibilityCondition. The section opening asserts that the main text's candidate classes are these moment orbits, but no declaration identifies the keys with the classes as def:six-sslp-orbits defines them, support-dimension clause as worded included. So fifteen and the split, as counts of the paper's classes, depend on that unstated identification; the per-key equivalence is carried, and the statement is unchanged from 20260924. Not carried: (1) Identification of the 66 directory keys with the paper's candidate classes as defined in def:six-sslp-orbits: full-fibre data of reduced representatives within the cutoff that are moment-feasible and meet the support-dimension clause as worded. The count 15 and the 11:3:1 split, as counts of paper classes, depend on it. (2) The tie between the generated numbering paperOrbitId, through which the displayed indices are stated, and the printed table rows that OrbitTableRecords.paperKey, OrbitTableNumericData.all_rows and OrbitTableNumeric.all_labeled_equivalences attach to keys: no declaration states paperOrbitId (paperKey i) = i + 1. The per-key equivalence (hasCompletion_iff_mem_realizationKeys) and its restatement in the paperOrbitId numbering are carried.

### `supplementary.tex:thm:main-result-III` — partial

theorem, line 5873.

- `MainTheory.WImageSettled62.all_11_realized_WImages`
- `MainTheory.ProvedWEUnion.provedImages_eq`
- `MainTheory.WImageOpenL.FI_subset_orbit1`
- `MainTheory.WImageOpenL.FI_subset_orbit2`
- `MainTheory.WImageOpenL.FI_subset_orbit3`
- `MainTheory.WImageOpenL.FI_subset_orbit4`
- `MainTheory.OpenOrbitsRealized.openKeys_hasCompletion`
- `MainTheory.CubeAction.fiberEquivalent_refl`

2026-10-02 two-agent semantic review (reader and adversarial checker, then a consistency resolver and adversarial verifier) of the 20260929 source. The theorem lists eleven exact sets: - W_36 = {R_5^A}; - W_7 = L on [0,1] and W_8 = L on [1/2,1]; - W_9, W_10, W_16, W_21 and W_22 equal {E_2^A}; - W_11 and W_23 equal {E_1^A}; - W_45 = M on [2/3,1]. It says W_1..W_4 are nonempty but unresolved, gives the union identity, and disclaims both the full classification and the global conjecture. Just before the theorem, at lines 5858-5860, the supplement defines W_r as the normalized A-vectors realized by exact codes whose projectors lie in class r. That is a class-level set. MainTheory.WImageSettled62.all_11_realized_WImages inhabits Realized11Statement. Its fields are these eleven equalities for Levels.WImage at the paper representatives, with the correct residue pairs (Orbit7Real.av = 011122 mod 3, Orbit36Transport.originalAv = 111224 mod 5, Orbit45Support.av = 112344 mod 6, and so on). R5A, E1A, E2A and the /4 normalization match the displays and eq:o36Ajdef. MainTheory.ProvedWEUnion.provedImages_eq is the union identity over the same eleven images. Equating those images with the class-level W_r needs every completion on every member of the class to give a vector already in the representative's image. The pieces cover the whole class: pushCompletion (CubeCompletionTransport.lean:100), actFibers_inv_left (CubeAction.lean:169) and Aco_fixed_perm_flip_swap (SixQubit/CodeEquivEnum.lean:426). But they are not assembled: - no public declaration turns a transported completion into a WImage member with its enumerator; - completion_of_mem_WImage keeps only existence; - WImageSettled62's module note limits that file to the paper-representative images. By the composition rule, the eleven equalities and the union are carried only at the representative's fibre pair. Nonemptiness of W_1..W_4 is carried. FI_subset_orbit1..4 place the L-interval in the representative's image, that representative lies in its own class (CubeAction.fiberEquivalent_refl), and openKeys_hasCompletion gives completions on keys 0..3. The unresolved status and the disclaimers assert nothing further. The cross-reference to the global conjecture resolves to eq:global-WE-conjecture in main.tex. Not carried: Equality of the class-level W_r (the supplement's definition at lines 5858-5860, matching def:six-classification-levels) with Levels.WImage at the table representative. The eleven set equalities and the union identity eq:main-result-III-union are proved only for completions on the representative's own fibre pair, not for every member of the class.

### `supplementary.tex:thm:main-result-IV` — covered

theorem, line 5955.

- `MainTheory.OrderFiveOrbitMembership.exists_cubeParameter_orbit36`
- `SixQubit.Orbit36Certified.original_equivalent_canonical`
- `MainTheory.OrderFiveOrbitMembership.unique_C5_LU`
- `MainTheory.OrderFiveCodeRigidity.luEquivalent_of_orderFive`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The theorem makes three claims. Every exact ((6,2,3)) code with an order-five element in its projective diagonal group lies in class 36. All class-36 completions are related by qubit permutations, bit flips and diagonal phase gates. Hence the projective-C_5 sector is one LU class with permutations allowed. MainTheory.OrderFiveOrbitMembership.exists_cubeParameter_orbit36 takes any ExactCode 6 2 3 and any g in its intrinsic group with orderOf g = 5. It returns a sorted normal form and a cube parameter (permutation and flips) carrying the code's fibre pair onto key 34, whose paper number is 36. SixQubit.Orbit36Certified.original_equivalent_canonical shows that every normalized distance-three pair on the full residue-0 and residue-1 fibres of the table representative (1,1,1,2,2,4) mod 5 is CodeEquiv.Equivalent to the canonical pair c36, d36. That relation is a LocalMonomial (permutation, flips, diagonal phases) followed by logical phases and an optional logical swap, and the last two leave the code space unchanged. MainTheory.OrderFiveOrbitMembership.unique_C5_LU gives LUEquivalent of the code projector to the canonical projector. LUEquivalent is the equivalence closure of one-qubit unitary conjugations and qubit permutations. luEquivalent_of_orderFive gives the pairwise statement. The proof's appeal to the controlled-lift bound goes through Section III.C of the main text, which still holds the bound in 20260929 (Corollary III.11, eq:d3-full-bound).

### `supplementary.tex:cor:main-order-five-minimum-length` — covered

corollary, line 5992.

- `MainTheory.MinimumLengthOrderFive.minimum_length`
- `MainTheory.MinimumLengthOrderFive.canonical_attains`
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`

2026-10-02 two-agent semantic review (reader and adversarial checker) of the 20260929 source. The corollary makes three claims. If an exact ((n,2,d)) code with d>=3 has a one-block transversal gate acting with projective order five, then n>=6. The canonical class-36 code attains n=6. Any six-qubit code with that property is LU-and-permutation equivalent to it. MainTheory.MinimumLengthOrderFive.minimum_length takes arbitrary n and an ExactCode n 2 d with 3<=d. It also takes arbitrary one-qubit unitaries U_j and a logical unitary Q with tensorKernel U times the code frame equal to the frame times Q. Projective order five is orderOf (adjoint Q) = 5, and the conclusion is 6<=n. MainTheory.MinimumLengthOrderFive.canonical_attains supplies such U and Q for canonicalCode, whose frame is the c36, d36 pair encoding the supplement's canonical words. MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three gives LUEquivalent to the canonical projector for every six-qubit code with d>=3 under the same interface. The corollary uses only thm:main-result-IV and supplement equations. Its main-text counterpart cor:six-C5-minimum-length (IV.8 in both versions) still exists. The full-transversal-group/Clifford prose after the proof is outside this entry.

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
See `results/prose-review-20260929.md` and `results/errata-20260929.json`.
