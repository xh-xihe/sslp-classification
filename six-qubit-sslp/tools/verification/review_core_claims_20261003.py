#!/usr/bin/env python3
"""Apply explicit current-source reviews of the introductory definitions.

These decisions come from reading the current statements, their context and
the named Lean types. They are not a transfer of historical coverage.
"""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims

SOURCES = {
    'documents/20261003/main.tex': 'fb694c01b1144ce99d9a6d602c1a2629269bdd4c906a95fe9654f43f54a70958',
    'documents/20261003/supplementary.tex': '7b15965e38cce05c0b1d3ae0ccccc0642d5c2db74d06f7453d4dd8fac5459ede',
}
REVIEWS = {
    'displaymath@749': ([
        'QECC.realSupportWeight', 'QECC.supportPhase_coe_real'],
        'The current real subset sum is the literal sum of t_j times the 0/1 computational bit. Its image in the circle equals the gate support phase.'),
    'eq:diagonal-conjugation-entry': ([
        'MainTheory.DiagonalProofSteps.real_conjugation_entry'],
        'New public theorem gives the exact entry of actual D(t)*P*D(t)-dagger with the stated full-turn exponential of s_t(x)-s_t(y), for any physical matrix P. It is not merely an equality consequence restricted to preserving gates.'),
    'displaymath@760': ([
        'QECC.CodeProjector.Edge'],
        'Edge is exactly the finite subtype of ordered computational pairs with the actual projector entry nonzero, including diagonal entries. No chosen sparse support replaces it.'),
    'displaymath@765': ([
        'QECC.CodeProjector.edgeMatrix', 'QECC.CodeProjector.edgeMatrix_mulVec'],
        'Each integer row is bitInt(x_j)-bitInt(y_j) for an actual nonzero projector edge, and its real action is proved equal to the difference of the two subset sums. Any ordering is only a finite-index reindexing.'),
    'eq:preservation-integer-matrix': ([
        'MainTheory.DiagonalProofSteps.preserving_integer_matrix_iff'],
        'New arbitrary-n,K iff directly identifies the physical conjugation equation with existence of the integral edge-image vector for the supplied real t and actual edge matrix. It uses all nonzero projector entries and both directions.'),
    'eq:diagonal-Hh': ([
        'QECC.CodeProjector.weightedNumberOp',
        'QECC.CodeProjector.weightedNumberOp_eq_sum'],
        'The diagonal Hamiltonian is the actual sum of h_j times physical number operators and has the real subset-sum diagonal.'),
    'displaymath@784': ([
        'MainTheory.DiagonalProofSteps.hamiltonian_commutator',
        'QECC.CodeProjector.edgeMatrix_mulVec'],
        'The commutator entry is now public and exactly ((x-y).h)*P_xy. On nonzero entries the edge-kernel hypothesis makes the difference zero; on zero entries the product vanishes directly.'),
    'displaymath@788': ([
        'QECC.CodeProjector.weightedNumberOp_compression',
        'QECC.CodeProjector.weightedNumberOp_eq_sum'],
        'The compression theorem takes the supplied detection scalars mu and gives exactly the sum h_j*mu_j times P, using actual matrix multiplication and finite distributivity.'),
    'displaymath@792': ([
        'MainTheory.DiagonalProofSteps.hamiltonian_scalar'],
        'The public scalar theorem executes the displayed chain with actual projector idempotence, Hamiltonian commutation from exact edges, and the supplied compression scalars. Its scalar is the literal h.mu.'),
    'eq:kernel-direction-scalar': ([
        'MainTheory.DiagonalProofSteps.kernel_direction_scalar',
        'QECC.CodeProjector.edgeMatrix_mulVec'],
        'The public theorem gives D(h)*P=exp(2*pi*i*(h.mu))*P with the actual supplied mu. The real kernel of the actual edge matrix supplies its exact-edge hypothesis. The exponential scalar is explicit, rather than an unspecified projective scalar.'),
    'displaymath@806': ([
        'QECC.integerMatrix_uniform_rational_lift',
        'QECC.CodeProjector.preserves_integral_edge_values'],
        'The fixed edge matrix determines Q0 before choosing a preserving phase and its real lift. The rational-section theorem then returns integer c with the exact displayed homogeneous equation.'),
    'displaymath@810': ([
        'QECC.rationalPhase', 'QECC.integerMatrix_uniform_rational_lift',
        'QECC.CodeProjector.exists_uniform_rationalPhase_representative'],
        'These are the actual chosen rational phase c/Q0 and its real lift difference. The uniform representative proof uses this same witness, proves its kernel condition and code preservation, and proves that the difference acts as a code scalar.'),
    'displaymath@817': ([
        'MainTheory.DiagonalProofSteps.real_projective_replacement'],
        'New public matrix theorem proves the displayed D(r+h)*P=exp(2*pi*i*(h.mu))*(D(r)*P) on the supplied real vectors, using the exact common scalar. Setting h=t-r yields the current chain, not just existence of a projectively equivalent gate.'),
    'displaymath@826': ([
        'QECC.phaseHom', 'QECC.phaseHom_injective',
        'QECC.rationalPhase_eq_phaseHom', 'QECC.CodeProjector.ModularPreserving',
        'QECC.CodeProjector.projectiveDiagonalGroup_finite_of_uniform'],
        'The finite ZMod Q0 coefficient vectors embed injectively into the torus. Integer numerators reduce modulo Q0 without changing phases, and the map from preserving residue vectors onto actual projective classes is proved surjective. This supplies the finite representative set used in the proof.'),
    'eq:exact-phase-order': ([
        'QECC.exists_reducedDiagonalRepresentative',
        'QECC.ReducedDiagonalRepresentative.addOrderOf_phase',
        'QECC.rationalPhase_isOfFinAddOrder'],
        'Finite additive order exists for the selected rational phase; the reduced representative chooses its actual least positive order q. The projective nonidentity ensures phase nonzero and hence q>=2.'),
    'displaymath@844': ([
        'QECC.exists_reducedDiagonalRepresentative',
        'QECC.ReducedDiagonalRepresentative.phase', 'QECC.phaseHom'],
        'The reduced representative represents the original finite-order phase exactly, coordinatewise via ZMod.toAddCircle; its canonical residue values lie in [0,q). This is an equality of physical phase vectors, not only logical classes.'),
    'displaymath@856': ([
        'MainTheory.FiniteGateCanonicalNormalization.common_divisor_phase_zero',
        'QECC.ReducedDiagonalRepresentative.commonGCD_eq_one'],
        'The new public divisor theorem proves that a common g dividing q and every actual numerator kills the physical phase at q/g. The existing reduced-representative proof uses this same arithmetic and least-order contradiction to establish the literal common gcd one.'),
    'eq:prelim-two-fiber': ([
        'MainTheory.FiniteGateCanonicalNormalization.supplied_primitive_gate',
        'QECC.CodeProjector.HasRankTwoCanonicalNormalization',
        'QECC.CodeProjector.exists_rankTwoCanonicalNormalization',
        'MainTheory.RankTwoGlobal.finiteGenerator_twoFiber'],
        'The given finite primitive physical gate is retained with its original q. Its actual projective order m is derived, not supplied as a free integer. The canonical certificate transports its two exhaustive rank-one phase sectors to 0 and q/m by a unit power, local X and a qubit permutation, preserves exact physical and logical orders, and preserves every distance condition. This supplied-gate theorem needs no distance>=2 assumption or replacement rational representative; the orthonormal-eigenframe two-fiber theorem supplies the state-level support formulation.'),
    'eq:prelim-LP-normalization': ([
        'MainTheory.PhaseSectorMoments.probability_nonneg',
        'MainTheory.DiagonalMomentBridge.fiber_probability_sum'],
        'The probabilities are actual squared amplitudes. State support in a full residue fiber and innerC(v,v)=1 give sum one over that full fiber, including strings with zero amplitude. Nonnegativity is normSq_nonneg.'),
    'eq:prelim-diagonal-Pauli': ([
        'MainTheory.DiagonalMomentBridge.diagonal_action',
        'MainTheory.DiagonalMomentBridge.character_eq_product'],
        'The mask represents exactly the distinct sites J. Actual SS.pauliAct for the pure-Z Pauli is multiplication by the product of 1-2*x_j, with the bit convention 0/1; no informal substitution for the operator is assumed.'),
    'eq:prelim-moment-LP': ([
        'MainTheory.BinaryFeatureMoments.phi2',
        'MainTheory.BinaryFeatureMoments.average_iff_binary_moments',
        'MainTheory.BinaryFeatureMoments.average_iff_character_moments',
        'MainTheory.BinaryFeatureMoments.average_eq_of_distance',
        'MainTheory.BinaryFeatureMoments.average_eq_fiber'],
        'New arbitrary-n phi2 has one constant, all single bits, and exactly the ordered distinct pairs i<j. Equality of its actual weighted vectors is proved iff every binary moment of degree<3 matches, and iff the diagonal-character moments match. Genuine distance>=3 supplies this vector equality for actual logical words; fiber support turns the whole-cube sums into the displayed full-fiber sums.'),
    'eq:sslp-three-layers': ([
        'SS.Sk', 'MainTheory.BinaryFeatureMoments.average',
        'MainTheory.BinaryFeatureMoments.average_eq_fiber',
        'MainTheory.ClassificationLevels.SSLPMomentDatum.geometry',
        'MainTheory.SSLPPipelineExact.pipeline_exact_three',
        'MainTheory.SSLPPipelineExact.code_of_sortedNormalForm'],
        'Reviewed as the workflow definition. The full modular fibers supply the LP weighted feature vectors; in the six-qubit executable classification SSLPMomentDatum.geometry is computed from those fibers. The final exact-code construction consumes a solved full KL frame. It does not infer all X/Y constraints from LP feasibility.'),
    'displaymath@633': ([
        'QECC.CodeProjector.preserves_iff_gate_conjugates', 'QECC.diagonalGate'],
        'The actual matrix theorem proves the code-preservation iff D(theta) P D(theta)-dagger=P, in both directions. The phase quotient is harmless because the displayed gate depends only on theta modulo integer periods.'),
    'eq:Gdiag': ([
        'QECC.CodeProjector.ProjectiveDiagonalGroup',
        'QECC.CodeProjector.projectiveClassMap',
        'QECC.CodeProjector.projectiveClass_eq_iff_gate_restrictions'],
        'The quotient of preserving phases by scalar code actions is the actual fixed-product-basis projective logical group: equality of classes is proved iff the two gate restrictions differ by one unit-circle scalar. The definition makes no finiteness assumption.'),
    'eq:number-operator': ([
        'QECC.numberOp', 'QECC.CodeProjector.zOp_eq_one_sub_two_numberOp',
        'MainTheory.NumberOperator.numberOp_apply',
        'MainTheory.DiagonalInfinitesimal.numberKernel_eq_half_one_sub'],
        'Both actual matrix and amplitude definitions identify N_j=(I-Z_j)/2 and its computational-basis eigenvalue x_j. The matrix subtraction and division use the physical complex operator.'),
    'eq:Nj-detection': ([
        'MainTheory.NumberDetectionBridge.single_site_iff',
        'MainTheory.NumberDetectionBridge.all_sites_iff'],
        'The new single-site theorem proves both directions with the exact complex scalar mu=(1-lambda)/2. The all-sites theorem additionally identifies the two existing real-scalar detection predicates. Neither direction nor the displayed scalar is left implicit.'),
    'displaymath@669': ([
        'QECC.PhaseVector', 'MainTheory.PhysicalTorusCells.AngleTorus',
        'MainTheory.PhysicalTorusCells.angleTorusHomeomorph',
        'MainTheory.PhysicalTorusCells.angleTorusHomeomorph_real'],
        'The quotient is modeled coordinatewise by AddCircle 1, with the proved homeomorphism to the product of complex unit circles. On a real vector that map is the stated full-turn exponential, so no radian/full-turn change is hidden.'),
    'eq:physical-diagonal-stabilizer': ([
        'QECC.CodeProjector.preservingPhases',
        'QECC.CodeProjector.preserves_iff_gate_conjugates'],
        'The actual preserving phases form an additive subgroup. Its predicate is proved equivalent to the displayed matrix conjugation identity; it is attached to the supplied code projector.'),
    'lem:uniform-rational-section': ([
        'QECC.integerMatrix_uniform_rational_lift'],
        'The universal denominator is selected before the real solution t and its integral image b. The arbitrary finite rectangular integer-matrix theorem returns an integer a with exactly A(t-a/Q)=0, including singular and empty-dimensional cases. The separate author-held prose about the homogeneous component is not certified here.'),
    'eq:uniform-rational-section': ([
        'QECC.integerMatrix_uniform_rational_lift'],
        'The displayed equation is precisely the conclusion of the arbitrary rectangular integer-matrix rational-section theorem; all casts and the positive common denominator are explicit.'),
    'eq:rational-generalized-inverse': ([
        'QECC.matrix_exists_generalizedInverse'],
        'For every rational square matrix B, the kernel proves existence of a rational G with B*G*B=B via a right inverse on the actual image and a linear projection. No invertibility of B is assumed.'),
    'displaymath@713': ([
        'MainTheory.RationalSectionSteps.cast_num_mulVec_div_den',
        'MainTheory.RationalSectionSteps.rational_section_chain',
        'QECC.integerMatrix_uniform_rational_lift'],
        'New public chain concerns the specific witness a=G.num*d and Q=G.den, not merely an existentially unrelated lift. It proves Ba/Q=BGd=BGBt=Bt under d=Bt; the actual uniform-section proof derives d=A-transpose*b=Bt from b=At.'),
    'displaymath@718': ([
        'MainTheory.RationalSectionSteps.gram_quadratic_form',
        'MainTheory.RationalSectionSteps.gram_euclidean_norm'],
        'The literal quadratic form of A-transpose*A equals the sum of squares and the square of the Euclidean L2 norm of A*v. Lean uses EuclideanSpace/WithLp 2 here, not the default function-space supremum norm.'),
    'thm:finite-projective-group': ([
        'QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives',
        'QECC.CodeProjector.FiniteDiagonalLogicalGroupConclusion',
        'QECC.CodeProjector.detects_real_of_hermitian',
        'QECC.PauliString.operator_hermitian',
        'QECC.PauliString.operator_singleZ'],
        'Read the current complete theorem against its actual conclusion structure: finite group, commutativity, and for every nonidentity class a reduced code-preserving physical representative of exact q, literal common gcd one and logical order dividing q. Detection of Hermitian Z admits real scalars, so the real-vector predicate introduces no stronger manuscript hypothesis. No Lie-group premise is assumed.'),
    'eq:all-Z-detection': ([
        'QECC.CodeProjector.DetectsSingleZ',
        'QECC.CodeProjector.detects_real_of_hermitian',
        'QECC.PauliString.operator_hermitian',
        'QECC.PauliString.operator_singleZ'],
        'The displayed all-sites scalar projector compressions are exactly single-Z detection; Hermiticity proves that complex scalars can be replaced by real ones even for the zero projector.'),
    'equation@231': ([
        'MainTheory.CodeSpec.OrthonormalFrame', 'MainTheory.CodeSpec.ExactCode',
        'MainTheory.GeneralColoredSubspaces.finrank_codeSpan',
        'MainTheory.ClassificationLevels.CodeProjector.ofFrame'],
        'Current Hilbert-space and rank convention checked: amplitudes on BitString n present H_n; the span of an orthonormal K-frame has finrank K, and its actual orthogonal projector is ofFrame. ExactCode additionally carries genuine KL detection and positive rank.'),
    'eq:general-KL': ([
        'MainTheory.QuantumRecovery.hermitian_projector_kl_iff_recovery',
        'MainTheory.KnillLaflammeRecovery.knillLaflamme_iff_scalar_recovery',
        'MainTheory.KnillLaflammeRecovery.finite_error_set_recovery',
        'MainTheory.QuantumRecovery.recovery_of_half_distance'],
        'The current arbitrary finite error-set equations are covered by the scalar-recovery iff without a TP hypothesis on that error set. The same recovery corrects every TP channel in its span. The normalized-channel projector iff supplies the displayed Hermitian Gram matrix; the separate distance theorem gives floor((d-1)/2) correction. TP is not silently imposed on the manuscript finite error set.'),
    'eq:KL': ([
        'MainTheory.ProjectorCompression.pauli_compression',
        'MainTheory.ProjectorCompression.tensor_compression',
        'SS.HasDistance', 'MainTheory.KLCodeBridge.projector_compression_iff'],
        'The current weight<d0 quantifier agrees with HasDistance. Orthonormal-frame compression is equivalent to the actual projector equation; arbitrary supported tensor operators are also detected. This equation does not identify X/Y matrix elements with probability moments.'),
    'eq:logical-basis-KL': ([
        'SS.KLCondition', 'SS.HasDistance',
        'MainTheory.KLCodeBridge.projector_compression_iff'],
        'Read in the stated orthonormal logical basis: compressed matrix equals lambda times identity iff the actual projector compression holds. KLCondition supplies every r,s matrix entry, including the complex off-diagonal entries. The subsequent unrestricted probability-moment sentence is an author-held prose issue and is not covered by this equation review.'),
    'eq:A-enumerator': ([
        'MainTheory.PauliKernelTrace.Aco_eq_sum_normSq_trace',
        'MainTheory.PauliKernelBTrace.BWeight_cast_eq_sum_trace',
        'MainTheory.CodeSpec.AWeight', 'MainTheory.CodeSpec.BWeight'],
        'Checked the current A normalization K^2 and B normalization K against the actual matrix traces. The historical Bco already contains a factor K, so BWeight=Bco/K^2 is exactly the displayed trace sum divided by K; no rank-two convention is used here.'),
    'eq:enumerator-polynomials': ([
        'MainTheory.MacWilliamsPolynomial.A_eq_sum',
        'MainTheory.MacWilliamsPolynomial.B_eq_sum'],
        'Both current homogeneous polynomials are the finite sums from w=0 to n with the stated normalized coefficients. Nat subtraction in the exponent is only evaluated over that range.'),
    'eq:quantum-MacWilliams': ([
        'MainTheory.MacWilliamsPolynomial.quantum_macwilliams'],
        'The current identity is proved for arbitrary n,K and all real x,y with the factor K/2^n, using the actual phase-free Pauli action. It is not only a six-qubit numerical specialization.'),
    'eq:enumerator-distance': ([
        'MainTheory.KLWeightEquality.AWeight_eq_BWeight_of_hasDistance'],
        'The stated normalized A_w=B_w holds for every natural weight w<d from actual HasDistance on an orthonormal K-frame, with arbitrary n and K.'),
    'eq:LU-equivalence': ([
        'MainTheory.LocalUnitaryClosure.luEquivalent_iff_tensor',
        'MainTheory.LocalUnitaryEnumerators.enumerators_luEquivalent'],
        'Checked actual projector conjugation by arbitrary one-qubit U(2) factors and a physical-qubit permutation. Reindexing factors matches the displayed product/permutation order. Both normalized enumerators are invariant; their equality is not asserted to imply LU equivalence.'),
    'eq:transversal-product': ([
        'MainTheory.LocalTensorKernel.tensorKernel',
        'MainTheory.LocalTensorKernel.tensorKernel_unitary',
        'MainTheory.FiniteTensorKernel.tensor'],
        'The current single-block product is the literal finite tensor kernel of one-qubit matrices. Unitarity is derived from both unitary identities for each factor. This entry reviews the product definition, not an unformalized fault-propagation narrative.'),
    'eq:code-preserving-unitary': ([
        'MainTheory.CodePreservingUnitary.PreservesProjector',
        'MainTheory.CodePreservingUnitary.preservesProjector_iff',
        'MainTheory.CodePreservingUnitary.mapsTo_of_preservesProjector'],
        'PreservesProjector unfolds to the displayed U P U-dagger=P. For a unitary kernel it maps the code span into itself. The definition is not replaced by the weaker maps-to predicate without unitarity.'),
    'eq:Dtheta': ([
        'MainTheory.RealGate.realGate', 'MainTheory.RealGate.angle',
        'MainTheory.PhaseSectorBridge.realGateEnd',
        'MainTheory.LocalPhaseAngle.exists_angleVector',
        'MainTheory.LocalPhaseAngle.diagonalValue_eq_exp'],
        'Current phases are in full turns. The amplitude action is exp(2*pi*i*sum theta_j x_j); diagonalValue_eq_exp identifies it with the tensor product in the fixed local product basis. The local-phase existence theorem covers arbitrary one-site unit phases.'),
    'eq:Daq': ([
        'MainTheory.Gate.diag', 'MainTheory.Gate.gate', 'SS.weight',
        'MainTheory.GlobalClassificationBridge.diagonalValue_finiteLocalPhase',
        'MainTheory.D3NormalizedFiniteToReal.canonicalRoot_primitive'],
        'Checked the finite representative in the current fixed basis: the ZMod q subset sum is the exponent of the canonical exp(2*pi*i/q) root. The finite local-phase presentation and the actual amplitude gate agree. q>=2 in context supplies NeZero q.'),
    'eq:primitive': ([
        'MainTheory.Gate.Primitive', 'MainTheory.GateGCD.primitive_iff_gcd',
        'MainTheory.GatePrimitiveConverse.primitive_iff_exact_order'],
        'The new gcd bridge proves the literal iterated gcd(q,a_1,...,a_n)=1 equivalent to the existing common-divisor predicate. The current reduced-form next sentence is the proved iff between primitivity and exact physical order q; it does not assert minimality among representatives.'),
    'eq:qmin': ([
        'MainTheory.GeneralLiftOrder.HasPrimitiveLift',
        'MainTheory.SharpSectorZDetection.qMinOfExists',
        'MainTheory.SharpSectorZDetection.qMinOfExists_spec',
        'MainTheory.SharpSectorZDetection.qMinOfExists_le'],
        'Read with the current explicit fixed-code, fixed-product-basis restriction: HasPrimitiveLift records precisely a primitive finite diagonal representative of the supplied projective class. Under the displayed existence assumption qMinOfExists is attained and no larger than any admissible q. This interface does not require distance>=2 and does not minimize over arbitrary physical unitaries.'),
    'eq:subset-sum': ([
        'SS.weight', 'MainTheory.OuterCompleteness.weight_wordBitString_eq_subsetSum'],
        'The current A_a(x) is the modular sum in ZMod q. The six-bit executable subsetSum convention is identified with it by the wordBitString bridge, not assumed to be a second phase convention.'),
    'eq:fiber': ([
        'SS.Sk', 'SS.mem_Sk',
        'MainTheory.OuterCompleteness.mem_gateResidueFiber_iff'],
        'The current full solution set S_b is exactly the level set of SS.weight; it is not the smaller positive-amplitude support. The enumeration membership bridge relates this full set to the literal mask representation.'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'results/paper-claims-20261003.json'
    ledger = json.loads(path.read_text(encoding='utf8'))
    paper_claims.validate(ledger, sources=paper_claims.sources_for_version('20261003'))
    if ledger['sources'] != SOURCES:
        raise ValueError('The reviewed manuscript context changed')
    decisions = []
    for entry in ledger['claims']:
        suffix = entry['id'].removeprefix('main.tex:')
        if not entry['id'].startswith('main.tex:') or suffix not in REVIEWS:
            continue
        names, review = REVIEWS[suffix]
        entry.update(status='covered', lean_declarations=names,
                     review='20261003 current-source review (2026-10-04): ' + review)
        decisions.append({k: entry[k] for k in ('id', 'statement_sha256', 'status', 'lean_declarations', 'review')})
    if len(decisions) != len(REVIEWS):
        raise ValueError('Missing reviewed statement')
    evidence = {'schema': 1, 'sources': SOURCES, 'claims': decisions,
                'verification': 'Full content build and selected-release axiom gate are separate required checks.'}
    if args.apply:
        path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        (ROOT / 'artifacts/orbit-certification-20261003/core-correspondence-review.json').write_text(
            json.dumps(evidence, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        paper_claims.validate(ledger, sources=paper_claims.sources_for_version('20261003'))
    print('Reviewed current-source core claims:', len(decisions))


if __name__ == '__main__':
    main()
