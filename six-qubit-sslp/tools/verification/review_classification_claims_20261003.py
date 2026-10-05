#!/usr/bin/env python3
"""Current-source review of the six-qubit definitions and four main results."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
from review_core_claims_20261003 import SOURCES

IMAGE_ROOTS = ['MainTheory.DirectoryEnumeratorImages.orbit' + str(i) + '_image'
               for i in (7, 8, 9, 10, 11, 16, 21, 22, 23, 36, 45)]
GROUPS = [
    (['six:eq:qcutoff'], 'covered',
     ['MainTheory.SSLPCompleteness.completeness_six_qubit',
      'MainTheory.Generated.BinaryBetaSixKernel.Certificate.betaExact'],
     'Read the fixed-basis, nontrivial distance-three search scope. The kernel completeness theorem retains a primitive bounded representative, its logical order, full distance and actual support; betaSix gives the literal exhaustive cutoff nine.'),
    (['displaymath@2095', 'six:eq:Daq', 'six:eq:primitive', 'six:eq:fibers',
      'six:eq:sslp0', 'six:eq:sorted'], 'covered',
     ['MainTheory.LabelledGates.canonicalRoot',
      'MainTheory.LabelledGates.canonicalRoot_isPrimitiveRoot',
      'MainTheory.Gate.diag', 'MainTheory.Gate.gate',
      'MainTheory.GateGCD.primitive_iff_gcd',
      'MainTheory.Gate.pow_eq_one_iff',
      'MainTheory.FiniteGateCanonicalNormalization.primitive_addOrder',
      'SS.Sk', 'MainTheory.SortedForm.SortedNormalForm',
      'MainTheory.SSLPCompleteness.completeness_six_qubit'],
     'Read the actual sixth-coordinate tensor action, full residue fibers (including unused zero-amplitude strings), normalized supported words and sorted residues. The physical exact-order criterion is literal gcd one, with both directions. Sorting belongs to the proved complete normalization, not an extra restriction on codes.'),
    (['def:six-sslp-orbits', 'eq:Kr-definition'], 'covered',
     ['MainTheory.ClassificationLevels.SSLPMomentDatum',
      'MainTheory.ClassificationLevels.SSLPMomentDatum.geometry',
      'MainTheory.ClassificationLevels.SSLPMomentEquivalent',
      'MainTheory.CubeCompletionTransport.Completion',
      'MainTheory.CubeCompletionTransport.completion_of_fiberEquivalent',
      'MainTheory.PaperReductionChain.six_66_orbits',
      'MainTheory.Generated.FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries',
      'MainTheory.CompletionCodeBridge.code'],
     'The current candidate relation is checked on full fibers with exact cube actions, preserving q and m. The actual finite rank-compatible pipeline has 66 distinct classes. A completion carries normalized complex words and all Pauli KL equations; its exact-code frame is constructed from those same words. Moment feasibility alone is not used as completion.'),
    (['def:six-classification-levels', 'eq:Wr-definition'], 'covered',
     ['MainTheory.ClassificationLevels.IntrinsicProjectiveDiagonalLogicalGroup',
      'MainTheory.GeneralFiniteness.isCyclic',
      'MainTheory.CubeCompletionTransport.Completion',
      'MainTheory.EnumeratorOrbitTransport.completionImage',
      'MainTheory.EnumeratorOrbitTransport.WImage_eq_orbitImage',
      'MainTheory.EnumeratorOrbitTransport.completionImage_actFibers',
      'MainTheory.ClassificationLevels.LUEquivalent',
      'MainTheory.LocalMonomialSixBridge.luEquivalent_of_codeEquivalent'],
     'Reviewed all four current definitions separately: the entire intrinsic group; realizable chosen symmetry data; actual normalized enumerator vectors of full KL completions; and physical-projector LU equivalence. The actual image transport proves every enumerator coordinate is invariant under the candidate cube relation. The monomial relation maps into physical LU equivalence.'),
    (['six:thm:global-status', 'eq:six-intrinsic-groups', 'eq:M36'], 'covered',
     ['MainTheory.IntrinsicOrderAudit.orderOf_mem',
      'MainTheory.IntrinsicOrderAudit.natCard_mem',
      'MainTheory.IntrinsicOrderAudit.orderOf_le_five',
      'MainTheory.GeneralFiniteness.isCyclic',
      'MainTheory.SixQubitIntrinsicAttainment.two_three_five_attained'],
     'The actual intrinsic quotient is finite cyclic; its nontrivial whole-group cardinality and every element order lie in the displayed lists. Actual code constructions attain each of two, three and five. The maximum five therefore has both an upper bound and an actual witness.'),
    (['thm:six-15-sslp-realization-orbits', 'six:eq:15-sslp-realization-orbits',
      'displaymath@2304'], 'covered',
     ['MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys',
      'MainTheory.RealizationOrbits15.card_realization_orbits',
      'MainTheory.RealizationOrbits15.realizationKeys_paperIds',
      'MainTheory.RealizationOrbits15.realizationKeys_orderDistribution',
      'MainTheory.PaperSupplementaryNoGo.hasCompletion_iff_paperOrbitId',
      'MainTheory.OrbitNumberingBridge.paperOrbitId_paperKey'],
     'Read the literal fifteen paper numbers and the 11:3:1 distribution. Each positive key has actual normalized full-KL words; each negative key has an actual no-completion theorem. Exact finite paper-number/cube-witness bridges prevent substituting directory indices for the paper numbers.'),
    (['eq:Lalpha'], 'covered',
     ['MainTheory.WImages.FI', 'MainTheory.WImages.FII',
      'MainTheory.WImages.E1A', 'MainTheory.Levels.E2A', 'MainTheory.WImages.R5A',
      'MainTheory.ProvedWEUnion.FI_one', 'MainTheory.ProvedWEUnion.FI_zero',
      'MainTheory.ProvedWEUnion.FII_one'],
     'Every one of the seven displayed coordinates, including the isolated rational point and all three endpoint identities, matches the current kernel definitions.'),
    (['tab:six-realizable-classes'], 'expository',
     IMAGE_ROOTS + ['MainTheory.Generated.OrbitTableNumericData.all_rows',
                    'MainTheory.Generated.OrbitTableNumeric.all_labeled_equivalences',
                    'MainTheory.RealizationOrbits15.realizationKeys_paperIds',
                    'MainTheory.OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive'],
     'Reviewed the fifteen literal rows against the paper table payload and actual labeled fiber equivalences. The listed eleven exact images and the class-36 LU uniqueness have kernel proofs. Open is a manuscript progress annotation, not a mathematical proposition: the newly proved orbit-2/3 images supersede that annotation without changing the frozen main text.'),
    (['eq:global-W-set'], 'covered',
     ['MainTheory.GlobalWeightSet.globalWSet', 'MainTheory.GlobalWeightSet.aweight_eq'],
     'The actual full-code-space enumerator set has no transversal-gate premise. Its trace normalization is identified with the frame definition, retaining the projectively trivial sector.'),
    (['eq:global-WE-conjecture'], 'conjecture',
     ['MainTheory.GlobalWeightSet.GlobalWEConjecture',
      'MainTheory.GlobalWeightSet.globalWSet', 'MainTheory.WEStrictInclusion.conjecturedImages'],
     'Read the question-mark equality and the lower M endpoint 3/5. This is encoded as a proposition, not asserted as a proved theorem; proving that stated conjecture is not a manuscript certification obligation.'),
    (['thm:six-WE-status', 'eq:W36-main', 'eq:W7-main', 'eq:W-E2-main',
      'eq:proved-WE-union'], 'covered', IMAGE_ROOTS +
     ['MainTheory.EnumeratorOrbitTransport.WImage_eq_orbitImage',
      'MainTheory.ProvedWEUnion.provedImages_eq'],
     'Read every literal image and closed interval in Result III. The actual directory image equalities transport full KL complex encoders and all normalized A coordinates through exact fiber equivalences; they include both the converse and attainment. Their representative union is exactly the stated L interval, upper M segment and isolated point. Historical open-status prose is excluded from the mathematical equality.'),
    (['eq:four-open-L-inclusion'], 'covered',
     ['MainTheory.WImageOpenL.FI_subset_orbit1', 'MainTheory.WImageOpenL.FI_subset_orbit2',
      'MainTheory.WImageOpenL.FI_subset_orbit3', 'MainTheory.WImageOpenL.FI_subset_orbit4',
      'MainTheory.DirectoryEnumeratorImages.orbit1_attainment',
      'MainTheory.DirectoryEnumeratorImages.orbit2_attainment',
      'MainTheory.DirectoryEnumeratorImages.orbit3_attainment',
      'MainTheory.DirectoryEnumeratorImages.orbit4_attainment'],
     'All four actual full-KL constructions attain the entire L interval, including both endpoints; exact cube equivalence transfers the families to the candidate classes.'),
    (['eq:four-open-M-inclusion'], 'covered',
     ['MainTheory.WImageOrbit4M.FII_subset_WImage_orbit1_inter_orbit4'],
     'The actual family has the closed interval [2/3,1] and full KL distance three, and its two fiber presentations put each same enumerator in both classes one and four.'),
    (['rem:four-open-orbits', 'eq:W23-conjecture'], 'conjecture',
     ['MainTheory.Orbit2FullImage.directory_image',
      'MainTheory.Orbit3FullImage.directory_image',
      'MainTheory.WImageOrbit4M.FII_subset_WImage_orbit1_inter_orbit4'],
     'The combined align block contains both the conjectural W2/W3 equality and the separate W1/W4 union conjecture. W2/W3 is now actually proved by the original-encoder kernel bridges. The W1/W4 converse remains a stated research conjecture. The remaining sentences describe historical numerical/proof status, not extra universal code assertions.'),
    (['eq:six-C5-shells', 'eq:six-C5-code0'], 'covered',
     ['MainTheory.Orbit36CanonicalAmplitudes.all_amplitudes',
      'MainTheory.Orbit36RootOfUnity.rho_eq_exp',
      'SixQubit.Orbit36Class.canonical_topForm',
      'SixQubit.Orbit36Code.c36_vanishes_off_S0',
      'SixQubit.Orbit36Code.d36_vanishes_off_S1',
      'SixQubit.Orbit36Code.canonical_is_code',
      'MainTheory.Orbit36LUBridge.canonicalFrame'],
     'Reviewed all printed x1...x6 ket strings. The six vertex coefficients are 1/sqrt(10); the six edge coefficients have the printed opposite-pair 1,omega,omega^2 pattern and modulus 1/sqrt(15). The actual canonical_topForm determines every top-word coefficient with the stated signs and complex conjugation. Vanishing outside the two twelve-string lists and normalized full KL prove that these literal vectors form the claimed orthonormal code.'),
    (['eq:six-C5-gate-data', 'eq:six-C5-logical-action'], 'covered',
     ['SixQubit.Orbit36Code.av', 'SixQubit.Orbit36Code.S0_eq_fiber',
      'SixQubit.Orbit36Code.S1_eq_fiber',
      'MainTheory.WImageIntrinsicBridge.orbit36_angle_primitive',
      'MainTheory.WImageIntrinsicBridge.rootFive_primitive',
      'MainTheory.PhaseSector.eigen_of_ssCondition', 'MainTheory.Gate.diag_pow',
      'MainTheory.MinimumLengthOrderFive.canonical_attains'],
     'Read the actual vector (1,1,1,1,2,3), residue supports zero and four, and standard fifth root. Exact fiber identities yield eigenvalues 1 and zeta^4; taking the fourth power gives zeta^16=zeta. The primitive criterion certifies physical order five and the actual projective representation has order five.'),
    (['thm:unique-C5-LU'], 'covered',
     ['MainTheory.OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive',
      'MainTheory.OrderFiveCodeRigidity.luEquivalent_of_orderFive',
      'SixQubit.Orbit36Certified.original_equivalent_canonical',
      'MainTheory.Orbit36LUBridge.original_projector_luEquivalent_canonical'],
     'The source is an arbitrary exact six-qubit code with an actual intrinsic element of order five. Complete directory/no-go transport forces class 36. Its amplitude rigidity uses only physical permutations, X flips and diagonal phases, and the projector bridge gives the stated LU class. Equal enumerators are not used as a substitute for this rigidity.'),
    (['cor:six-C5-minimum-length'], 'covered',
     ['MainTheory.MinimumLengthOrderFive.minimum_length',
      'MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three',
      'MainTheory.MinimumLengthOrderFive.canonical_attains'],
     'Read the arbitrary single-block transversal scope. The theorem starts from actual one-qubit unitary tensor factors, their actual logical matrix and faithful adjoint order five. KL-preserving padding and actual local diagonalization prove n>=6; the literal canonical code attains six and physical projector LU uniqueness retains the original distance>=3.'),
    (['six:rem:global-family-caveat'], 'expository',
     ['MainTheory.ClassificationLevels.LUEquivalent',
      'MainTheory.EnumeratorOrbitTransport.completionImage',
      'MainTheory.OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive'],
     'This paragraph states unresolved code-level classification tasks and distinguishes amplitude/projector equivalence from an enumerator vector. It asserts no missing universal theorem beyond the separately kernel-proved class-36 uniqueness.'),
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    reviews = {}
    for ids, status, declarations, review in GROUPS:
        for ident in ids:
            if ident in reviews:
                raise ValueError('Duplicate review: ' + ident)
            reviews[ident] = (status, declarations, review)
    path = ROOT / 'results/paper-claims-20261003.json'
    ledger = json.loads(path.read_text(encoding='utf8'))
    paper_claims.validate(ledger, sources=paper_claims.sources_for_version('20261003'))
    if ledger['sources'] != SOURCES:
        raise ValueError('The reviewed manuscript context changed')
    decisions = []
    for entry in ledger['claims']:
        if not entry['id'].startswith('main.tex:'):
            continue
        suffix = entry['id'].removeprefix('main.tex:')
        if suffix not in reviews:
            continue
        status, declarations, review = reviews[suffix]
        entry.update(status=status, lean_declarations=declarations,
                     review='20261003 current-source review (2026-10-04): ' + review)
        decisions.append({k: entry[k] for k in ('id', 'statement_sha256', 'status', 'lean_declarations', 'review')})
    if len(decisions) != len(reviews):
        raise ValueError('Missing reviewed classification statement')
    if args.apply:
        path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        (ROOT / 'artifacts/orbit-certification-20261003/classification-correspondence-review.json').write_text(
            json.dumps({'schema': 1, 'sources': SOURCES, 'claims': decisions}, ensure_ascii=False, indent=2) + '\n',
            encoding='utf8')
    print('Reviewed current-source classification claims:', len(decisions))

if __name__ == '__main__':
    main()
