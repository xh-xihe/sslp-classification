#!/usr/bin/env python3
"""Explicit current-source review of phase-sector geometry and replacement."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
from review_core_claims_20261003 import SOURCES

REVIEWS = {
    'displaymath@1339': (['QECC.eigenvalueRatio', 'QECC.CodeProjector.preservingPhaseRatioHom',
        'QECC.CodeProjector.exists_injective_projectivePhaseRatio_of_two_sectors',
        'QECC.CodeProjector.projectiveDiagonalGroup_isAddCyclic_of_rankTwo'],
        'The actual preserving phases restrict to scalars on the two actual one-dimensional sectors. Their phase difference factors through the actual scalar quotient with zero kernel; toCircle converts the difference to the written eigenvalue ratio. This proves cyclicity of the actual group.'),
    'eq:rank-two-color': (['QECC.CodeProjector.card_activeResidue_eq_two_of_projectiveClass_ne_zero',
        'QECC.CodeProjector.GeneralSSLPData', 'QECC.isUnit_of_addOrderOf_eq_modulus'],
        'Rank two and a nonzero logical class give exactly two rank-one sectors. The sole nonzero anchored color has full order m and therefore gcd one with m.'),
    'displaymath@1362': (['QECC.exists_unit_lift_inverse', 'QECC.exists_unit_lift_mul_eq_one'],
        'For every positive q divisible by m, reduction of units modulo q onto units modulo m is surjective. Applying it to gamma inverse gives exactly the unit needed here; the standard unitsMap theorem proves this with no coprimality requirement between m and q/m.'),
    'displaymath@1379': (['QECC.unit_mul_colorEmbed', 'QECC.exists_unit_scaling_colorEmbed_eq_one',
        'QECC.CodeProjector.exists_normalized_rankTwo_activeResidues'],
        'Unit multiplication commutes with the q/m embedding, and the selected unit sends the second residue to q/m without changing the physical order.'),
    'displaymath@1391': (['QECC.diagonalGate_phaseHom_mulVec_of_mem_fiberSubspace',
        'MainTheory.ScaledColorPhases.normalized_rank_two_phase',
        'MainTheory.SSLPConverse.orderOf_intrinsicClass_resolutionOfPair'],
        'The actual normalized pair has eigenvalues one and exp(2*pi*i/m), whose ratio has exact order m. The pair converse retains the full supplied KL equations.'),
    'eq:three-layers': (['QECC.CodeProjector.general_sslp_canonical_normal_form',
        'QECC.CodeProjector.sslp_sector_probabilities_and_moments', 'QECC.general_sslp_directSum_converse'],
        'Current staged structure checked: full-fiber spectral support is necessary and exhaustive, moments are necessary projections of diagonal Z equations, and exact KL completion is the sufficient converse. Moment feasibility alone is not declared sufficient.'),
    'eq:Talpha': (['MainTheory.PhaseSectorFull.sectorSupport',
        'MainTheory.PhaseSectorFull.sectorProjectorKernel_diag'],
        'The actual logical-sector projector diagonal is the sum of squared basis amplitudes; its positive locus is precisely the intrinsic support used here.'),
    'eq:phase-sector-congruence': (['MainTheory.PhaseSectorFull.phase_congruence',
        'MainTheory.ZDetection.phaseSectors_of_zDetects'],
        'On the actual positive sector support the original real physical subset sum equals its logical eigenphase modulo one, with disjoint supports for distinct phases.'),
    'lem:phase-sectors': (['MainTheory.PhaseSectorFull.phaseSectorFull_package',
        'MainTheory.SectorMeanValue.sectorMean_eq_klScalar',
        'MainTheory.NumberDetectionBridge.single_site_iff'],
        'The rank-normalized actual projector diagonal is positive exactly on its intrinsic support and has mass one. Single-Z compression gives every coordinate mean (1-lambda_j)/2. The result applies to sectors of arbitrary positive rank.'),
    'eq:palpha': (['MainTheory.PhaseSectorFull.sectorProbability',
        'MainTheory.PhaseSectorFull.sectorProjectorKernel_diag'],
        'Probability is the actual sector-projector diagonal divided by its rank, restricted to the positive diagonal locus.'),
    'eq:common-mean': (['MainTheory.SectorMeanValue.sectorMean_eq_klScalar',
        'MainTheory.PhaseSectorFull.sectorMean_eq_of_ZDetects',
        'MainTheory.NumberDetectionBridge.single_site_iff'],
        'Every sector has the same actual occupation mean; the literal number/Z operator bridge identifies the written scalar mu.'),
    'displaymath@1484': (['MainTheory.PhaseSectorFull.sectorProbability_sum_eq_one',
        'QECC.CodeProjector.trace_sectorProjector'],
        'The trace of a positive-rank orthogonal sector projector is its rank, and zero diagonal values outside its intrinsic support contribute no mass.'),
    'displaymath@1491': (['MainTheory.SectorProjectorIdentities.sector_supported_occupation_trace',
        'MainTheory.SectorMeanValue.sectorMean_eq_klScalar'],
        'Compressing the number operator to each sector and taking its trace gives the stated unnormalized coordinate first moment mu_j k_alpha.'),
    'lem:common-mean-rational-replacement': (['MainTheory.CommonMeanReplacement.support_value',
        'MainTheory.CommonMeanReplacement.replacement_on_direct_sum'],
        'New generic proof matches the current arbitrary supports/distributions and subspaces. A within-support constant is its probability average and equals delta dot mu. Actual physical matrix action on the full sum of supported subspaces differs by exactly exp(2*pi*i*delta dot mu); no rationality of probabilities or KL hypothesis is added.'),
    'displaymath@1505': (['MainTheory.CommonMeanReplacement.average'],
        'The common coordinate mean is supplied for arbitrary finite supports; the weighted support phase equals the dot product with that mean.'),
    'displaymath@1510': (['MainTheory.CommonMeanReplacement.support_value'],
        'Within-support equality of delta dot x is equivalent to vanishing on each difference x-y, and it is exactly the hypothesis of the generic support-value theorem.'),
    'displaymath@1516': (['MainTheory.CommonMeanReplacement.support_value'],
        'The same value delta dot mu holds on every support and hence on their union, because every sector distribution is normalized and has this common mean.'),
    'displaymath@1522': (['MainTheory.CommonMeanReplacement.replacement_on_direct_sum'],
        'The actual diagonal matrix action on every vector of the subspace sum has precisely the displayed exponential scalar. Setting t=theta and delta=theta-prime minus theta gives the current formula.'),
    'displaymath@1537': (['MainTheory.CommonMeanReplacement.average',
        'MainTheory.CommonMeanReplacement.support_value'],
        'Finite averaging, normalization and interchange of the coordinate/support sums prove every equality in this display.'),
    'displaymath@1547': (['MainTheory.CommonMeanReplacement.replacement_on_supported_union'],
        'The pointwise physical action identity holds for every vector supported in the union, so in particular for every vector of any stated E_alpha.'),
    'eq:common-phase-shift': (['MainTheory.CommonMeanReplacement.support_value'],
        'Equal lifted sector equations force within-sector constancy of the difference. Averaging with the common means gives this equality on the union.'),
    'eq:rational-replacement': (['MainTheory.CommonMeanReplacement.replacement_on_direct_sum'],
        'Applied to the actual intrinsic spectral subspaces, the full code restriction of the two physical matrices has exactly the stated common scalar.'),
    'displaymath@1866': (['MainTheory.Covariance.centeredHull_eq_affineSpan'],
        'For an anchor in a nonempty set, affine span is that anchor plus the span of all differences to it, independently of the anchor.'),
    'lem:positive-affine-moments': (['MainTheory.PositiveAffineMoments.zero_transfer',
        'MainTheory.PositiveAffineFunctionExpansion.affineSpan_eq_of_coordinate_squares'],
        'New theorem covers arbitrary finite real point sets, of different cardinalities, with strictly positive weights. Equality of all affine squared expectations transfers their zero sets and gives equality of affine spans through the dual annihilator. It is not restricted to binary code supports.'),
    'eq:affine-square-moments': (['MainTheory.PositiveAffineFunctionExpansion.expansion',
        'MainTheory.PositiveAffineFunctionExpansion.affineSpan_eq_of_coordinate_squares',
        'QECC.affineSquareExpectation_expansion'],
        'The generic affine-map squared expectation is the displayed arbitrary affine functional c+w dot x. The separate binary moment expansion supplies this hypothesis for code supports.'),
    'eq:same-affine-span': (['MainTheory.PositiveAffineFunctionExpansion.affineSpan_eq_of_coordinate_squares'],
        'The conclusion is equality of actual affine subspaces of R^n for the arbitrary finite positive-weight point sets in this lemma.'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    art = ROOT / 'artifacts/orbit-certification-20261003'
    for name in ('common-mean-replacement-build.json', 'positive-affine-moments-build.json',
                 'positive-affine-expansion-build.json'):
        if json.loads((art / name).read_text(encoding='utf8'))['status'] != 'PASS':
            raise ValueError('Unpassed geometry proof: ' + name)
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
        if suffix not in REVIEWS:
            continue
        names, review = REVIEWS[suffix]
        entry.update(status='covered', lean_declarations=names,
                     review='20261003 current-source review (2026-10-04): ' + review)
        decisions.append({k: entry[k] for k in ('id', 'statement_sha256', 'status', 'lean_declarations', 'review')})
    if len(decisions) != len(REVIEWS):
        raise ValueError('Missing reviewed geometry statement')
    if args.apply:
        path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        (art / 'phase-geometry-correspondence-review.json').write_text(
            json.dumps({'schema': 1, 'sources': SOURCES, 'claims': decisions}, ensure_ascii=False, indent=2) + '\n',
            encoding='utf8')
    print('Reviewed current-source phase-geometry claims:', len(decisions))


if __name__ == '__main__':
    main()
