#!/usr/bin/env python3
"""Explicit current-source review of the general and rank-two normal forms."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
from review_core_claims_20261003 import SOURCES

REVIEWS = {
    'thm:general-sslp-normal-form': (
        ['QECC.CodeProjector.general_sslp_canonical_normal_form',
         'QECC.CodeProjector.HasCanonicalGeneralSSLPData', 'QECC.general_sslp_directSum_converse'],
        'Read both directions against the current statement. The forward theorem retains the chosen projective element, produces a reduced physical representative, sorted local-X/permutation transport, all positive active-sector ranks, distinct primitive colors and the full colored fiber inclusions. The direct-sum converse constructs the actual sum projector and proves its rank, exact logical order and the supplied full target KL distance.'),
    'eq:general-sslp-outer-data': (
        ['QECC.CodeProjector.HasCanonicalGeneralSSLPData', 'QECC.ReducedDiagonalRepresentative.commonGCD_eq_one'],
        'The current modulus is the exact physical order of one reduced representative. Canonical data give sorted ZMod values, literal common gcd one and preservation of physical and projective orders; divisibility comes from the same intrinsic witness.'),
    'eq:general-sslp-colors': (
        ['QECC.CodeProjector.GeneralSSLPData', 'QECC.CodeProjector.sum_finrank_activeResidue',
         'QECC.CodeProjector.activeResidue_finrank_pos', 'QECC.colorPrimitive_iff_gcd_eq_one'],
        'The active-residue index has positive sector dimensions summing to K. Its colors are injective with anchor zero, and the literal gcd condition is equivalent to the proved color primitivity.'),
    'eq:general-colored-fibers': (
        ['QECC.CodeProjector.HasCanonicalGeneralSSLPData',
         'QECC.CodeProjector.canonicalPhaseSectorEquiv_support'],
        'The canonical sector equivalence identifies the transported dimensions and sends each actual sector into the full fiber labeled (q/m) gamma. Zero coefficients remain allowed: the conclusion is inclusion, not equality with the ambient fiber.'),
    'displaymath@1124': (
        ['QECC.CodeProjector.phaseSector', 'QECC.range_fiberProjector_mulVecLin'],
        'The concrete sector is code intersected with the span of computational basis strings of residue b; the literal fiber projector has exactly that range.'),
    'displaymath@1134': (
        ['QECC.CodeProjector.phaseSectorDecomposition', 'QECC.CodeProjector.sum_phaseSectorComponent_coe'],
        'The code decomposes into these actual spectral sectors. Components preserve the code, and their sum reconstructs every code vector.'),
    'displaymath@1141': (
        ['QECC.CodeProjector.sum_finrank_activeResidue', 'QECC.CodeProjector.activeResidue_finrank_pos'],
        'Only nonzero sectors are indexed; their positive dimensions have sum K.'),
    'displaymath@1150': (['QECC.xorCoefficient'],
        'The coefficient after local-X transport is exactly a_j or -a_j according to the corresponding bit, in the same ZMod q.'),
    'displaymath@1154': (['QECC.reindexOperator_xor_diagonalGate_phaseHom'],
        'The one-site identity is the n=1 specialization of the actual diagonal matrix conjugation theorem, with its subset-sum common scalar retained.'),
    'eq:general-local-X-gate': (['QECC.reindexOperator_xor_diagonalGate_phaseHom'],
        'Actual computational-basis XOR conjugation gives precisely the scalar from A_a(t) times the gate with signed coefficients.'),
    'eq:general-local-X-residues': (['QECC.subsetSum_xorEquiv'],
        'The signed-coefficient subset sum at x xor t is A_a(x)-A_a(t), with no change of residue convention.'),
    'displaymath@1178': (['QECC.CodeProjector.relativeResidues', 'QECC.CodeProjector.relativeResidues_anchor'],
        'The relative residue subtracts the chosen anchor and makes its value zero.'),
    'displaymath@1187': (['QECC.CodeProjector.nsmul_projectiveClass_eq_zero_iff',
        'QECC.CodeProjector.projectiveOrder_eq_relativeResiduesOrder'],
        'Scalar powers of the actual preserving gate are equivalent to annihilating every relative residue. Their least positive exponent is its projective order.'),
    'displaymath@1193': (['QECC.mem_range_colorEmbed_iff', 'QECC.existsUnique_color_of_nsmul_eq_zero'],
        'When m divides q, precisely the residues killed by m arise from the injective multiplication-by-q/m embedding of ZMod m; each has a unique color.'),
    'displaymath@1199': (['QECC.CodeProjector.sslp_color_residue_formula',
        'QECC.CodeProjector.exists_primitive_sslp_colors'],
        'The color of each active relative residue is the unique preimage in the q/m embedding.'),
    'displaymath@1205': (['QECC.addOrderOf_colorVector'],
        'The exact additive order of the current finite color vector is m divided by its common gcd with m, including an anchor zero.'),
    'displaymath@1218': (['QECC.CodeProjector.canonicalPhaseSectorEquiv_support',
        'QECC.CodeProjector.HasCanonicalGeneralSSLPData'],
        'The actual transported sector is supported on the stated full colored fiber; canonical data preserve ranks, both orders and every KL distance.'),
    'displaymath@1235': (['QECC.FiberProjectorFamily.totalProjector'],
        'The converse total operator is literally the finite sum of the mutually orthogonal sector projectors.'),
    'displaymath@1239': (['QECC.FiberProjectorFamily.rank_totalProjector',
        'QECC.FiberProjectorFamily.rank_totalProjector_eq_sum_multiplicity'],
        'Orthogonality gives the rank of the actual sum projector as the sum of the positive component ranks.'),
    'displaymath@1248': (['QECC.diagonalGate_phaseHom_mulVec_of_mem_fiberSubspace',
        'MainTheory.ScaledColorPhases.scaled_color_phase'],
        'The physical gate acts on each full residue fiber by its residue phase; scaling by q/m gives the displayed exp(2*pi*i*gamma/m).'),
    'displaymath@1257': (['QECC.addOrderOf_colorVector',
        'QECC.FiberProjectorFamily.projectiveOrder_eq_of_primitive_colors'],
        'Primitivity of the anchored colors makes the least common scalar power exactly m on the constructed direct sum.'),
    'eq:general-sector-probabilities': (['QECC.CodeProjector.sectorDistribution',
        'QECC.CodeProjector.sslp_sector_probabilities_and_moments'],
        'The actual sector-projector diagonal divided by its positive rank is nonnegative, normalized and zero outside its complete labeled fiber.'),
    'eq:general-sector-moments': (['QECC.CodeProjector.sslp_sector_probabilities_and_moments',
        'QECC.CodeProjector.sectorMoment_eq_of_detects_binaryMonomial'],
        'Full low-weight Pauli detection implies equality of every binary monomial moment of cardinality below d0 across all active sectors, by the exact Z-Pauli expansion.'),
    'cor:rank-two-sslp': (['QECC.CodeProjector.rankTwo_sslp_canonical_normal_form',
        'QECC.CodeProjector.HasCanonicalRankTwoSSLPNormalForm',
        'MainTheory.PaperGeneralSSLP.rank_two_sslp_converse'],
        'Read the current generator normalization against the actual rank-two theorem: the fixed-basis group is finite cyclic, a reduced representative has m dividing q, and the permitted unit power/local-X/permutation/interchange operations produce orthonormal states in full fibers 0 and q/m. The converse uses full KL, not moments alone.'),
    'eq:K2-bound': (['QECC.CodeProjector.rankTwo_sslp_canonical_normal_form'],
        'The chosen generator has a finite reduced physical representative, with logical order dividing its physical order.'),
    'eq:0L-fiber': (['QECC.CodeProjector.HasRankTwoCanonicalNormalization',
        'QECC.CodeProjector.rankTwo_sslp_canonical_normal_form'],
        'The actual normalized logical eigenvectors are supported in full fibers 0 and q/m; sparse coefficients are included.'),
    'eq:a-canonical': (['QECC.CodeProjector.HasRankTwoCanonicalNormalization',
        'QECC.CodeProjector.rankTwo_sslp_canonical_normal_form'],
        'The same normalized gate has sorted canonical ZMod values and literal gcd one, after the permitted physical transports.'),
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
        raise ValueError('Missing reviewed statement')
    if args.apply:
        path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        (ROOT / 'artifacts/orbit-certification-20261003/normal-form-correspondence-review.json').write_text(
            json.dumps({'schema': 1, 'sources': SOURCES, 'claims': decisions}, ensure_ascii=False, indent=2) + '\n',
            encoding='utf8')
    print('Reviewed current-source normal-form claims:', len(decisions))


if __name__ == '__main__':
    main()
