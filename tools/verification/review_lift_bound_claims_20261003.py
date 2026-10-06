#!/usr/bin/env python3
"""Explicit review of the current Smith and general physical-order proof steps."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
from review_core_claims_20261003 import SOURCES

GROUPS = [
    (['eq:snf', 'lem:denominator-clearing', 'eq:clear-denom', 'displaymath@1596', 'eq:beta'],
     ['MainTheory.SharpClearing.SmithWitness', 'MainTheory.SmithExistence.exists_smith_normal_form',
      'MainTheory.SharpClearing.inverse_eq_smithInverseCandidate',
      'MainTheory.PivotSmithNormalForm.clearing_smithLastFactor',
      'MainTheory.QECCSmithBridge.finalSmithInvariant_eq_lastFactor',
      'MainTheory.QECCSmithBridge.smithBeta_eq_betaOf', 'MainTheory.BetaExists.betaOf'],
     'Read the current Smith decomposition, its inverse formula, the final-factor integral clearing and the maximum over all sizes up to nu. The explicit Smith witness has integral unimodular changes of basis and a positive divisibility chain. The cokernel-exponent/final-factor bridge and the beta equality identify the two existing library definitions with the same displayed quantities.'),
    (['thm:colored-finite-lift', 'displaymath@1620', 'eq:general-q-bound',
      'eq:q-divides-smith', 'eq:qmin-general'],
     ['MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects',
      'MainTheory.BinaryPivotLift.rationalLift_order_dvd_smithLastFactor',
      'MainTheory.QECCSmithBridge.finalSmithInvariant_eq_lastFactor',
      'QECC.CodeProjector.general_physicalOrder_bound',
      'QECC.CodeProjector.GeneralPhysicalOrderBoundConclusion',
      'QECC.CodeProjector.minimalPhysicalOrder_le'],
     'The current bound uses the number ell of the source logical sectors, under single-Z detection in the same basis. The actual-support lifted binary system has n+ell-1 variables and gives the same logical class a reduced finite representative with m dividing q and q dividing its final Smith factor. This bounds the defined minimum over reduced diagonal representatives. The separately archived proof sentence about all physical representatives is not included in this formula review.'),
    (['displaymath@1656', 'eq:X-conjugation', 'eq:normalized-first-sector'],
     ['QECC.xorEquiv', 'QECC.reindexOperator_xor_diagonalGate',
      'MainTheory.RealXNormalization.gate_shift',
      'MainTheory.NormalizedRealSectors.zero_mem_shifted_support',
      'MainTheory.NormalizedRealSectors.shifted_reference_phase_zero'],
     'Actual local-X conjugation relabels x by x xor the chosen support anchor and changes physical angles by its coordinate signs, with the displayed common scalar. The normalized first support contains zero, so its real logical phase can be chosen zero.'),
    (['eq:first-sector-eq', 'displaymath@1688', 'eq:Ru=h', 'displaymath@1703'],
     ['MainTheory.FiniteLift.realUnknown', 'MainTheory.FiniteLift.phaseInteger_spec',
      'MainTheory.FiniteLift.coloredMatrix_realSolution',
      'MainTheory.NormalizedPhaseEquations.same_integer_phase_equations',
      'MainTheory.BinaryPivot.isZeroOne_binaryColoredMatrixZ',
      'MainTheory.PivotSize.card_color', 'MainTheory.PivotSize.rank_le',
      'MainTheory.ColoredBound.rank_pos'],
     'The current unknown vector consists of n physical angles and the negative phases of every non-anchor sector. The actual congruences lift to integer right-hand sides and a binary matrix of width n+ell-1; a non-anchor nonempty sector supplies an auxiliary one and makes rank positive. This reviews the real/rational matrix rank, not rank over F2.'),
    (['displaymath@1710', 'eq:pivot-solve', 'displaymath@1724', 'displaymath@1729', 'displaymath@1735'],
     ['MainTheory.PivotSize.exists_pivotData', 'MainTheory.FiniteLift.PivotData.rhs_spans',
      'MainTheory.FiniteLift.PivotData.selectedRow_solves',
      'MainTheory.FiniteLift.PivotData.fullSolution_solves',
      'MainTheory.BinaryPivot.binMatrix_isZeroOne', 'MainTheory.BinaryPivot.binMatrix_det_ne_zero',
      'QECC.exists_binaryPivotSolution', 'QECC.BinaryPivotSolution.solution_apply_of_not_mem_range'],
     'The selected independent rows and coordinate columns give a nonsingular square binary minor. Its inverse solves the selected integral right-hand side, with all other coordinates zero. Consistency of the original full system gives the same linear combination for each omitted right-hand-side entry; the reconstructed rational vector therefore solves every original row.'),
    (['displaymath@1744', 'displaymath@1748'],
     ['MainTheory.PivotSmithNormalForm.clearing_smithLastFactor',
      'MainTheory.ColoredSmithDisplays.fullSolution_smith_integral',
      'QECC.BinaryPivotSolution.exists_integral_finalSmithInvariant_smul_selectedSolution',
      'QECC.BinaryPivotSolution.exists_integral_finalSmithInvariant_smul_solution',
      'MainTheory.QECCSmithBridge.finalSmithInvariant_eq_lastFactor'],
     'The same selected binary matrix supplies the final Smith multiplier. It clears the selected solution and hence the full sparse reconstructed vector, because all unselected coordinates vanish.'),
    (['displaymath@1758', 'displaymath@1762'],
     ['MainTheory.NormalizedPhaseEquations.same_integer_phase_equations',
      'QECC.CodeProjector.supportWeight_sub_eq_sectorPhase_sub_of_solvesActualSectorEquations',
      'QECC.CodeProjector.SectorPhasePivot.difference_constant_on_actualSector',
      'MainTheory.CommonMeanReplacement.support_value'],
     'Subtracting the two actual lifted systems gives the sector-dependent phase difference on its support. Subtraction within one sector cancels that phase difference, so the physical difference vanishes on all within-sector point differences. The common-mean theorem then makes the value common to every sector.'),
    (['displaymath@1786', 'displaymath@1791', 'displaymath@1798'],
     ['MainTheory.Denominator.lcmDen_dvd_of_clears', 'MainTheory.Denominator.lcmDen_clears',
      'MainTheory.Denominator.eq_one_of_dvd_lcmDen_of_dvd_liftNum',
      'QECC.rationalVectorPhase_eq_rationalPhase_of_smul_eq',
      'QECC.ReducedDiagonalRepresentative.addOrderOf_phase',
      'QECC.ReducedDiagonalRepresentative.commonGCD_eq_one'],
     'The least common denominator divides every integral clearing multiplier, including this final Smith factor. Reducing its literal integral numerators modulo that denominator leaves the physical phases unchanged, gives exact physical order, and forces gcd one; a greater common divisor would contradict the least denominator.'),
    (['displaymath@1818'],
     ['MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects',
      'MainTheory.BetaAtPivotRank.betaOf_mono',
      'QECC.CodeProjector.GeneralPhysicalOrderBoundConclusion'],
     'The displayed inequality chain follows from positive final Smith factor, denominator divisibility, the positive pivot size at most n+ell-1 and ell at most K. The author-held following prose sentence about the minimization domain is excluded from this display review.'),
    (['eq:small-beta', 'eq:K2-q-bound-summary'],
     ['MainTheory.Generated.BinaryBetaFiveFast.Certificate.betaExact',
      'MainTheory.Generated.BinaryBetaSixKernel.Certificate.betaExact',
      'MainTheory.BinaryBetaSeven.betaSevenExact', 'MainTheory.BinaryBetaEight.betaEightExact',
      'MainTheory.BinaryBetaNine.betaNineExact', 'MainTheory.QECCSmithBridge.smithBeta_eq_betaOf',
      'MainTheory.QuantitativeGroup.k2_q_bound'],
     'The five current small beta values are actual exhaustive kernel-certified maxima, not values read from a table without proof. At rank two there are two sectors, giving the same-action physical representative bound beta_(n+1), and hence the stated six-qubit preliminary cutoff eighteen.'),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    reviews = {}
    for ids, declarations, review in GROUPS:
        for ident in ids:
            if ident in reviews:
                raise ValueError('Duplicate review: ' + ident)
            reviews[ident] = (declarations, review)
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
        declarations, review = reviews[suffix]
        entry.update(status='covered', lean_declarations=declarations,
                     review='20261003 current-source review (2026-10-04): ' + review)
        decisions.append({k: entry[k] for k in ('id', 'statement_sha256', 'status', 'lean_declarations', 'review')})
    if len(decisions) != len(reviews):
        raise ValueError('Missing reviewed lift-bound statement')
    if args.apply:
        path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        (ROOT / 'artifacts/orbit-certification-20261003/lift-bound-correspondence-review.json').write_text(
            json.dumps({'schema': 1, 'sources': SOURCES, 'claims': decisions}, ensure_ascii=False, indent=2) + '\n',
            encoding='utf8')
    print('Reviewed current-source lift-bound claims:', len(decisions))


if __name__ == '__main__':
    main()
