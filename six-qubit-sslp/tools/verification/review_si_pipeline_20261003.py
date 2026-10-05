#!/usr/bin/env python3
"""Explicit review of the current SI reduction chain and complete 66-row table."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
from review_core_claims_20261003 import SOURCES

GROUPS = [
    (['six:eq:qcutoff'], ['MainTheory.SSLPCompleteness.completeness_six_qubit',
     'MainTheory.Generated.BinaryBetaSixKernel.Certificate.betaExact'],
     'The source searches bounded representatives of nontrivial logical classes, not every physical representative. Completeness retains logical order dividing physical order and the literal cutoff nine.'),
    (['displaymath@100', 'six:eq:primitive', 'displaymath@111', 'six:eq:sorted'],
     ['MainTheory.Gate.diag', 'MainTheory.Gate.gate', 'MainTheory.GateGCD.primitive_iff_gcd',
      'SS.Sk', 'MainTheory.SortedForm.SortedNormalForm',
      'MainTheory.SSLPCompleteness.completeness_six_qubit'],
     'Read the tensor action, gcd-one exact physical order, full residue fibers, sorted residues and allowed zero amplitudes. The complete normalization is a theorem on the actual code.'),
    (['thm:six-66-orbits', 'equation@141', 'displaymath@145', 'displaymath@159', 'displaymath@790'],
     ['MainTheory.PaperReductionChain.six_66_orbits',
      'MainTheory.Generated.FiniteOrbitDistribution.orbit_order_distribution',
      'MainTheory.Generated.FinitePairProvenance.exact_image',
      'MainTheory.Generated.FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries'],
     'The eight stages retain their actual record/pair/key domains. HasExactlyClasses covers every input and excludes ghost keys. The counts and logical-order distribution refer to moment skeletons, not code equivalence classes.'),
    (['lem:six-raw-outer-count', 'displaymath@216', 'six:eq:starsbars',
      'six:eq:rawcount', 'six:eq:13877', 'six:eq:qequalsm', 'displaymath@281', 'remark@290'],
     ['MainTheory.PaperReductionChain.raw_outer_count',
      'MainTheory.OuterCountDisplays.multiplicities_sum',
      'MainTheory.SortedVectorMobius.sortedCount_six',
      'MainTheory.OuterCountDisplays.raw_records_divisor_formula',
      'MainTheory.OuterCountDisplays.raw_count_summands',
      'MainTheory.OuterCountDisplays.faithful_records_binomial_formula',
      'MainTheory.OuterCountDisplays.excess_raw_records'],
     'Reviewed stars-and-bars for arbitrary positive q, all eight summands, the divisor choices and both 13877/6434 counts. The raw list precedes all primal and symmetry tests.'),
    (['proposition@306', 'six:eq:primitiveMobius', 'six:eq:primitivevalues',
      'lem:six-primitivity-reduction', 'six:eq:primitiveTotal'],
     ['MainTheory.SortedVectorMobius.primitiveCount_eq_mobiusChoose',
      'MainTheory.SortedVectorMobius.primitiveCount_six_eq_mobiusCount',
      'MainTheory.SortedVectorMobius.primitiveAngles6_length_eq_primitiveCount',
      'MainTheory.PaperReductionChain.primitive_sorted_counts',
      'MainTheory.PaperReductionChain.primitivity_reduction'],
     'The Mobius formula is proved for all positive moduli, independently of the eight evaluated counts. Primitive enumerated vectors equal the mathematical gcd-one sorted-vector count, giving the 13449-record reduction.'),
    (['lem:six-nonempty-fiber-reduction', 'six:eq:nonemptyrecords',
      'lem:six-fiber-hashing', 'displaymath@382', 'six:eq:hashedpairs'],
     ['MainTheory.PaperReductionChain.nonempty_fiber_reduction',
      'MainTheory.PaperReductionChain.fiber_hashing',
      'MainTheory.Generated.FinitePairProvenance.exactRecord',
      'MainTheory.Generated.FinitePairProvenance.noGhostIndex',
      'MainTheory.Generated.FinitePairProvenance.pairAt_injective',
      'MainTheory.Generated.FinitePairProvenance.exact_image'],
     'Actual bit masks are computed from all 64 subset sums. The kernel checks each record payload, inverse witnesses and injectivity of distinct pair entries, so lossless hashing is not inferred from equal counts.'),
    (['lem:six-affine-smith-reduction', 'six:eq:mean', 'six:eq:covrange', 'six:eq:ractual',
      'six:eq:qbetar', 'six:eq:betasix', 'displaymath@464', 'six:eq:rmin',
      'six:eq:coarserank', 'six:eq:508'],
     ['MainTheory.CodeAffineSpanBridge.commonAffineSpan_of_exactCodeFrame',
      'MainTheory.CovarianceRange.range_cov_eq_span',
      'MainTheory.NormalizedSupportCovariance.covariance_range_dimension',
      'MainTheory.D3AffineRankBound.fresh_order_le_betaOf_source_affineRank',
      'MainTheory.SmallBetaValues.small_values', 'MainTheory.SmallBetaValues.rMin_spec',
      'MainTheory.SmallBetaValues.rMin_eq_minimum',
      'MainTheory.CoarseFilterUnconditional.fullFiberCriterion_of_s0_of_feasible',
      'MainTheory.PaperReductionChain.affine_smith_reduction',
      'MainTheory.StageRecordCounts.coarse_record_count'],
     'Strict positivity is on actual nonzero supports, not entire fibers. The common covariance range is the span of actual differences, and the controlled lift is bounded at that affine rank. Full-fiber rank is only a necessary prefilter. Checked beta values, four rMin sectors, 508 pairs and 510 representing records.'),
    (['lem:six-moment-lp-reduction', 'six:eq:phi', 'six:eq:lpnormal',
      'six:eq:convintersection', 'six:eq:Apb', 'six:eq:exactfeas', 'six:eq:separator',
      'six:eq:291', 'displaymath@592'],
     ['MainTheory.FiniteMomentMatrix.featureZ_eq_feature',
      'MainTheory.MomentPolytope.moment_row_counts',
      'MainTheory.MomentMatrix23.feasible_iff',
      'MainTheory.MomentMatrix23.exact_rational_iff_real',
      'MainTheory.MomentConvexHull.exists_feasible_iff_convexHull_inter',
      'MainTheory.ExactLP.exists_rational_feasible_of_real',
      'MainTheory.RealMomentSeparatorBridge.not_realFeasible_of_separator',
      'MainTheory.PaperReductionChain.moment_lp_reduction',
      'MainTheory.StageRecordCounts.feasible_record_count',
      'MainTheory.DuplicateOuterPair.records_distinct',
      'MainTheory.DuplicateOuterPair.same_full_fibers',
      'MainTheory.DuplicateOuterPair.both_primitive'],
     'The literal 21 features form the 23-row matrix on both full fibers. Rational feasibility is equivalent to real feasibility, and exact separators exclude real probabilities. Checked 291 pairs, 292 records and the stated q4,m2 duplicate, without relying on floating-point solver status.'),
    (['displaymath@613', 'lemma@621', 'six:eq:rstar', 'six:eq:rankcriterion',
      'six:eq:forcedzero', 'displaymath@663'],
     ['MainTheory.ActiveFace.avg_mem', 'MainTheory.ActiveFace.avg_pos',
      'MainTheory.ActiveFace.exists_attains_both_active_sets',
      'MainTheory.MomentPolytope.maximum_support_rank_and_threshold',
      'MainTheory.FiniteMomentSupportRank.rank_threshold_iff',
      'MainTheory.ExactLP.ForcedZeroCertificate',
      'MainTheory.ExactLP.coordinate_eq_zero_of_certificate',
      'MainTheory.ExactLP.rational_active_iff_real',
      'MainTheory.RealFaceBridge.realSupport_subset_face'],
     'A finite average attains both complete active supports simultaneously. Equal covariance gives equal active affine ranks and a maximum attainable rank, in both threshold directions. The forced-zero certificate has the exact negative-basis-vector inequality; rational/real active-coordinate equivalence and the direct real face theorem cover arbitrary real probabilities.'),
    (['lem:six-active-rank-reduction', 'six:eq:215', 'displaymath@685'],
     ['MainTheory.PaperReductionChain.active_rank_reduction',
      'MainTheory.ActiveRankRecordCount.compatible_record_count',
      'MainTheory.RankStageDistribution.table',
      'MainTheory.RankStageDistribution.eight_two_rank_four',
      'MainTheory.RankStageDistribution.nine_three_rank_five',
      'MainTheory.FiniteRankPipeline.RankRow.sound_of_valid'],
     'Checked 291-to-215 pairs, 216 records, all four displayed feasible/compatible counts and the universal ranks four/five in the rejected q8,m2/q9,m3 sectors. These are controlled-presentation exclusions, not a prohibition on order-two or order-three codes.'),
    (['six:eq:lpdim'], ['MainTheory.LPDimension.direction_eq_kernel_of_positive',
      'MainTheory.LPDimension.finrank_eq_card_sub_rank_of_positive',
      'MainTheory.FiniteMomentLP.affine_dimension_eq_of_face'],
     'The dimension is the relative real affine dimension after restriction to every active coordinate. Positivity removes no affine direction; rank-nullity gives active-cardinality minus restricted matrix rank.'),
    (['lem:six-orbit-reduction', 'displaymath@723', 'six:eq:cubegroup', 'six:eq:66'],
     ['MainTheory.CubeAction.six_cube_isometry_count',
      'MainTheory.CubeAction.allSixCubeIsometries_card',
      'MainTheory.CubeCompletionTransport.completion_of_fiberEquivalent',
      'MainTheory.PaperReductionChain.orbit_reduction',
      'MainTheory.Generated.FiniteOrbitDistribution.labeled_pair_order_distribution',
      'MainTheory.Generated.FiniteOrbitDistribution.orbit_order_distribution',
      'MainTheory.SurvivingLiftOrders.survivingQ_table'],
     'The 46080 count includes physical permutations and shifts; color interchange is separately included in the pair relation. Actual completion transport preserves full KL equations. Checked every logical-order count and surviving lift-order set.'),
    (['six:eq:allorders', 'remark@814'],
     ['MainTheory.Generated.FiniteOrbitDistribution.orbit_order_distribution',
      'MainTheory.IntrinsicOrderAudit.orderOf_mem',
      'MainTheory.ClassificationLevelsSix.level_four_lu_class'],
     'Every targeted order two through nine has a moment skeleton, while the later actual-code order theorem permits only 1,2,3,5. The text distinguishes moment skeletons, realizations and code classes; it does not equate the 66 or 15 with inequivalent code projectors.'),
    (['displaymath@929', 'tab:66orbits'],
     ['MainTheory.Generated.OrbitTableNumericData.all_rows',
      'MainTheory.Generated.OrbitTableNumericData.all_faces_valid',
      'MainTheory.Generated.OrbitTableNumeric.all_labeled_equivalences',
      'MainTheory.Generated.OrbitTableNumeric.all_real_statistics',
      'MainTheory.OrbitTablePaperKey.paperKey_bijective',
      'MainTheory.OrbitTablePaperKey.sum_paperMultiplicity',
      'MainTheory.RealizationOrbits15.realizationKeys_paperIds',
      'MainTheory.WImageSettled62.all_62_settled_WImages'],
     'Read all 66 printed rows and the status legend. The exact payload proves q,m,angles,full-fiber sizes,rStar,relative LP dimension and record multiplicity on the actual matched key. The map is bijective and multiplicities total 216. The current realization/order classification supersedes the old four-open-orbit image record and resolves orbit 2/3 to their actual full images.'),
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
        raise ValueError('The reviewed manuscript changed')
    decisions = []
    for entry in ledger['claims']:
        if not entry['id'].startswith('supplementary.tex:'):
            continue
        suffix = entry['id'].removeprefix('supplementary.tex:')
        if suffix not in reviews:
            continue
        declarations, review = reviews[suffix]
        entry.update(status='covered', lean_declarations=declarations,
                     review='20261003 current-source review (2026-10-04): ' + review)
        decisions.append({k: entry[k] for k in
                         ('id', 'statement_sha256', 'status', 'lean_declarations', 'review')})
    if len(decisions) != len(reviews):
        raise ValueError('Missing reviewed SI pipeline statement')
    if args.apply:
        path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        (ROOT / 'artifacts/orbit-certification-20261003/si-pipeline-correspondence-review.json').write_text(
            json.dumps({'schema': 1, 'sources': SOURCES, 'claims': decisions},
                       ensure_ascii=False, indent=2) + '\n', encoding='utf8')
    print('Reviewed current SI pipeline claims:', len(decisions))


if __name__ == '__main__':
    main()
