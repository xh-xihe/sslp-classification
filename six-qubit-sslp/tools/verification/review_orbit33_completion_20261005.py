"""Review the literal six-block derivation against exported current Lean types.

Compilation, axiom acceptance and source correspondence are separate gates.
This scoped review never marks the remaining manuscript obligations complete.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
import paper_release

B='MainTheory.Orbit33PrintedBlocks.'
S='MainTheory.Orbit33ScalarReflection.'
F='MainTheory.Orbit33PhysicalReflection.'
N='MainTheory.Orbit33NormalizedPairs.'
P='MainTheory.Orbit33ProjectorArgument.'
GROUPS=[
    (['displaymath@10239','displaymath@10246','displaymath@10252','displaymath@10258'],
     [B+'tail',B+'actual_words',B+'actual_fibers',B+'CBlock',B+'DBlock'],
     'The actual block words and their complements are checked against the '
     'native fibers. The zero-angle site is the first physical coordinate; '
     'top blocks retain that coordinate and reverse the native tail order.'),
    (['eq:o33blocknorms'],[B+'R',B+'physical_norms_and_reflection',B+'physical_blocks_nonzero'],
     'All six bottom and six top squared norms are derived from actual '
     'normalized diagonal moments, including every boundary. Every R_i '
     'is strictly positive, so all twelve block vectors are nonzero.'),
    (['displaymath@10276','eq:o33reflection'],[B+'actual_characters',S+'C_cast',S+'inverse',
      S+'reflection_entries','MainTheory.Orbit33PrintedReflection.determinant'],
     'The literal character matrix is checked against the actual five-bit '
     'tails. Its signed determinant is 160. The inverse and reflection '
     'are proved over both the rational and complex coefficient fields.'),
    (['displaymath@10291','displaymath@10295'],[B+'evaluation',B+'evaluation_formula',
      F+'physical_scalar_reflection',F+'physical_character_reflection'],
     'The quadratic form is exactly c_i dagger F c_i, for arbitrary '
     'complex two-by-two F. Actual physical KL and moments imply the '
     'complete f=C^{-1}JCg identity in the printed tail coordinates.'),
    (['displaymath@10306','eq:o33matrixreflection'],[B+'rho',B+'matrix_reflection_iff',
      B+'physical_norms_and_reflection',F+'physical_common_reduced_state'],
     'The two actual reduced matrices agree. All four entries of all '
     'six outer-product identities are proved. Equality of matrices '
     'is equivalent to equality of pairings with all complex F.'),
    (['eq:o33rankonepairs'],[B+'rankone_rows_iff_1',B+'rankone_rows_iff_2',B+'physical_rankone_pairs'],
     'For each of the two literal reciprocal pairs, the four raw cross '
     'rows are equivalent in both directions to the zero rank-one matrix '
     'sum. Every physical Pauli used has weight at most two.'),
    (['displaymath@10332'],[N+'factorization',N+'normalized_pairs',N+'physical_normalized_pairs'],
     'The two matrix pairs and the positive actual norms give common '
     'unit vectors and all six nonzero scalar factors. Normalization '
     'uses the positive square root with its nonzero denominator proved.'),
    (['displaymath@10339','eq:o33gammasigns'],[N+'gamma',N+'quotient_sign',N+'physical_normalized_pairs'],
     'The phase quotient is beta_i/conjugate(alpha_i). All denominators '
     'and the baseline quotient are proved nonzero, and both printed '
     'sign relations follow from the actual rank-one equations.'),
    (['displaymath@10349','eq:o33crosscomplete'],[B+'near',B+'far',B+'crossFlip',
      B+'cross_weight',B+'cross_incidence',B+'physical_complete_cross'],
     'All nine near/far reciprocal pairs are checked on the actual '
     'physical fibers. Each flip has weight two and exactly its four '
     'qubit-resolved incidences. Every displayed scalar cross equation '
     'is derived from actual distance three.'),
    (['displaymath@10361','displaymath@10367'],[N+'inner',N+'divided_cross',
      B+'physical_complete_cross',N+'physical_normalized_pairs'],
     'The two inner products are A_j=c_j dagger v and B_j=u dagger d_j. '
     'Substitution of the actual nonzero factors and division by '
     'conjugate(alpha_i) gives gamma_i A_j+B_j=0 for i=0 and i=1.'),
    (['displaymath@10373','eq:o33orthogonalblocks'],[N+'orthogonal_from_opposite',
      N+'physical_far_orthogonal',N+'physical_frame'],
     'The nonzero opposite quotients force both inner products to '
     'vanish in every far block, yielding both stated orthogonality '
     'relations independently of the final no-code conclusion.'),
    (['displaymath@10387','displaymath@10391'],[P+'scaled_outer',P+'orthogonal_outer',
      P+'physical_near_and_far_sums'],
     'The unit-vector outer products and the two-dimensional orthogonal '
     'complements give the two literal projector sums. The strictly '
     'positive R_0 and R_3 are canceled explicitly.'),
    (['displaymath@10398'],[P+'physical_all_bottom_outers',P+'physical_rho_projector',
      P+'physical_projector_sums',P+'physical_unit_orthogonality',P+'rank_one_not_half',P+'physical_no_go'],
     'The two projector sums imply I/2 and perpendicular unit vectors. '
     'All six actual bottom outer products equal R_i P_u, so their '
     'sum is P_u. Its determinant zero contradicts that of I/2.'),
]
PROSE=[
    (10265,10272,[B+'physical_norms_and_reflection',B+'physical_blocks_nonzero'],
     'All twelve positive block norms and nonzero vectors are proved in physical coordinates.'),
    (10274,10316,[B+'actual_characters',B+'evaluation_formula',B+'matrix_reflection_iff',
      F+'physical_character_reflection',F+'physical_common_reduced_state',B+'physical_norms_and_reflection'],
     'The actual character matrix, arbitrary-F quadratic forms, common reduced state and full six-block matrix reflection are checked.'),
    (10318,10346,[B+'rankone_rows_iff_1',B+'rankone_rows_iff_2',B+'physical_rankone_pairs',N+'physical_normalized_pairs'],
     'Both directions of the literal matrix-pair reduction, unit-vector factorization, nonzero factors and phase signs are proved.'),
    (10348,10383,[B+'cross_incidence',B+'cross_weight',B+'physical_complete_cross',
      N+'divided_cross',N+'physical_far_orthogonal'],
     'All nine actual reciprocal pairs and both far-block orthogonality relations are derived from physical cross KL.'),
    (10385,10403,[P+'physical_near_and_far_sums',P+'physical_projector_sums',
      P+'physical_unit_orthogonality',P+'physical_all_bottom_outers',P+'physical_rho_projector',P+'physical_no_go'],
     'The two projector sums, half-identity reduced state, perpendicular unit vectors, rank-one reduced state and final contradiction are separately exposed.'),
]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    evidence=ROOT/'artifacts/manuscript-certification-20261005/kernel-types-orbit31-completion.json'
    types=json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Changed current source/type binding')
    required={n for row in GROUPS for n in row[1]}|{n for row in PROSE for n in row[2]}
    missing=required-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected roots: '+str(sorted(missing)))
    apply_reviews('supplementary',GROUPS,'orbit33-completion-review',args.apply,
        expected_sources=SOURCES,review_prefix='20261005 literal six-block/current type review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    path=ROOT/'results/prose-review-20261003.json'
    record=json.loads(path.read_text(encoding='utf8'))
    paper_release.validate_review(record,'20261003',ROOT)
    lines=(ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
    rows=[{'source':'supplementary.tex','line':lo,'end_line':hi,'kind':'covered',
        'reason':reason,'declarations':names,'origin':'20261005 literal six-block current type review',
        'context_sha256_lf':hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
        for lo,hi,names,reason in PROSE]
    keys={(r['source'],r['line'],r['end_line']) for r in rows}
    record['assertions']=[r for r in record['assertions']
        if (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]+rows
    record['status']='partial'
    paper_release.validate_review(record,'20261003',ROOT)
    if args.apply:
        path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        (evidence.parent/'orbit33-completion-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'prose_blocks':rows,'scope':'Scoped current six-block correspondence; other manuscript review remains incomplete'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Current explicit prose blocks:',len(record['assertions']),'status:',record['status'])

if __name__=='__main__':
    main()
