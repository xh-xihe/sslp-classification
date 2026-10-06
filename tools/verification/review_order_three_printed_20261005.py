"""Bind the current order-three normal forms and literal cross reductions."""
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

M='MainTheory.OrderThreePrintedMoments.'
C='MainTheory.OrderThreePrintedCrossRows.'
R='MainTheory.OrderThreePrintedRanks.'
W49='MainTheory.Orbit49PrintedRows.'
A49='MainTheory.Orbit49PrintedAlgebra.'
P49='MainTheory.Orbit49PhysicalCompletion.'
W50='MainTheory.Orbit50PrintedRows.'
P50='MainTheory.Orbit50PhysicalTriangle.'
W51='MainTheory.Orbit51PrintedRows.'
A51='MainTheory.Orbit51PrintedAlgebra.'
P51='MainTheory.Orbit51PhysicalCompletion.'
GROUPS=[]
MOMENTS={47:['eq:o47-p','eq:o47-domain'],48:['eq:o48-p','eq:o48-domain'],
         49:['eq:o49-S0','eq:o49-moments','eq:o49-domain','eq:o49-pairsums'],
         50:['eq:o50-S0','eq:o50-moments','eq:o50-domain','eq:o50-keymasses'],
         51:['eq:o51-S0','eq:o51-moments','eq:o51-domain'],
         52:['eq:o52-p','eq:o52-domain']}
for orbit,labels in MOMENTS.items():
    names=[M+f'Orbit{orbit}.'+name for name in
           ('bottom','top','bottomProb','topProb','Domain','actual_words',
            'normal_coordinates','domain_of_moment','reconstruct','complete_iff','physical_normal_form')]
    if orbit in (49,50,51):names += [M+f'Orbit{orbit}.actual_complements',M+f'Orbit{orbit}.complementIndex']
    if orbit in (49,50):names += [M+f'Orbit{orbit}.key_masses']
    GROUPS.append((labels,names,
      f'The literal orbit-{orbit} probability vectors and exact nonnegativity '
      'domain are equivalent in both directions to the complete real native '
      'moment system. Actual words and physical normalized-code probabilities '
      'are also checked. All zero-amplitude boundaries are retained. '
      +('The native orbit-50 top order is reversed relative to complementary '
        'bottom indexing, and the explicit complementIndex records this map. ' if orbit==50 else '')
      +'These statements certify the normal forms and their displayed mass '
      'consequences; separate matrix-rank and minor prose is not inferred.'))
    GROUPS[-1][1].extend(R+f'Orbit{orbit}.'+name for name in
        ('matrixZ','actualMatrix','actual_matrix','rows','columns','minorQ','determinant',
         'matrixR','minorR','real_determinant','rank_factorization','real_rank_factorization',
         'rank_exact','kernel_dimension'))
GROUPS += [
    (['eq:o50-baseedge','eq:o50-zero-k-table','eq:o50-k10-table',
      'eq:o50-k10-edge','eq:o50-six-rref'],
     [W50+f'Row{r:02d}.'+name for r in range(7) for name in
      ('flip','printedSources','printedDestinations','sources','destinations',
       'characters','rowSign','literal_indexing','actual_incidence','actual_images',
       'actual_characters','weights','printed_entry','row_reduction','physical_rows','physical_reciprocal')]
      +[P50+'complementary_index',P50+'physical_reciprocals'],
     'All seven literal two- and six-incidence tables are checked in complementary '
     'top indexing. The explicit native reversal and the harmless global minus '
     'sign on the six-incidence Z4 row are recorded. Both directions of the '
     'complete row reductions and their actual physical reciprocal equations '
     'are proved, including the four middle incidences.'),
    (['eq:o50-zero-k-phase','eq:o50-k10-phase','eq:o50-triangle'],
     [P50+'rho',P50+'physical_masses',P50+'physical_norm_matching',P50+'physical_active',
      P50+'physical_reciprocals',P50+'physical_triangle',P50+'physical_no_go',
      'MainTheory.PhysicalPhaseQuotients.opposition','MainTheory.PhysicalPhaseQuotients.unit',
      A49+'triangleC',A49+'triangle_equations',A49+'triangle_determinant'],
     'The actual moment masses guarantee only one active index among 1,2,5. '
     'For each such index the three physical reciprocal equations give the '
     'printed unit-modulus phase triangle and its literal final contradiction, '
     'with every zero-amplitude boundary retained.'),
    (['eq:o51-X3-incidences','eq:o51-X3matrix','eq:o51-X3kernel','eq:o51-X6kernel'],
     [W51+f'Row{r:02d}.'+name for r in range(2) for name in
      ('flip','sources','destinations','characters','W','WC','actual_incidence',
       'actual_images','actual_characters','weights','matrix_checked','row_reduction',
       'kernel_span','physical_rows','physical_relations')]+[P51+'physical_kernel_rows'],
     'The literal X3 and X6 incidence orders and all three actual Pauli rows '
     'are checked. Both directions of each printed one-dimensional kernel '
     'and all reciprocal equalities in its coordinates are proved.'),
    (['eq:o51-pin1','eq:o51-linear-pin','eq:o51-betagamma',
      'eq:o51-fixedprobabilities','eq:o51-boundarymass'],
     [A51+'kernel_norm_equalities',A51+'printed_pin_identities',A51+'linear_pin',
      A51+'pin_parameters',A51+'fixedIndices',A51+'fixedProbability',A51+'pinned_point',
      A51+'fixed_nonzero',A51+'boundary_active',P51+'physical_moment',
      P51+'physical_kernel_rows',P51+'physical_pinned_point'],
     'The physical kernel rows give the two exact norm-product identities. '
     'The complete moment normal form yields the literal beta/gamma pinning '
     'and linear equations. All six fixed probabilities, their nonzero '
     'amplitudes and the 6/7 boundary mass are checked.'),
    (['eq:o51-partialsync','eq:o51-sync1','eq:o51-rho89','eq:o51-fullsync'],
     [W51+f'Row{r:02d}.'+name for r in (2,3) for name in
      ('flip','sources','destinations','characters','actual_incidence','actual_images',
       'actual_characters','weights','row_reduction','physical_relations')]
       +[A51+'rho',A51+'partial_sync',A51+'boundary_active',A51+'anchor_sync',
         A51+'full_sync',P51+'physical_sync_rows',P51+'physical_full_sync'],
     'Both complete actual four-incidence synchronization systems are checked. '
     'At least one of indices 6,7 is active, so anchor synchronization and all '
     'six printed equal phase quotients hold at both alpha boundary endpoints.'),
    (['eq:o51-two-polys','eq:o51-thirdpoly','eq:o51-ratios','eq:o51-triangle-equations'],
     [W51+'Row04.actual_incidence',W51+'Row04.actual_images',W51+'Row04.weights',
      W51+'Row04.row_reduction',W51+'Row04.physical_relations',
      P51+'physical_four_row',P51+'quadrics_of_sync',P51+'physical_quadrics',
      P51+'physical_ratios',P51+'physical_no_go',A51+'fixed_nonzero',
      A49+'ratio_triangle',A49+'triangle_determinant'],
     'The synchronized physical amplitude identities and the complete actual '
     'rank-one row give all three literal quadrics. Every ratio denominator '
     'is nonzero by the fixed probabilities. The printed three ratio equations '
     'give the final contradiction without invoking the earlier no-code theorem.'),
    (['eq:o49-synchronization-table','eq:o49-example-rref'],
     [W49+f'Row{r:02d}.'+name for r in range(8) for name in
      ('flip','sources','destinations','characters','actual_incidence','actual_images',
       'actual_characters','weights','matrix_checked','row_reduction','physical_relations')]
       +[A49+'reciprocal_rows'],
     'All eight literal flip masks, every endpoint and all four physical Pauli '
     'dressings are checked. Each complete matrix system is equivalent in '
     'both directions to the two printed reciprocal equations. The odd '
     'masks use the required opposite incidence pairing.'),
    (['eq:o49-rho89','eq:o49-uniformphase'],
     [A49+'rho',A49+'reciprocal_rows',A49+'reconstruct_from_anchor',
      A49+'uniform_phase',P49+'physical_uniform_phase'],
     'Actual moment masses make both anchors nonzero and guarantee an active '
     'index among zero and one. The actual reciprocal rows identify both '
     'anchor quotients and give the uniform amplitude identity at every '
     'index zero through seven, including every zero-amplitude boundary.'),
    (['eq:o49-rankone-table','eq:o49-poly1'],
     [W49+f'Row{r:02d}.'+name for r in range(8,12) for name in
      ('flip','sources','destinations','characters','actual_incidence','actual_images',
       'weights','row_reduction','physical_relations')]
      +[A49+'poly_from_four_reciprocals',P49+'fourRows',P49+'quadrics',
        P49+'four_polynomials',P49+'physical_four_rows',P49+'physical_quadrics'],
     'The four actual rank-one tables are checked with every Pauli dressing. '
     'Nonzero-anchor cancellation of their exact reciprocal consequences '
     'proves all four literal bottom-amplitude quadrics without division by '
     'a possibly zero bottom amplitude.'),
    (['eq:o49-pin1','eq:o49-pin2','eq:o49-pinnedpoint'],
     [A49+'norm_product',A49+'pin_parameters',A49+'pinned_point',
      P49+'physical_quadrics',P49+'physical_moment',P49+'physical_pinned_point',
      M+'Orbit49.normal_coordinates'],
     'Norm squares of the actual quadrics give the three product equalities. '
     'The literal normal form yields the two printed parameter pinning '
     'identities and pins alpha=beta=gamma=1/12. All twenty actual bottom '
     'and top probabilities are proved, including both anchor masses 1/6.'),
    (['eq:o49-ratios','eq:o49-triangle'],
     [A49+'triangle',A49+'triangleC',A49+'triangle_determinant',A49+'triangle_equations',
      A49+'ratio_triangle',P49+'physical_pinned_point',P49+'physical_no_go'],
     'The three literal amplitude ratios have nonzero denominators and '
     'numerators by the pinned physical probabilities. The three quadrics '
     'give the exact printed matrix equation; its signed determinant is -2. '
     'The final physical contradiction is composed through these steps '
     'without invoking the previous orbit-49 no-code theorem.'),
    (['eq:m3-complementfibers','eq:m3-complementstates'],
     [M+f'Orbit{o}.actual_complements' for o in (49,50,51)]+
     [M+f'Orbit{o}.actual_words' for o in (49,50,51)]+
     ['MainTheory.SupportKetExpansion.expansion','MainTheory.SupportKetExpansion.indexed_expansion'],
     'The three actual fiber pairs are complementary, with an explicit top-index permutation where necessary. The generic support-basis expansion applies to each actual supported complex state.'),
    (['eq:o50-record'],['SixQubit.Orbit50.av','SixQubit.Orbit50.S0_eq_fiber','SixQubit.Orbit50.S1_eq_fiber'],
     'The actual modulus-six angle vector and residue-zero/two fibers are checked in native coordinates.'),
    (['eq:o51-record'],['SixQubit.Orbit51.av','SixQubit.Orbit51.S0_eq_fiber','SixQubit.Orbit51.S1_eq_fiber'],
     'The actual modulus-six angle vector and residue-zero/two fibers are checked in native coordinates.'),
]
for orbit,labels in {
 47:['eq:o47-X5-incidences','eq:o47-AB','eq:o47-Walsh','eq:o47-contradiction'],
 48:['eq:o48-X4-incidences','eq:o48-ABCD','eq:o48-Hadamard'],
 52:['eq:o52-X2-incidences','eq:o52-ABCD','eq:o52-Hadamard','eq:o52-halfrelations','eq:o52-squared'],
}.items():
    names=[C+f'Orbit{orbit}.'+name for name in ('flip','sources','destinations','characters',
      'actual_incidence','actual_images','actual_characters','weights','matrix_checked','determinant',
      'product_expansion','product_norm','physical_rows','physical_products_zero','physical_no_go')]
    names += [C+f'Orbit{orbit}.physical_first_product_positive'] if orbit!=52 else [
        C+'Orbit52.physical_half_relations',C+'Orbit52.physical_squared_products']
    GROUPS.append((labels,names,
      f'The SI-specified physical flip in orbit {orbit}, every incidence '
      'endpoint and every dressing character are kernel checked. Actual KL '
      'gives the printed matrix equations, whose nonsingular determinant '
      'annihilates every product. Exact physical probability products give '
      +('the positive first product 1/18. ' if orbit!=52 else
        'both half-probability square identities and their nonzero total 1/3, even when either endpoint amplitude is zero. ')
      +'The final contradiction is composed through these literal steps, '
      'independently of the previous orbit no-code proof.'))
PROSE=[
    (13927,13994,[P50+'physical_active',P50+'physical_reciprocals',P50+'physical_triangle',
                  P50+'physical_no_go',W50+'Row04.actual_characters',W50+'Row04.rowSign'],
     'The literal orbit-50 incidence and reciprocal route is checked, including '
     'the native top reversal and global Z4 row sign; one active index suffices '
     'for the unit-modulus odd triangle.'),
    (14050,14104,[W51+'Row00.kernel_span',W51+'Row01.kernel_span',A51+'printed_pin_identities',
                  A51+'linear_pin',A51+'pin_parameters',P51+'physical_pinned_point'],
     'Both actual printed kernels and the exact norm-product parameter pinning '
     'give all six fixed positive probabilities.'),
    (14106,14147,[A51+'partial_sync',A51+'boundary_active',A51+'anchor_sync',A51+'full_sync',
                  P51+'physical_sync_rows',P51+'physical_full_sync'],
     'The two actual synchronization systems identify both anchors even when '
     'alpha is at either boundary endpoint.'),
    (14149,14184,[P51+'quadrics_of_sync',P51+'physical_quadrics',P51+'physical_ratios',
                  A51+'fixed_nonzero',P51+'physical_no_go'],
     'All three physical quadrics, the explicitly nonzero ratio denominators '
     'and the literal odd-triangle contradiction are proved.'),
    (13750,13806,[A49+'reciprocal_rows',P49+'physical_uniform_phase',
                 P49+'physical_four_rows',P49+'physical_quadrics'],
     'The literal twelve mask reductions, common anchor phase and four '
     'quadrics are physically derived, including the whole closed boundary.'),
    (13821,13864,[A49+'norm_product',A49+'pin_parameters',P49+'physical_pinned_point',
                 A49+'triangle_equations',A49+'triangle_determinant',P49+'physical_no_go'],
     'Both parameter pinning identities, all physical pinned probabilities '
     'and the exact nonzero-ratio triangle and final contradiction are proved.'),
    (13506,13524,[M+'Orbit47.complete_iff',M+'Orbit47.physical_normal_form'],
     'The complete real two-parameter probability family and its exact domain are proved in both directions.'),
    (13587,13611,[M+'Orbit48.complete_iff',M+'Orbit48.physical_normal_form'],
     'The complete real two-parameter probability family and nonnegative domain are proved; rank/minor prose is reviewed separately.'),
    (13719,13737,[M+'Orbit49.complete_iff',M+'Orbit49.physical_normal_form'],
     'The complete real three-parameter probability family and all facets of its exact domain are proved.'),
    (13892,13918,[M+'Orbit50.complete_iff',M+'Orbit50.physical_normal_form',M+'Orbit50.actual_complements'],
     'The complete real four-parameter probability family and its exact nonnegative domain are proved, including the top-order reversal.'),
    (14029,14045,[M+'Orbit51.complete_iff',M+'Orbit51.physical_normal_form'],
     'The complete real three-parameter moment cube, with every boundary, is proved in both directions.'),
    (14215,14239,[M+'Orbit52.complete_iff',M+'Orbit52.physical_normal_form'],
     'The complete real two-parameter probability rectangle and its exact nonnegative domain are proved.'),
    (13530,13559,[C+'Orbit47.actual_incidence',C+'Orbit47.physical_rows',C+'Orbit47.physical_products_zero',C+'Orbit47.physical_first_product_positive',C+'Orbit47.physical_no_go'],
     'The actual X5 and X5Z1 rows, their individual zero products and the positive probability product 1/18 give the literal exclusion.'),
    (13616,13651,[C+'Orbit48.actual_incidence',C+'Orbit48.physical_rows',C+'Orbit48.determinant',C+'Orbit48.physical_products_zero',C+'Orbit48.physical_first_product_positive',C+'Orbit48.physical_no_go'],
     'The actual X4 four-incidence Hadamard system and positive first product give the literal exclusion.'),
    (14243,14298,[C+'Orbit52.actual_incidence',C+'Orbit52.physical_rows',C+'Orbit52.physical_half_relations',C+'Orbit52.physical_squared_products',C+'Orbit52.physical_no_go'],
     'The actual X2 Hadamard system, two half-probability identities and positive total give a boundary-inclusive literal exclusion.'),
]
for orbit,lo,hi in [(47,13525,13527),(48,13613,13614),(49,13739,13741),
                    (50,13920,13921),(51,14047,14048),(52,14241,14242)]:
    PROSE.append((lo,hi,[R+f'Orbit{orbit}.'+name for name in
        ('actual_matrix','rows','columns','determinant','real_determinant','rank_exact',
         'kernel_dimension')]+[M+f'Orbit{orbit}.complete_iff'],
        f'The actual orbit-{orbit} 23-row occupation matrix has the printed exact rank '
        'and an explicitly selected maximal minor with the printed signed determinant. '
        'Kernel-checked rectangular factors give the rank upper bound; the real nonzero '
        'minor gives the lower bound, independently of any phase exclusion.'))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    evidence=ROOT/'artifacts/manuscript-certification-20261005/kernel-types-orbit31-completion.json'
    types=json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256']!=SOURCES:raise ValueError('Changed current manuscript/type binding')
    required={n for row in GROUPS for n in row[1]}|{n for row in PROSE for n in row[2]}
    missing=required-{r['name'] for r in types['declarations']}
    if missing:raise ValueError('Uninspected roots: '+str(sorted(missing)))
    apply_reviews('supplementary',GROUPS,'order-three-printed-review',args.apply,
        expected_sources=SOURCES,review_prefix='20261005 literal real normal-form/physical row review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    path=ROOT/'results/prose-review-20261003.json'
    record=json.loads(path.read_text(encoding='utf8'))
    paper_release.validate_review(record,'20261003',ROOT)
    lines=(ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
    rows=[{'source':'supplementary.tex','line':lo,'end_line':hi,'kind':'covered',
           'reason':reason,'declarations':names,'origin':'20261005 real normal-form and physical type review',
           'context_sha256_lf':hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
          for lo,hi,names,reason in PROSE]
    keys={(r['source'],r['line'],r['end_line']) for r in rows}
    record['assertions']=[r for r in record['assertions'] if
        (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]+rows
    record['status']='partial'
    paper_release.validate_review(record,'20261003',ROOT)
    if args.apply:
        path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        (evidence.parent/'order-three-printed-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'prose_blocks':rows,'scope':'Scoped current probability/row correspondence; other manuscript review remains incomplete'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Explicit prose blocks:',len(record['assertions']),'status:',record['status'])

if __name__=='__main__':main()
