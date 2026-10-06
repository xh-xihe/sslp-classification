"""Bind the literal order-two scalar moment, shell and Walsh displays."""
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
S='MainTheory.OrderTwoShellProjectors.'
M='MainTheory.OrderTwoPrintedMoments.'
W='MainTheory.OrderTwoPrintedWalsh.'
R='MainTheory.OrderTwoPrintedRanks.'
GROUPS=[]
GROUPS.append((['eq:m2-halfangle-flip','eq:m2-halfangle-bijection'],
    ['MainTheory.HalfAngleFiberFlip.'+n for n in
     ('half_modulus','negative_half','weight_shift','flip_involutive','zero_to_half','fiber_bijection')],
    'For arbitrary physical dimension and even modulus q=2k, the actual modular '
    'weight changes by the half modulus under the selected coordinate flip. '
    'The same involutive flip gives the exact finite residue-fiber bijection.'))
for orbit,labels in {
18:['eq:o18-shellcoords','eq:o18-shelltypes','eq:o18-anchormasses','eq:o18-shellsystem','eq:o18-shellsolution'],
41:['eq:o41-shellcoords','eq:o41-shelltypes','eq:o41-shellsystem','eq:o41-shellchain','eq:o41-shellsolution'],
}.items():
    names=[S+f'Orbit{orbit}.'+n for n in ('bottom','top','coordinates','bottomTypes','topTypes',
      'actual_coordinates','shell_types','bottomMass','topMass','actual_shell_masses','Moment',
      'ShellSystem','shell_system','shell_solution','physical_moment','physical_shell_system')]
    if orbit==41:names.append(S+'Orbit41.shell_chain')
    GROUPS.append((labels,names,
      f'The actual orbit-{orbit} shell coordinates exhaust both fibers. Every '
      'literal shell mass equals the sum over its actual words. Rational combinations '
      'of the complete native physical diagonal moments give every printed shell '
      'equation and the unique literal shell solution.'))
for orbit,labels in {
18:['eq:o18-charactersum','eq:o18-anchorprojector','eq:o18-anchorzero'],
41:['eq:o41-anchorprojector','eq:o41-anchorzero'],
}.items():
    names=[S+f'Orbit{orbit}.'+n for n in ('point_projector','flip','characters','W','coefficients',
      'actual_incidence','actual_images','actual_characters','weights','matrix_checked','projector_checked',
      'complex_projector','anchor_extraction','physical_rows','physical_anchor_zero',
      'physical_anchor_norm','physical_no_go')]
    if orbit==18:names.append(S+'Orbit18.character_sum')
    GROUPS.append((labels,names,
      f'The literal orbit-{orbit} point indicator is proved on the entire actual top '
      'fiber. Its exact rational row combination isolates the actual anchor '
      'monomial from complete physical KL. The forced probability product 1/16 '
      'contradicts its vanishing without invoking the previous no-go result.'))
for orbit,labels in {
42:['eq:o42o43-momentform','eq:o42o43-domain'],
43:['eq:o42o43-momentform','eq:o42o43-domain'],
44:['eq:o44-momentform','eq:o44-uv','eq:o44-domain'],
46:['eq:o46-momentform','eq:o46-uv','eq:o46-domain'],
}.items():
    # Both 42 and 43 must be named together for their shared display.
    if orbit==43:continue
    orbits=(42,43) if orbit==42 else (orbit,)
    names=[M+f'Orbit{o}.'+n for o in orbits for n in ('bottom','top','bottomProb','topProb',
      'Domain','actual_words','normal_coordinates','domain_of_moment','reconstruct','complete_iff',
      'actual_matched_flip','matched_probabilities','physical_normal_form')]
    GROUPS.append((labels,names,
      'The literal real three-parameter probability family and exact nonnegative '
      'domain are equivalent in both directions to each complete native moment '
      'system. Actual word order, matched coordinate flip, and equality of '
      'bottom/top probabilities are checked independently of any no-code conclusion.'))
for orbits,labels in [((42,43),['eq:o42o43-walshdet']),((44,),['eq:o44-walshdet']),((46,),['eq:o46-walshdet'])]:
    names=[W+f'Orbit{o}.'+n for o in orbits for n in ('flip','characters','W','WC',
      'actual_incidence','actual_images','actual_characters','weights','matrix_checked',
      'factorization','determinant','complex_determinant','physical_rows',
      'physical_products_zero','physical_product_norm','physical_no_go')]
    GROUPS.append((labels,names,
      'The exact ten character rows are evaluated on all ten actual matched '
      'incidences in the printed row order. Kernel-checked LU gives the printed '
      'signed determinant. Complete physical KL forces every monomial to zero; '
      'matched probabilities and normalization give the literal exclusion.'))
GROUPS.append((['eq:m2-zsquare'],[W+'norm_sq_matched_product'],
    'The generic complex norm-square identity follows from equality of the two '
    'matched norms alone, with no no-code or distance hypothesis.'))
PROSE=[]
for orbit,lo,hi in [(18,14475,14477),(41,14582,14583),(42,14720,14723),
                    (43,14720,14723),(44,14791,14792),(46,14865,14866)]:
    # The shared 42/43 prose is recorded as one block with both actual matrices.
    if orbit==43:continue
    orbits=(42,43) if orbit==42 else (orbit,)
    PROSE.append((lo,hi,[R+f'Orbit{o}.'+n for o in orbits for n in
      ('bottom','top','actual_matrix','rows','columns','determinant','real_determinant','rank_exact','kernel_dimension')],
      'The actual 23-row occupation matrix, explicitly selected signed maximal '
      'minor, exact real rank and kernel dimension are independently proved.'))
PROSE += [
    (14423,14507,[S+'Orbit18.shell_types',S+'Orbit18.actual_shell_masses',S+'Orbit18.shell_system',
        S+'Orbit18.shell_solution',S+'Orbit18.point_projector',S+'Orbit18.physical_anchor_zero',
        S+'Orbit18.physical_anchor_norm',S+'Orbit18.physical_no_go'],
     'The complete literal orbit-18 shell and restricted-projector proof is '
     'checked from the actual physical diagonal and cross KL equations.'),
    (14527,14609,[S+'Orbit41.shell_types',S+'Orbit41.actual_shell_masses',S+'Orbit41.shell_system',
        S+'Orbit41.shell_chain',S+'Orbit41.shell_solution',S+'Orbit41.point_projector',
        S+'Orbit41.physical_anchor_zero',S+'Orbit41.physical_anchor_norm',S+'Orbit41.physical_no_go'],
     'The complete literal orbit-41 shell chain and four-character anchor '
     'projector are checked from the actual physical KL equations.'),
]
for orbit,lo,hi in [(42,14700,14739),(44,14767,14812),(46,14843,14880)]:
    orbits=(42,43) if orbit==42 else (orbit,)
    PROSE.append((lo,hi,[M+f'Orbit{o}.complete_iff' for o in orbits]+
        [W+f'Orbit{o}.'+n for o in orbits for n in ('determinant','physical_product_norm',
          'physical_products_zero','physical_no_go')],
        'The complete real moment normal form and literal signed ten-character '
        'system give the physical matched-flip exclusion at every boundary.'))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    evidence=ROOT/'artifacts/manuscript-certification-20261005/kernel-types-orbit31-completion.json'
    types=json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256']!=SOURCES:raise ValueError('Changed manuscript/type binding')
    required={n for row in GROUPS for n in row[1]}|{n for row in PROSE for n in row[2]}
    missing=required-{r['name'] for r in types['declarations']}
    if missing:raise ValueError('Uninspected roots: '+str(sorted(missing)))
    apply_reviews('supplementary',GROUPS,'order-two-printed-review',args.apply,
        expected_sources=SOURCES,review_prefix='20261005 literal physical intermediate/type review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    path=ROOT/'results/prose-review-20261003.json'
    record=json.loads(path.read_text(encoding='utf8'))
    paper_release.validate_review(record,'20261003',ROOT)
    lines=(ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
    rows=[{'source':'supplementary.tex','line':lo,'end_line':hi,'kind':'covered',
           'reason':reason,'declarations':names,'origin':'20261005 literal physical intermediate type review',
           'context_sha256_lf':hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
          for lo,hi,names,reason in PROSE]
    keys={(r['source'],r['line'],r['end_line']) for r in rows}
    record['assertions']=[r for r in record['assertions'] if
        (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]+rows
    record['status']='partial'
    paper_release.validate_review(record,'20261003',ROOT)
    if args.apply:
        path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        (evidence.parent/'order-two-printed-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'prose_blocks':rows,'scope':'Scoped current correspondence; full manuscript review remains incomplete'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Explicit prose blocks:',len(record['assertions']),'status:',record['status'])

if __name__=='__main__':main()
