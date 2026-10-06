"""Review the remaining literal order-four and order-five intermediate displays."""
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

W='MainTheory.OrderFiveWalshRemainingDisplays.'
G='MainTheory.OrderFiveGridRemainingDisplays.'
F='MainTheory.OrderFourWalshRemainingDisplays.'
GROUPS=[
    (['displaymath@9919','displaymath@9923'],
     [W+'Orbit34.incidence_all',W+'Orbit34.flip_images',W+'Orbit34.separating_signs',W+'Orbit34.weights',W+'Orbit34.physical_two_rows'],
     'Both literal rows are proved for every distinct physical coordinate pair, with the complete two-source incidence and weight-at-most-two checks.'),
    (['displaymath@9981'],[W+'Orbit39.sources',W+'Orbit39.destinations',W+'Orbit39.characters',W+'Orbit39.actual_incidence',W+'Orbit39.actual_images',W+'Orbit39.source_characters',W+'Orbit39.determinant'],
     'The exact five sources, five characters I,Z2,Z3,Z4,Z5, source/destination convention and signed determinant 16 are checked against the actual fibers.'),
    (['displaymath@10043'],[G+'Orbit38.A',G+'Orbit38.B',G+'Orbit38.literal_labels'],
     'The actual four A words, two-by-four B grid and star exhaust S0. All top grid labels are the actual complements.'),
    (['eq:o38commonphase'],[G+'Orbit38.physical_hub',G+'Orbit38.physical_star_nonzero',G+'Orbit38.physical_weighted_phases',G+'Orbit38.physical_common_phase'],
     'Actual physical hub rows yield the common phase on every active B entry. The weighted relation also retains zero B amplitudes; both star amplitudes are proved nonzero from moments.'),
    (['eq:o38permanent'],[G+'Orbit38.physical_rectangle',G+'Orbit38.physical_permanents'],
     'All six literal rectangle rows are derived from physical KL and the common nonzero star phase, yielding the permanents without assuming grid positivity.'),
    (['displaymath@10109','displaymath@10118'],[G+'Orbit38.rowSupport','MainTheory.GridSupportAlgebra.full_support','MainTheory.GridSupportAlgebra.supports_univ',G+'Orbit38.physical_supports_full'],
     'Row supports are the nonzero actual amplitudes. Positive row masses and column masses, together with the actual permanents, imply both complete four-column supports, including boundary cases.'),
    (['displaymath@10192'],[G+'Orbit37.activeColumns',G+'Orbit37.rowSupport',G+'Orbit37.A',G+'Orbit37.B',G+'Orbit37.actual_complements'],
     'J is precisely the support of the actual A amplitudes. Each R_i is the B-row support restricted to J, with the printed ordering and actual complementary coordinates retained.'),
    (['displaymath@10200'],[G+'Orbit37.physical_reciprocal',G+'Orbit37.physical_sync',G+'Orbit37.physical_active_column_phase'],
     'For each active A and B entry in a column, physical reciprocity and all nine signed sync rows give the same phase, opposite to the star phase. Nonzero star mass is proved as 1/10.'),
    (['equation@11194','eq:q4o27weightoneprob'],[F+'Orbit27.consequence0',F+'Orbit27.consequence1',F+'Orbit27.physical_probabilities'],
     'The exact bottom-zero mass 3/8 and total weight-one top mass 5/8 are derived using rational combinations of the actual normalization and diagonal degree-two moments.'),
    (['eq:q4o27W6','equation@11223','equation@11228'],[F+'Orbit27.actual_characters',F+'Orbit27.actual_incidence',F+'Orbit27.actual_images',F+'Orbit27.determinant',F+'Orbit27.physical_matrix_rows',F+'Orbit27.physical_all_edges_zero',F+'Orbit27.AllCoordinates.physical_weight_one_zero'],
     'The literal six-edge matrix, signed determinant -128, and every individual product are certified. A separately checked all-coordinate matrix identity forces all six actual weight-one top amplitudes to vanish.'),
    (['eq:q4o62probabilities'],[F+'Orbit62.physical_probabilities',F+'Orbit62.actual_complements',F+'Orbit62.physical_all_nonzero'],
     'All fourteen actual probabilities are pinned, with complementary masses 1/4 at zero and 1/8 elsewhere; every bottom and top amplitude is independently proved nonzero.'),
    (['equation@12660','equation@12665','equation@12673','equation@12682'],[F+'Orbit62.rho',F+'Orbit62.triangle',F+'Orbit62.flips',F+'Orbit62.actual_incidence',F+'Orbit62.actual_images',F+'Orbit62.weights',F+'Orbit62.physical_triangle_rows',F+'Orbit62.physical_phase_triangle'],
     'The actual SI triangle is (000000,111100,010111), with flips X5X6,X2X4,X1X3. All three complete two-incidence sets and all three phase oppositions are checked, with their quotient denominators proved nonzero.'),
]
PROSE=[
    (10079,10103,[G+'Orbit38.physical_hub',G+'Orbit38.physical_common_phase',G+'Orbit38.physical_rectangle',G+'Orbit38.physical_permanents'],
     'The physical star-to-grid rows, common active phase and rectangle permanent reduction retain all zero-amplitude boundaries.'),
    (10106,10121,['MainTheory.GridSupportAlgebra.full_support',G+'Orbit38.physical_supports_full'],
     'Actual positive row and column masses and all permanents force full support in both grid rows.'),
    (11191,11237,[F+'Orbit27.physical_probabilities',F+'Orbit27.determinant',F+'Orbit27.AllCoordinates.physical_weight_one_zero'],
     'The exact masses, actual six-edge rows and every physical coordinate version give the complete Walsh exclusion.'),
    (12647,12688,[F+'Orbit62.physical_probabilities',F+'Orbit62.actual_complements',F+'Orbit62.physical_all_nonzero',F+'Orbit62.physical_phase_triangle'],
     'All complementary probability pins and the literal SI three-mask odd cycle are separately proved.'),
]

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
    apply_reviews('supplementary',GROUPS,'order-four-five-remaining-review',args.apply,
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
        (evidence.parent/'order-four-five-remaining-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'prose_blocks':rows,'scope':'Scoped current correspondence; full manuscript review remains incomplete'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Explicit prose blocks:',len(record['assertions']),'status:',record['status'])

if __name__=='__main__':main()
