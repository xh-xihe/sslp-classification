"""Review actual scalar moments, spinor rows and literal finite displays."""
import argparse, hashlib, json
from pathlib import Path
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES
ROOT=Path(__file__).resolve().parents[2]
D=ROOT/'artifacts/manuscript-certification-20261005'
F='MainTheory.Orbit5Displays.'
M='MainTheory.Orbit6MomentDisplays.'
S='MainTheory.Orbit6SpinorDisplays.'
T='MainTheory.Orbit12MomentDisplays.'
B='MainTheory.Orbit12Frames.'
GROUPS=[
 (['equation@11135'],['MainTheory.Orbit26MatchingZeroRow.sRow',
   'MainTheory.Orbit26MatchingZeroRow.physical_sRow_norm',
   'MainTheory.Orbit26MatchingZeroRow.physical_sRow_nonzero'],
  'The printed row is the actual normalized bottom anchor contracted with the actual block. When the other actual normalized row vanishes, physical block mass one quarter and the complete orthogonal anchor basis give this row squared norm one quarter and hence nonzero.'),
 (['eq:o5-tailnotation'],[F+n for n in ('Omega','hat','actualBottomTail','actualTopTail','actual_tail_notation')],
  'The literal four-bit all-one word, its singleton complements, and the actual bottom/top tail coordinates are checked on every finite index in the native six-qubit fibers.'),
 (['eq:o5-aggregatenorms'],['SixQubit.Trace5.nsq','SixQubit.Trace5.ip_self',
   'SixQubit.Orbit5.uu','SixQubit.Orbit5.aa1','SixQubit.Orbit5.aa2',
   'SixQubit.Orbit5.aa3','SixQubit.Orbit5.aa4','SixQubit.Orbit5.bb1',
   'SixQubit.Orbit5.bb2','SixQubit.Orbit5.bb3','SixQubit.Orbit5.bb4','SixQubit.Orbit5.vv',
   'MainTheory.Orbit5PhysicalRowData.physical_row_data'],
  'All aggregate symbols are squared Hermitian norms of the actual four-component native coefficient vectors. The physical row-data theorem supplies their printed anchor and singleton masses without using the final obstruction.'),
 (['eq:o5-marginal-u'],[F+'marginal_expectation',F+'physical_marginal_expectation'],
  'The actual full marginal matrix equality is contracted with the actual bottom anchor. Its four actual orthogonal top singleton terms vanish, leaving precisely the printed fourth-power norm and four squared pairing terms.'),
 (['eq:o5-vectorization'],[F+n for n in ('coord','coefficientMatrix','traceSecond','traceFirst','vectorization_second','vectorization_first')],
  'Both partial traces of an arbitrary two-qubit rank-one operator are defined entrywise and proved equal to the two printed coefficient-matrix products. The second identity uses entrywise conjugation, not matrix adjoint.'),
 (['eq:o5-matrixentries'],[F+'coefficientMatrix',F+'literal_coefficient_matrix'],
  'Vectorization of the arbitrary four actual coefficients gives exactly the displayed two-by-two entry order, including the row/column convention used by both partial traces.'),
 (['eq:o6-totalvalues','eq:o6-shellmasses'],[M+n for n in
   ('physical_moments','bottomProb','topProb','bottom_anchor','bottom_edge_mass',
    'top_singleton_mass','top_complement_mass','edge_coordinates','top_coordinates')],
  'Exact rational combinations of the complete actual moment equations give bottom anchor one third, bottom edge mass two thirds, top singleton mass two thirds and top complementary-singleton mass one third. All native coordinate-to-edge and singleton mappings are finite kernel checks.'),
 (['eq:o6-W5'],['MainTheory.Orbit6CharacterMatrix.W5',
   'MainTheory.Orbit6CharacterMatrix.determinant_checked'],
  'The literal five-by-five integer character matrix has kernel-computed determinant minus forty-eight. This review covers the displayed matrix and determinant; its derivation from individual physical character rows remains separate.'),
 (['eq:o6-matrixidentity'],[S+n for n in
   ('anchor','bottomEdge','topSingleton','topComplement','edgeOuter',
    'matrix_identity_of_data','physical_matrix_identity')],
  'For each of the five actual active coordinates, all four entries of the printed matrix identity are proved from the actual native one-flip rows before any final obstruction or vanishing of the top singleton vectors.'),
 (['eq:o12-anchor-equality'],[T+n for n in
   ('physical_moments','bottomProb','topProb','zero_anchor_equality','four_anchor_equality')],
  'The complete actual physical moments directly imply equality of each bottom/top empty and full active-subset anchor squared norm, with both zero-angle components included.'),
 (['equation@15500','eq:o12-Hmoment'],[T+n for n in
   ('bottomProb','topProb','physical_moments','edge_coordinates','half_angle_moment')],
  'The two edge masses are precisely sums of squared moduli over the actual paired free-bit coordinates. The literal half-angle-bit labels and its physical moment equation give the printed equality with the two actual top anchor norms.'),
 (['eq:o12-shellmasses'],[T+n for n in
   ('physical_moments','bottom_edge_mass','top_edge_mass','bottom_anchor_mass','top_anchor_mass')],
  'All four printed total shell and anchor masses equal one half as exact rational consequences of the actual full moment system.'),
 (['eq:o12-anchor-quarter'],[T+n for n in
   ('physical_moments','bottom_zero_anchor','bottom_four_anchor','top_zero_anchor','top_four_anchor')],
  'Each of the four actual paired free-bit anchor norms equals one quarter, independently of the final no-code conclusion.'),
 (['eq:o12-edgedegrees'],[T+'physical_moments',T+'edge_coordinates']+
   [T+f'edge_degree_{i}' for i in range(4)],
  'At each of the four printed active graph vertices the sum of actual bottom edge norms is exactly one quarter; the edge order is checked against the actual native words.'),
 (['eq:o12-edgepolytope'],[T+'physical_moments',T+'representative_mass']+
   [T+f'complementary_mass_{i}' for i in range(3)]+[T+'bottomProb',T+'Moment'],
  'The three complementary pairs of actual edge norms agree, their representative sum is one quarter, and each is nonnegative because it is a sum of complex squared moduli. This is the displayed necessary polytope constraint, not an assertion that arbitrary points satisfy full physical KL.'),
 (['eq:o12-AH-crossblock','eq:o12-H0frame'],[B+n for n in
   ('u','v','ut','vt','a','b','outer','AHcrossBlock','H0bottomFrame',
    'H0topFrame','cross_block_of_data','H0_frame_of_data','physical_blocks')],
  'The two actual anchor spinors and six actual edge spinors retain their native free-bit coefficient order. Actual AH one-flip rows make all four cross-block entries zero; actual H=0 diagonal and off-diagonal rows make all four positive frame entries equal.'),
 (['eq:parity4-edgedet'],['MainTheory.ParityFourEdgeDeterminant.'+n for n in
   ('other','evenPoint','rowMask','W','literal_even_points','gram_checked','absolute_determinant')],
  'For every one of the four parity-changing directions, the actual eight-point even-parity character matrix has Gram matrix eight times identity. Taking determinants and the real square identity gives exactly the printed absolute determinant 4096.'),
]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    for phase in ('scalar-spinor-completion-full-build-v1','scalar-spinor-completion-type-inspection-v1'):
        if json.loads((D/(phase+'-exit.json')).read_text(encoding='utf8'))['exit_code']!=0:
            raise ValueError('Canonical verification has not passed: '+phase)
    evidence=D/'kernel-types-scalar-spinor-completion-v1.json'
    types=json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256']!=SOURCES:
        raise ValueError('Changed manuscript/type binding')
    missing={n for _,roots,_ in GROUPS for n in roots}-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected roots: '+str(sorted(missing)))
    apply_reviews('supplementary',GROUPS,'scalar-spinor-completion-review-v2',args.apply,
        expected_sources=SOURCES,
        review_prefix='20261005 actual scalar/spinor type and context review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (D/'scalar-spinor-completion-type-binding-v2.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'scope':'Only listed actual scalar/spinor intermediates; other obligations remain.'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8',newline='\n')

if __name__=='__main__':
    main()
