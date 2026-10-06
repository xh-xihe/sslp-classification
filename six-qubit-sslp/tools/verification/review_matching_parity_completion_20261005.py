"""Review literal moments and actual matching/parity intermediates."""
import argparse,hashlib,json
from pathlib import Path
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES
ROOT=Path(__file__).resolve().parents[2];D=ROOT/'artifacts/manuscript-certification-20261005'
M='MainTheory.Orbit26MatchingPhysical.'
N='MainTheory.Orbit26MatchingNotation.'
C='MainTheory.Orbit26MatchingComponents.'
U='MainTheory.Orbit26NormalizedRows.'
P='MainTheory.Orbit26NonmatchingPhysical.'
F='MainTheory.Orbit13Frames.'
R='MainTheory.OrderTwoRecordResidues.'
B='MainTheory.Orbit14BlockFrames.'
T='MainTheory.Orbit17MomentDisplays.'
Q='MainTheory.Orbit17ConjugatePhases.'
GROUPS=[
 (['equation@11047'],[N+'complementary_projector_sum',P+'physical_nonmatching_projectors'],
  'The actual nonmatching-branch unit anchor projectors sum to the identity. The checked matrix identity gives precisely the printed equality of the sum of their complementary projectors and the sum of the projectors.'),
 (['equation@11059'],[U+'unitAnchor',P+'physical_normalized_data',N+'kappa',N+'kappa_bounds',N+'kappa_sq'],
  'The normalized directions are the actual first columns divided by their fixed positive norm. Kappa is the norm of their Hermitian pairing, lies between zero and one, and its square is the actual complex squared modulus.'),
 (['eq:q4o26cdgauge'],['MainTheory.Orbit26AnchorGauge.standard_form_kappa',P+'physical_normalized_data',N+'kappa'],
  'The unitary two-spinor gauge retains the actual overlap modulus: the returned real first coordinate equals kappa, rather than an unrelated existential scalar. The second coordinate is its nonnegative complementary square root and the first direction is the first basis vector up to a unit phase.'),
 (['eq:q4o26firstrowD'],[M+'physical_firstrowD'],
  'The actual physical anchor row equation is divided by the common positive anchor norm, giving the printed conjugate negative first-row relation for every actual nonanchor block.'),
 (['eq:q4o26rJr'],[M+'physical_Jrows'],
  'The actual physical outer-flip matrix equation is contracted with the two actual normalized anchors. Substitution of the actual first-row relations gives every displayed symmetric J relation.'),
 (['eq:q4o26rsum'],[M+'physical_row_sum',N+'kappa_sq'],
  'The actual nonanchor Gram sum and normalized rank-one anchors give exactly one half plus one quarter of the squared actual overlap modulus, with no final no-code conclusion used.'),
 (['eq:q4o26cperpd'],[M+'physical_anchor_orthogonal',N+'physical_kappa_zero'],
  'The actual row sum, three pairwise J relations, group bounds and coordinate-axis bounds force the actual anchor Hermitian pairing and its norm kappa to vanish.'),
 (['eq:q4o26twofullrows'],[M+'physical_two_full_rows'],
  'There is exactly one zero actual normalized bottom row; each of the other two has squared norm one quarter. The proof uses the actual physical moment and column bounds and the J-axis lemma.'),
 (['eq:q4o26skr'],[C+'physical_mixed_J_rows',C+'complementary_row_zero',C+'row_norm_decomposition',C+'physical_anchor_basis'],
  'The two unit actual anchors form a complete orthogonal basis. Saturation of an actual group norm removes the complementary row. The actual physical outer-flip equation then gives the mixed J relation between the remaining anchor-direction row and each full row.'),
 (['eq:o19-h-u'],['MainTheory.Orbit19ShellDisplays.h','MainTheory.Orbit19ShellDisplays.u',
   'MainTheory.Orbit19TailIdentity.mismatch_square'],
  'Both polynomial definitions are literal; the Boolean tail polynomial is also exactly the square of the difference of the two actual final bits.'),
 (['eq:o17-normalizations'],[T+'physical_moments',T+'bottom_normalization',T+'top_normalization',T+'shell_first',T+'shell_second',T+'edge_coordinates'],
  'The complete actual physical moment system supplies both normalizations and both displayed shell equations. The edge order is explicitly checked against the complementary bottom words and top two-subsets.'),
 (['eq:o17-anchor-masses'],[T+'bottom_anchor',T+'top_anchor',T+'bottom_edge_mass',T+'top_edge_mass',T+'physical_moments'],
  'Exact rational combinations of the actual full moment system give both anchor squared norms one quarter and both total edge masses three quarters.'),
 (['eq:o17-degree-sum'],[T+f'degree_sum_{i}' for i in range(6)]+[T+'physical_moments',T+'edge_coordinates'],
  'At each of the six actual graph vertices the sum of the two matched weighted degrees is exactly one half.'),
 (['eq:o17-degree-second'],[T+f'degree_second_{i}' for i in range(6)]+[T+'physical_moments'],
  'At every actual vertex the rational pair-moment combinations give three times the bottom weighted degree plus the top weighted degree equal to one.'),
 (['eq:o17-degree-quarter'],[T+f'{side}_degree_{i}' for side in ('bottom','top') for i in range(6)]+[T+'physical_moments'],
  'All twelve actual weighted degrees equal one quarter, with the exact edge indexing and complete physical moments retained.'),
 (['eq:o17-matched-magnitudes','eq:o17-fractionalmatching'],
  [T+f'matched_mass_{i}' for i in range(15)]+[T+f'bottom_degree_{i}' for i in range(6)]+
  [T+'bottom_anchor',T+'top_anchor',T+'edge_coordinates',T+'physical_moments'],
  'Every one of the fifteen actual complementary bottom/top edge magnitudes agrees, both anchors have squared norm one quarter, and all six edge-degree sums are one quarter. The displayed forward normal-form assertions are directly derived; converse prose is a separate context obligation.'),
 (['eq:o17-lambda','eq:o17-conjugate-phases'],[Q+'phaseRatio',Q+'physical_phase_unit',Q+'indexed_anchor_flips',Q+'physical_conjugate_phases'],
  'The ratio uses the printed negative top anchor divided by the conjugate bottom anchor. Its norm is one, with the denominator proved nonzero. All fifteen actual top edge amplitudes equal that common ratio times the conjugate complementary bottom amplitude, including zero edges.'),
 (['eq:o12-record','eq:o13-record','eq:o14-record','eq:o15-record','eq:o24-record'],[R+'row',R+'angle',R+'records_checked'],
  'The five exact printed q=4, m=2 and six-coordinate representatives match their actual finite orbit-table rows, using the manuscript row numbers rather than an auxiliary fiber identifier.'),
 (['equation@15898','equation@16016','eq:o24-residue'],[R+n for n in ('residue','orbit14_residue','orbit15_residue','orbit24_residue','orbit14_fibers','orbit15_fibers','orbit24_fibers')],
  'All three printed modular residue polynomials agree with the actual finite angle records on every six-bit word, and their zero/half residues are exactly the native physical bottom/top fibers. Orbit 24 explicitly uses the equality of coefficients three and minus one modulo four.'),
 (['eq:o24-repetition-paulis'],['MainTheory.Orbit24RepetitionPaulis.'+n for n in
   ('R','literal_repetition','actual_isometry','labels','effectivePauli','actual_operator','actual_compressions','physical_weights')],
  'The actual repetition isometry maps each effective basis bit to two identical physical bits. Literal Gaussian-integer Pauli compression identities are transported to actual complex tensor Paulis, proving the printed Z, XX and YX compressions and their physical weights at most two.'),
 (['eq:o13-R','eq:o13-Pr','eq:o13-bottomword'],[F+n for n in ('R','pack','flipLast','literal_R','literal_fibers','bottom_coordinates','top_coordinates','bottomSpinor','topSpinor')],
  'The four literal three-bit patterns and their two parity-selected tail words exhaust the actual bottom fiber. Flipping the final physical bit gives the complete top fiber in the printed matching convention, with both zero-angle spinor components retained.'),
 (['eq:o13-Pir'],[F+'character',F+'pointProjector',F+'projector_checked'],
  'The literal restricted character polynomial is exactly the indicator of each of the four actual three-bit patterns on that four-point domain.'),
 (['eq:o13-X6overlaps','eq:o13-X5overlaps','eq:o13-completeorthogonality'],[F+'orthogonality_of_data',F+'physical_frames','MainTheory.Orbit13BlockData.physical_block_data'],
  'All four actual bottom/top spinor pairings vanish within every printed three-bit block. Both identical-tail and opposite-tail incidences are included, deriving complete block orthogonality before any block annihilation or final contradiction.'),
 (['eq:o13-blockframes','eq:o13-frameequality','eq:o13-frameproduct'],[F+'bottomFrame',F+'topFrame',F+'frame_of_data',F+'frame_product_zero',F+'physical_frames'],
  'The actual positive block frames sum both literal tail spinors. Each of their four matrix entries agrees by actual KL and moments, and complete block orthogonality makes their actual matrix product zero. No earlier no-go result is used.'),
 (['eq:o14-blockframes','eq:o14-blockframeequality'],[B+n for n in ('blockIndex','block_labels','block_labels_exact','bottomBlockFrame','topBlockFrame','block_frame_of_data','physical_block_frame_equality')],
  'The two actual fixed-repetition-bit blocks are exactly the corresponding four even/odd labels. Both complete two-by-two block frames agree entry by entry under actual physical KL, including diagonal and conjugate off-diagonal entries.'),
 (['eq:o14-edgeorthogonality'],['MainTheory.Orbit14EdgeRows.'+n for n in ('middleAdjacent','middle_adjacent_checked','edge_rows_of_data','physical_edge_rows')],
  'Every actual parity-changing edge in one of the three half-angle directions has zero spinor Hermitian pairing. The literal adjacency enumeration fixes the repetition coordinate and checks all twenty-four incidences against actual physical KL rows.'),
]

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    for phase in ('matching-parity-completion-full-build-v1','matching-parity-completion-type-inspection-v2'):
        if json.loads((D/(phase+'-exit.json')).read_text(encoding='utf8'))['exit_code']!=0:
            raise ValueError('Canonical verification has not passed: '+phase)
    evidence=D/'kernel-types-matching-parity-completion-v2.json'
    types=json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256']!=SOURCES:raise ValueError('Changed manuscript/type binding')
    missing={n for _,roots,_ in GROUPS for n in roots}-{r['name'] for r in types['declarations']}
    if missing:raise ValueError('Uninspected roots: '+str(sorted(missing)))
    apply_reviews('supplementary',GROUPS,'matching-parity-completion-review',args.apply,
        expected_sources=SOURCES,review_prefix='20261005 physical matching/parity type and context review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (D/'matching-parity-completion-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'scope':'Only listed actual physical intermediates. Other SI claims and prose remain incomplete.'},
            ensure_ascii=False,indent=2)+'\n',encoding='utf8',newline='\n')
if __name__=='__main__':main()
