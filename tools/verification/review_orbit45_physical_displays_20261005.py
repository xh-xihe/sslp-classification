"""Review actual orbit-45 intermediate formulas against fresh kernel types."""
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
P='MainTheory.Orbit45PhysicalPrintedRows.'
S='MainTheory.Orbit45PhysicalSpinFlip.'
D='MainTheory.Orbit45PhysicalProbabilityDomain.'
G='MainTheory.Orbit45AffineGauge.'
F='MainTheory.Orbit45CrossFactors.'
Z='MainTheory.Orbit45PrintedDiagonalContribution.'
Q='MainTheory.Orbit45PhysicalGauge.'
B='MainTheory.Orbit45BottomGauge.'
T='MainTheory.Orbit45TopGauge.'
N='MainTheory.Orbit45PhysicalPhaseNormalForm.'
K='MainTheory.Orbit45PhysicalCanonicalForm.'
O='MainTheory.Orbit45OrientedCoherences.'
E='MainTheory.Orbit45PrintedEnumerator.'
J='MainTheory.Orbit45DressingParseval.'
V='MainTheory.Orbit45PrintedOffContribution.'
C='MainTheory.Orbit45TriangleExistence.'
GROUPS=[
(['eq:o45-A2-off-before','eq:o45-A2-off'],
 [J+n for n in ('Dressing','error','sources','target','signSource','signDestination','complete_dressings',
  'checked_dressing_z','dressing_exhaustion','dressings_injective','bottom_incidence','bottom_images',
  'bottom_characters','value','parseval','actual_bottom_value','physical_parseval')]+
 [V+'table_norm_sum',V+'physical_off_contribution',V+'physical_off_reduction'],
 'Every actual XX/XY/YX/YY dressing has its literal physical compression '
 'from the oriented incidence sum. The complete four dressings give exactly '
 '8 normSq(F), and the four masks give the printed weighted square-root '
 'formula. The unit vector triangle reduces this actual contribution to '
 '1/2-16R, rather than an abstract quantity bearing the same name.'),
(['eq:o45-A2-final','eq:o45-A3-final','displaymath@7065','displaymath@7073'],
 [E+n for n in ('literal_block_positions','printed_block_masses','physical_A2','physical_A3',
  'physical_full_enumerators','boundary_permutations','boundary_R','physical_boundary')],
 'The actual printed beta/gamma/sigma probabilities are tied explicitly '
 'to the three native block masses, in the correct permutation and scaling. '
 'The normalized full enumerators have t=32R for every actual code. '
 'Zero product forces precisely the three printed boundary triples and '
 'the actual normalized coefficients A2=1 and A3=0, without nonzero amplitudes.'),
(['eq:o45-canonical-c'],
 [N+'physical_phase_normal_form',K+'physical_forced_phases',K+'physical_triangle',K+'physical_canonical_form',
  'MainTheory.Orbit45PrintedAttainment.canonical_bottom','MainTheory.Orbit45PrintedAttainment.canonical_top',
  'MainTheory.Orbit45PrintedAttainment.full_kl'],
 'Every actual positive-stratum code is physically diagonally and logically '
 'phase equivalent to the final literal canonical amplitudes, with unit xi, '
 'unit eta and the actual vector triangle. Conversely the printed family '
 'satisfies complete physical KL. Both directions use actual codewords.'),
(['eq:o45-within-fiber-masks','displaymath@6936','eq:o45-oriented-coherences'],
 [O+n for n in ('pairs','flip','sourceIndices','destinationIndices','channel','orientedSet',
  'all_within_masks','bottom_incidence','top_incidence','source_injective','bottom_images','top_images',
  'unique_channel','oriented','oriented_restrict','row','bottom_expansion','top_expansion','table',
  'literal_table','physical_table','printedTable','square_root_table','physical_printed_table')],
 'The four literal masks exhaust every nonidentity within-fiber incidence '
 'of weight at most two in both actual fibers. Each orientation has exactly '
 'the same two printed source/destination pairs and a unique occupied channel. '
 'The zero-extended physical sum equals its finite indexed expression, and '
 'both actual canonical words give precisely all four square-root coherences.'),
(['eq:o45-logical-action'],['MainTheory.Orbit45PrintedLogicalAction.root_cube',
 'MainTheory.Orbit45PrintedLogicalAction.physical_logical_action'],
 'The actual standard sixth root exp(pi I/3) cubed is -1. Every state '
 'supported in the literal residue-zero or residue-three fiber is respectively '
 'fixed or negated by the actual diagonal gate, including boundary supports.'),
(['eq:o45-bottom-phase-gauge','eq:o45-top-phase-gauge'],
 [Q+n for n in ('FullKL','frame','code','diagonal_fullKL','rephase_fullKL','global_unit',
  'phaseAction_fullKL','phaseAction_normSq','phaseAction_probabilities','physical_anchor_gauge','physical_relative_gauge')]+
 [B+n for n in ('equal_norm','physical_norms','bottom_canonical','half_amplitude','physical_bottom_gauge')]+
 [T+'top_norm',T+'top_canonical',N+'physical_phase_normal_form'],
 'Every actual supported normalized positive-stratum distance-three code '
 'admits physical diagonal angles and unit logical phases giving both literal '
 'printed gauges. The square-root amplitudes, h=1/sqrt(8), all six unit phases, '
 'probability preservation and the complete physical KL predicate are retained. '
 'The gauges are constructed from arbitrary actual codes rather than assumed.'),
(['eq:o45-codewords-general'],[P+'codewords'],
 'Every arbitrary actual supported logical state equals the full printed indexed ket expansion; zero coefficients remain allowed.'),
(['displaymath@6596'],[P+'characters',P+'weights',P+'actual_row_signs',P+'physical_walsh',
 'MainTheory.Orbit45PrintedWalsh.masks','MainTheory.Orbit45PrintedWalsh.actual_rows'],
 'The twelve actual weight-at-most-two Pauli rows use precisely the printed one-coordinate matching and character dressings. Evaluating on the top rather than bottom fiber produces verified nonzero row signs and the same homogeneous kernel.'),
(['eq:o45-A-gauge'],['MainTheory.Orbit45RelativeLogicalPhase.'+n for n in
 ('phase','fixed_norm','phase_unit','relative_gauge')],
 'The nonzero actual half-angle parameter admits the explicit unit relative logical phase (1/8)/A. This preserves support, normalization and all physical KL equations while setting A exactly to 1/8.'),
(['eq:o45-spin-flip','eq:o45-spinflip-basis'],
 ['MainTheory.Orbit8SpinSemantics.'+n for n in ('spinJ_pauli','spinJ_tensor','spinSign_power','spinJ_basis')]+
 ['MainTheory.Orbit8SpinProjector.spin_conjugate_action','MainTheory.Orbit8SpinProjector.spin_family'],
 'The actual anti-linear map is Y tensor six times complex conjugation; its basis sign differs from (-1)^weight by one harmless common phase. The projector conjugation and its family kernel are proved at the actual matrix level.'),
(['eq:o45-shadow-spinflip'],[S+'general_shadow_trace','MainTheory.Orbit8SpinProjector.trace_core',
 'MainTheory.Orbit8SpinProjector.spinflip_enumerator']+
 ['MainTheory.Orbit45ShadowNormalization.'+n for n in ('identity','identity_kernel','S0','shadow_trace','shadow_normal_form')],
 'For any normalized distance-three physical pair, the actual spin-conjugated projector trace equals one half of 1-A1-A2-A3 in the manuscript normalization. The zeroth shadow coefficient is one half of this trace.'),
(['eq:o45-spinflip-overlap','eq:o45-shadow-zero','eq:o45-A2A3-line'],
 [P+'physical_reversal',P+'physical_paired_products',P+'spinSum',P+'physical_spin_sum_zero']+
 [S+n for n in ('complementary_fibers','parity_sign','pair_overlap','diagonal_overlaps',
 'pairing_symmetric','physical_overlaps_zero','physical_spin_trace_zero','physical_A1_zero','physical_A2_A3_line')]+
 ['MainTheory.Orbit45ShadowNormalization.physical_shadow_zero'],
 'The literal ten-term pairing is the actual shadow/spin-flip overlap. Its reverse-index terms cancel from the actual moment and Walsh systems, including zero amplitudes. All four overlaps and the projector trace vanish, and A1=0 yields the printed A2+A3=1.'),
(['eq:o45-positive-stratum'],[D+'physical_probabilities',D+'triangle_domain',D+'positive_stratum'],
 'The literal product beta gamma sigma is positive exactly when every bottom and top coefficient is nonzero. The actual physical moment/cross equations force the displayed fixed mass and triangle probability domain.'),
(['displaymath@6788'],[G+n for n in ('anchors','A','actual_rows','inverse_checked','factorization',
 'determinant','real_determinant','solve_angles','localPhases','globalPhase','phaseAction',
 'value_exponential','affine_angle','normalize_arg','anchors_positive')],
 'The seven literal affine phase rows have signed determinant six. Their exact inverse gives real global and local diagonal angles making those actual bottom coefficients positive real on the positive stratum.'),
(['eq:o45-remaining-cross-masks','eq:o45-cross-factor-table','eq:o45-forced-phases','eq:o45-vector-triangle'],
 [F+'C',F+'D',F+'pairs',F+'flip',F+'all_cross_masks',F+'forced_phases',F+'triangle_after_gauge',F+'remaining_factors_zero']+
 [F+f'Row{i}.'+n for i in range(6) for n in ('sourceIndices','destinationIndices','sources','destinations',
 'characters','walsh','actual_incidence','actual_images','actual_characters','weights','matrix_checked',
 'physical_rows','gaugeProducts','factors','substitution','physical_factors')],
 'The complete six remaining actual cross incidences and all four dressings are checked. Literal substitution of the preceding displayed gauges gives every factor with the common amplitude and unit-phase denominators retained. On the positive stratum these factors force U=-1, V=conjugate xi, W=conjugate eta and zeta=1; all remaining factors then vanish and the vector triangle has the printed form.'),
(['eq:o45-lambdaij','eq:o45-ZZ-table','eq:o45-A2-diagonal'],[Z+n for n in
 ('pairs','pairZ','table','actual_bottom_characters','actual_top_characters','pure_pair_classification',
 'pair_injective','literal_table','indexed_expectation','physical_table','squared_contribution','physical_contribution')],
 'All fifteen actual weight-two pure-Z expectations in the printed qubit order are derived from the physical probability normal form on both logical states. These exhaust the pure-Z pairs and their squared sum is exactly 48R-1/2.'),
]
PROSE=[
 (6532,6539,[P+'codewords'], 'The printed general logical words are the actual complete-fiber indexed ket expansions.'),
 (6599,6607,['MainTheory.Orbit45PrintedWalsh.rank_seven','MainTheory.Orbit45PrintedWalsh.selectedRows',
  'MainTheory.Orbit45PrintedWalsh.selectedCols','MainTheory.Orbit45PrintedWalsh.minor_absolute_determinant',P+'physical_walsh'],
  'The actual half-angle rows have rank seven and the literal selected seven-column minor has absolute determinant 256. Nonzero physical/printed row signs are explicitly checked.'),
 (6695,6771,[S+'general_shadow_trace',S+'physical_overlaps_zero',S+'physical_spin_trace_zero',S+'physical_A1_zero',S+'physical_A2_A3_line'],
  'The actual spin flip, complementary index pairing, zero-overlap trace and A2+A3=1 are proved for arbitrary supported physical codes, including all zero-amplitude boundaries.'),
 (6783,6793,[G+'actual_rows',G+'determinant',G+'solve_angles',G+'anchors_positive',
  Q+'diagonal_fullKL',Q+'rephase_fullKL',Q+'phaseAction_fullKL',Q+'physical_anchor_gauge'],
  'The exact seven affine phase rows are invertible over the reals and yield the claimed physical/global phase normalization, preserving actual supports, probabilities, normalization and every physical KL equation.'),
 (6794,6831,[B+'physical_bottom_gauge',T+'top_canonical',N+'physical_phase_normal_form'],
  'Both literal gauges are constructed for every actual positive-stratum code. The top amplitudes follow from actual half-angle and paired-product equations after a unit relative logical phase; no displayed gauge is assumed.'),
 (6832,6889,[F+'all_cross_masks',F+'forced_phases',F+'triangle_after_gauge',F+'remaining_factors_zero']+
  [F+f'Row{i}.substitution' for i in range(6)]+[F+f'Row{i}.physical_factors' for i in range(6)],
  'Given the preceding displayed positive-stratum gauges, every actual remaining cross-KL row has the printed factorization and forces precisely the stated phases. Coverage here is conditional on those gauges; their complete arbitrary-code construction is reviewed separately.'),
 (6890,6925,[K+'physical_canonical_form','MainTheory.Orbit45PrintedAttainment.canonical_bottom',
  'MainTheory.Orbit45PrintedAttainment.canonical_top'],
  'The final printed canonical words are available for every actual positive-stratum solution, with the complete physical KL predicate, unchanged probabilities and literal vector triangle retained.'),
 (6926,6957,[O+'all_within_masks',O+'unique_channel',O+'physical_printed_table',
  'MainTheory.Orbit45PrintedAttainment.full_kl'],
  'The complete within-fiber incidence classification, unique occupied channels and identical literal coherences on both words are proved. The printed family independently satisfies every physical distance-three KL equation.'),
 (6958,6979,[C+'domain_phases',C+'canonical_fullKL',C+'every_triple_completion',
  'MainTheory.Orbit45PrintedAttainment.canonical_bottom','MainTheory.Orbit45PrintedAttainment.canonical_top',
  'MainTheory.Orbit45PrintedLogicalAction.physical_logical_action'],
  'Every triple in the printed triangle domain admits explicit unit phases and actual canonical logical words with full fiber support conditions, normalization, orthogonality, distance-three KL and the claimed diagonal logical action. All boundary triples are included.'),
 (7018,7048,[J+'dressing_exhaustion',J+'parseval',J+'actual_bottom_value',J+'physical_parseval',
  V+'physical_off_contribution',V+'physical_off_reduction'],
  'The complete actual Pauli dressings give the stated Parseval coefficient eight and the printed off-diagonal enumerator contribution; the displayed vector triangle gives its exact polynomial reduction.'),
 (7062,7078,[E+'printed_block_masses',E+'physical_A2',E+'physical_A3',E+'physical_full_enumerators',
  E+'boundary_permutations',E+'boundary_R',E+'physical_boundary'],
  'The printed probability coordinates determine the actual normalized enumerators. Every zero-product boundary is one of the three literal triples and has the actual coefficients A2=1, A3=0.'),
]
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
    apply_reviews('supplementary',GROUPS,'orbit45-physical-review',args.apply,
        expected_sources=SOURCES,review_prefix='20261005 actual orbit-45 intermediate/type review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    path=ROOT/'results/prose-review-20261003.json'
    record=json.loads(path.read_text(encoding='utf8'))
    paper_release.validate_review(record,'20261003',ROOT)
    lines=(ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
    rows=[{'source':'supplementary.tex','line':lo,'end_line':hi,'kind':'covered','reason':reason,
       'declarations':names,'origin':'20261005 actual orbit-45 intermediate/type review',
       'context_sha256_lf':hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
       for lo,hi,names,reason in PROSE]
    keys={(r['source'],r['line'],r['end_line']) for r in rows}
    record['assertions']=[r for r in record['assertions'] if
        (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]+rows
    record['status']='partial'
    paper_release.validate_review(record,'20261003',ROOT)
    if args.apply:
        path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        (evidence.parent/'orbit45-physical-type-binding.json').write_text(json.dumps({
          'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
          'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),'prose_blocks':rows,
          'scope':'Scoped physical intermediate correspondence; other manuscript review remains incomplete'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Explicit prose blocks:',len(record['assertions']),'status:',record['status'])
if __name__=='__main__':main()
