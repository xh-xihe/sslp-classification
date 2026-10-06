"""Review every literal orbit-30 formula against its physical kernel route."""
import argparse,hashlib,json,sys
from pathlib import Path
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
import paper_release
P='MainTheory.Orbit30PrintedMoments.'
L='MainTheory.Orbit30ProbabilityLabels.'
R='MainTheory.Orbit30PhysicalRows.'
F='MainTheory.Orbit30PhysicalPhases.'
G='MainTheory.Orbit30PhysicalGraph.'
H='MainTheory.Orbit30PhysicalHafnians.'
M='MainTheory.Orbit30PhysicalMask.'
C='MainTheory.Orbit30GraphClassification.'
T='MainTheory.Orbit30ProperGraphTables.'
E='MainTheory.Orbit30ProperGraphExclusion.'
V='MainTheory.Orbit30VertexScaling.'
D='MainTheory.Orbit30NormalizedDeterminant.'
B='MainTheory.Orbit30BoundaryDisplays.'
A='MainTheory.Orbit30TwoPointDisplays.'
K='MainTheory.Orbit30MomentRank.Orbit30.'
GROUPS=[
 (['eq:q4o30fiberparam','eq:q4o30complement'],[P+'actual_fibers',P+'bottom',P+'top',P+'complementIndex'],
  'The enumerated physical native fiber words give the displayed sixteen bottom strings and exactly their complements; the top index is explicitly reversed.'),
 (['eq:q4o30K5labels','eq:q4o30probnotation','eq:q4o30ampnotation'],
  [L+n for n in ('vertexIndex','edgeIndex','endpoints','pointMass','edgeMass','degreeMass')]+
  [R+n for n in ('pointC','edgeC','pointV','edgeV','edgeIndexMatrix')]+[G+'edge_symmetric'],
  'The five vertices and ten symmetric edges are the literal SI native coordinates, including the zero diagonal, physical top complements and probabilities as actual squared amplitude norms.'),
 (['eq:q4o30momentnormal'],[P+'complete_normal',P+'physical_normal',P+'literal_coordinate_sum',
  P+'literal_total_sum',K+'actual_matrix',K+'rank_exact',K+'real_witness',K+'full_diagonal_polytope_dimension'],
  'Both directions of the complete real moment form are proved. The actual 23 by 32 physical matrix has rank 23 and a strictly positive feasible witness, so its full nonnegative polytope has affine dimension nine. This is independent of the no-code theorem.'),
 (['eq:q4o30starindicator'],[L+'literal_pointwise_identities',L+'actual_probabilities',P+'physical_normal'],
  'All three labeled lines in this align environment are pointwise identities on the actual sixteen fiber words, with their exact rational coefficients and physical coordinate order.'),
 (['eq:q4o30degreeprob','equation@11536','eq:q4o30RW'],[L+'physical_probabilities',L+'literal_degree_sum',
  G+'degree_norm',G+'physicalData'],
  'The star probability, five weighted degrees, total point mass three eighths and total edge mass one half follow from physical supported normalized amplitudes and full weight-at-most-two KL.'),
 (['eq:q4o30rho','eq:q4o30z'],[F+'phase',F+'actual_equal_norms',F+'actual_unit_phase',F+'reciprocal_product'],
  'The conjugate amplitude denominator and complement index agree with the printed phase ratio. Unit modulus is asserted only at nonzero amplitudes; the reciprocal product identity retains its precise nonzero denominator hypothesis.'),
 (['eq:q4o30mu','eq:q4o30stars','eq:q4o30weightonediff','eq:q4o30matchpairs','eq:q4o30starsign'],
  [R+'physical_native_rows',R+'canonical_rows',R+'physical_rows',R+'starSum',R+'matchingSum'],
  'All thirty-five literal native Pauli rows are derived from actual full KL, then converted into the five reciprocal differences, five point/star pairs, five weight-one stars and five perfect-matching sums. The first starsign align entry includes the matching-sum line; no support or final impossibility assumption is used.'),
 (['eq:q4o30A','lem:q4o30threepoints'],[G+'physicalData',G+'actual_three_active',A+'internal_edge_zero',
  A+'two_term_row','MainTheory.Orbit30.Data.card_A_ne_zero','MainTheory.Orbit30.Data.card_A_ne_one'],
  'The abstract support-graph data are now instantiated from actual code amplitudes with every defining hypothesis proved; all small-active-set exclusions are applied through that physical bridge.'),
 (['eq:q4o30twopointmag','equation@11660','equation@11669'],[G+'physicalData']+
  [A+n for n in ('internal_edge_zero','two_term_row','two_point_magnitude','degree_magnitude',
    'equal_point_mass','point_and_degree_values','disjoint_star_bound')],
  'The conditional two-point branch derives the literal magnitude identity for every vertex including zero edges, sums it to the quadratic degree equality, proves equal masses three sixteenths and degrees five sixteenths, and derives the disjoint-star bound by nonnegative matrix partitioning. No previously proved no-code theorem supplies an intermediate assertion.'),
 (['align@11691','eq:q4o30WAA'],[G+'physicalData']+
  [B+n for n in ('innerWeight','crossWeight','inactiveWeight','exceptional_mass_equations')],
  'The two displayed exceptional-branch mass equations use unordered internal edge mass, correctly half the symmetric double sum. The isolated inactive pair contributes exactly one edge weight, and subtracting yields the printed one-quarter difference.'),
 (['lem:q4o30exceptional','eq:q4o30triangle1','eq:q4o30regular'],[G+'physicalData',G+'actual_four_active',
  H+'actual_regular_points','MainTheory.Orbit30.Data.q4o30_exceptional',
  'MainTheory.Orbit30.Data.row_over_A','MainTheory.Orbit30.triangle_contradiction'],
  'The physical graph supplies the restricted bilinear rows and actual nonzero point/edge factors. The three-active-point triangle exclusion proves the exceptional branch impossible and implies regularity; all three triangle lines in the align environment are included.'),
 (['eq:q4o30globalsync','eq:q4o30Hi'],[F+'actual_point_phase',H+'actual_all_edge_phases',
  H+'actual_edge_reconstruction',H+'actual_matching_factor',H+'actual_hafnians'],
  'All active physical point and edge ratios equal minus the star ratio. The exact physical matching sum is twice that nonzero common factor times the conjugated all-plus hafnian, proving each printed matching equation including zero-edge boundaries.'),
 (['lem:q4o30mindegree','equation@11748'],[G+'physicalData',M+'actual_minimum_degree',
  M+'actual_complement_degree',B+'unique_neighbor_weight'],
  'The actual support graph has minimum degree two. The displayed hypothetical unique-neighbor weight equals the complete weighted degree and is strictly greater than one eighth when the point is active.'),
 (['eq:q4o30tencomplements'],[M+'actual_admissible',C+'literal_representatives',C+'exhaustive_relabeling',
  'MainTheory.Orbit30GraphTypes.admissible_count','MainTheory.Orbit30GraphTypes.distinct_isomorphism_types'],
  'All 252 nonempty maximum-degree-two masks among the 1024 possible five-vertex graphs are classified by an actual kernel-checked vertex bijection into the ten printed representatives. Degree profiles and triangle counts prove the representatives pairwise nonisomorphic, and the physical zero-amplitude mask satisfies exactly these hypotheses.'),
 (['eq:q4o30monomialtable'],[T+'monomial'+str(i) for i in range(6)]+
  [E+'relabeled_missing','MainTheory.Orbit30GraphRelabel.hafnian_relabel',
   'MainTheory.Orbit30PhysicalProperSupport.actual_proper_support_no_go'],
  'Every literal missing-edge row and the specified single surviving nonzero product are checked. A bijective relabeling carries the actual physical zero pattern and hafnians to these representative equations.'),
 (['eq:q4o30AB','eq:q4o30binomialtable'],[T+'binomial'+str(i) for i in range(4)]+
  [T+'odd_product_contradiction',E+'representative_no_go',E+'proper_no_go'],
  'All four literal odd-binomial-cycle rows, the three indicated hafnian equations, the equal nonzero products and the minus sign from three factors are proved, completing every proper graph case.'),
 (['eq:q4o30C','eq:q4o30Cb0'],[H+'edgeMatrix',G+'edge_symmetric',G+'bilinear_row',
  'MainTheory.Orbit30PhysicalFullSupport.actual_point_vector_nonzero',
  'MainTheory.Orbit30PhysicalFullSupport.actual_matrix_kernel'],
  'The actual symmetric zero-diagonal edge matrix kills the actual point vector, which is nonzero by its physical total squared norm three eighths.'),
 (['eq:q4o30scaling','eq:q4o30normalization'],[V+n for n in ('scaled_entry','scaled_determinant',
  'preserves_singularity','scaled_hafnian','preserves_hafnians','four_edge_normalization')],
  'Nonzero vertex scaling preserves singularity and multiplies each four-vertex hafnian by the product of exactly its four vertex factors. A complex square root constructs all five nonzero scales setting the four literal edges to one.'),
 (['eq:q4o30sixvars','eq:q4o30H0'],[D+'matrix','MainTheory.Orbit30FullSupport.normalized_hafnians',
  'MainTheory.Orbit30FullSupport.full_hafnian_det_ne_zero'],
  'The displayed six variables occupy the actual symmetric matrix entries; all five labeled normalized hafnian equations in the align environment are the literal matching polynomials of that matrix.'),
 (['eq:q4o30cdfg','eq:q4o30cube'],[D+'products',D+'cube',D+'parameter_nonzero'],
  'Exact polynomial combinations of the normalized hafnians give cd=fg=1 and t squared plus t plus one equals zero, with t=cg nonzero.'),
 (['eq:q4o30det','eq:q4o30detnonzero'],[D+n for n in ('determinant_polynomial','cleared_determinant',
  'displayed_determinant','numerator_reduction','determinant_minus32')]+
  ['MainTheory.Orbit30PhysicalFullSupport.actual_full_support_no_go'],
  'The actual matrix determinant is expanded and reduced by kernel-checked polynomial identities, giving the literal rational expression and exactly minus 32. Scaling and the actual nonzero kernel vector connect this computation to the full-support physical contradiction.'),
 (['thm:q4o30nogo','equation@11922','remark@11938'],
  ['MainTheory.Orbit30PhysicalProperSupport.physical_printed_no_go',
   'MainTheory.PaperSupplementaryNoGo.q4o30nogo'],
  'The complete literal SI route excludes arbitrary physically supported normalized full-KL code columns, through the small-point support argument, all ten proper complements and the full K5 determinant branch. The existing exact-code frontend identifies the supplied projective-order-four representative.'),
]
PROSE=[
 (11481,11500,[P+'complete_normal',K+'actual_matrix',K+'rank_exact',K+'full_diagonal_polytope_dimension'],
  'The rank twenty-three, equivalent physical moment normal form and actual dimension-nine nonnegative polytope are checked independently of the no-code theorem.'),
 (11513,11550,[L+'literal_pointwise_identities',L+'physical_probabilities'],
  'The symmetric K5 probability translation follows from literal pointwise coordinate identities and balanced physical marginals.'),
 (11551,11623,[F+'actual_unit_phase',F+'reciprocal_product',R+'physical_rows'],
  'All phase definitions, reciprocal rows and five matching sums are explicitly tied to supported full physical KL without a nonzero-support assumption.'),
 (11625,11673,[G+'physicalData',G+'actual_three_active',A+'two_point_magnitude',A+'point_and_degree_values',A+'disjoint_star_bound'],
  'The one- and two-point support exclusions include the printed amplitude and mass intermediate steps, with exact nonnegative boundary handling.'),
 (11675,11735,[G+'physicalData',B+'exceptional_mass_equations',G+'actual_four_active',H+'actual_all_edge_phases'],
  'The exceptional branch uses the correct unordered edge masses, physical bilinear triangle rows and nonzero phase synchronization.'),
 (11737,11764,[M+'actual_minimum_degree',B+'unique_neighbor_weight',H+'actual_matching_factor',H+'actual_hafnians'],
  'Minimum physical degree and the exact common phase factor produce all five matching equations.'),
 (11766,11834,[C+'exhaustive_relabeling','MainTheory.Orbit30GraphTypes.distinct_isomorphism_types',
  'MainTheory.Orbit30GraphRelabel.hafnian_relabel',E+'proper_no_go',
  'MainTheory.Orbit30PhysicalProperSupport.actual_proper_support_no_go'],
  'The ten pairwise distinct complement types exhaust the actual proper graph; both exclusion tables survive actual vertex relabeling and cover zero/nonzero edges exactly.'),
 (11836,11916,[V+'four_edge_normalization',V+'preserves_singularity',V+'preserves_hafnians',
  D+'determinant_minus32','MainTheory.Orbit30PhysicalFullSupport.actual_full_support_no_go'],
  'The full graph route constructs the literal normalization, verifies each matching polynomial, proves the actual determinant minus 32 and contradicts the nonzero physical kernel vector.'),
 (11918,11942,['MainTheory.Orbit30PhysicalProperSupport.physical_printed_no_go',
  'MainTheory.PaperSupplementaryNoGo.q4o30nogo'],
  'The theorem and support-case coverage remark use the complete literal physical SI proof route.'),
]
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--apply',action='store_true')
 args=parser.parse_args()
 evidence=ROOT/'artifacts/manuscript-certification-20261005/kernel-types-orbit30-completion.json'
 types=json.loads(evidence.read_text(encoding='utf8'))
 if types['sources_sha256']!=SOURCES:raise ValueError('Changed manuscript/type binding')
 required={n for row in GROUPS for n in row[1]}|{n for row in PROSE for n in row[2]}
 missing=required-{r['name'] for r in types['declarations']}
 if missing:raise ValueError('Uninspected roots: '+str(sorted(missing)))
 apply_reviews('supplementary',GROUPS,'orbit30-completion-review',args.apply,
  expected_sources=SOURCES,review_prefix='20261005 actual orbit-30 literal intermediate/type review: ',
  evidence_directory='artifacts/manuscript-certification-20261005')
 path=ROOT/'results/prose-review-20261003.json'
 record=json.loads(path.read_text(encoding='utf8'))
 paper_release.validate_review(record,'20261003',ROOT)
 lines=(ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
 rows=[{'source':'supplementary.tex','line':lo,'end_line':hi,'kind':'covered','reason':reason,
  'declarations':names,'origin':'20261005 actual orbit-30 literal/type review',
  'context_sha256_lf':hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
  for lo,hi,names,reason in PROSE]
 keys={(r['source'],r['line'],r['end_line']) for r in rows}
 record['assertions']=[r for r in record['assertions'] if
  (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]+rows
 record['status']='partial'
 paper_release.validate_review(record,'20261003',ROOT)
 if args.apply:
  path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
  (evidence.parent/'orbit30-completion-type-binding.json').write_text(json.dumps({
   'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
   'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),'prose_blocks':rows,
   'scope':'All literal orbit-30 formulas reviewed against their physical kernel proof route; other manuscript correspondence remains incomplete.'
  },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
 print('Explicit prose blocks:',len(record['assertions']),'status:',record['status'])
if __name__=='__main__':main()
