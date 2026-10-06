"""Review actual manuscript basis, spinor, scalar and matrix display routes."""
import argparse,hashlib,json
from pathlib import Path
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES
ROOT=Path(__file__).resolve().parents[2];D=ROOT/'artifacts/manuscript-certification-20261005'
def roots(module,*names):return ['MainTheory.'+module+'.'+n for n in names]
GROUPS=[
 (['eq:o5-matrixflip'],roots('Orbit5MatrixRows','actFirst','actSecond','physical_cross_matrices','physical_matrix_flips'),
  'Both single-qubit operator actions on the actual zero-angle two-qubit coefficient vectors are explicit. Each of the eight actual cross partial-trace matrices is derived entrywise from native pre-obstruction KL rows. After the stated anchor phase gauge, arbitrary operator contraction gives the printed matrix-valued flip equation on either factor.'),
 (['eq:o5-offdiagonal-system'],roots('Orbit5OffdiagonalDisplays','PartialTraceRows','physical_partial_trace_rows','schmidtMatrix','offdiagonal_rows','physical_schmidt_offdiagonal_rows'),
  'The adjoints of both actual vanishing partial traces give exactly the two displayed coefficient-matrix equations. For the explicitly stated diagonal Schmidt matrix and nonzero real scale, their four actual off-diagonal entries give the four printed scalar equations; existence of the Schmidt gauge is a separate obligation.'),
 (['eq:o5-paulibasis','eq:o5-pauli-coordinates','eq:o5-frame-trace'],roots('Orbit5PauliDisplays','scale','scale_square','pauli','tau','hsInner','tau_orthonormal','tau_traceless','coordinates','coordinate_expansion','coordinate_norm','physical_coordinate_expansions','physical_coordinates_norms','frame','frame_trace','physical_frame_trace'),
  'The three literal Pauli matrices are scaled by the inverse square root of two and proved orthonormal and traceless. Every traceless actual coefficient matrix has the displayed three-coordinate expansion with preserved squared norm. In the stated Bell branch each of the four physical coefficient norms is one sixth, and summing the actual coordinate frame gives trace two thirds.'),
 (['eq:o6-vector0'],roots('Orbit6BasisNotation','bottomWord','topWord','bottomCoefficient','topCoefficient','physical_bottom_expansion','physical_top_expansion'),
  'Both words in this align environment are exact computational-basis delta expansions of the actual supported six-qubit states. Native free-bit/anchor/edge/singleton/complement coordinate orders are checked finitely, and injectivity prevents duplicated summands.'),
 (['eq:o6-b-line','eq:o6-alignedlines'],roots('Orbit6LineCompletion','wedge_zero_scalar','anchor_nonzero_of_data','line_of_data','physical_lines'),
  'The actual bottom anchor has nonzero norm one third. Actual wedge-zero and orthogonality rows imply a one-dimensional span containing it and every actual complementary singleton, with all actual bottom edges and top singletons orthogonal to that span.'),
 (['eq:o6-edgeorthogonality'],roots('Orbit6LineCompletion','edge_orthogonality_of_data','physical_edge_orthogonality'),
  'Every actual bottom edge is orthogonal to every actual complementary singleton, hence in particular to both endpoint complements printed here. The proof uses the actual proportionality and pairing rows before the final obstruction.'),
 (['eq:o6-matrixflips'],roots('Orbit6MatrixTests','incidentTest','physical_matrix_tests'),
  'For every active physical coordinate, the actual two-by-two matrix identity contracts with any one-qubit operator. The sum uses the actual incident edge order and complementary singleton at the other endpoint, giving exactly the displayed pairing identity.'),
 (['eq:o6-flipmonomials','eq:o6-Xkrow','eq:o6-ZlXkrow','eq:o6-oneflipzero'],roots('Orbit6CharacterRows','edgeIndex','actual_edge_index','p','r','physical_monomials_zero','physical_X_rows','physical_ZX_rows'),
  'The symbols p and r are literal pairings of the actual anchor, singleton, incident edge and complementary singleton vectors, with the actual finite edge index checked. Physical alignment rows prove each pairing zero and therefore both printed signed X and ZX relations. This proves the displayed relations and their conclusion, without claiming that character inversion is the dependency route used by this declaration.'),
 (['eq:o17-degree3-pairsums','equation@15242','eq:o17-triangle-system'],roots('Orbit17GraphDisplays','H','normalized_nonneighbor_pair_sum','isolated_matching_value','normalized_universal_triangle'),
  'For the complex edge variables in the stated normalized graph, H is exactly the three-term four-vertex hafnian. Substitution of the stated zero/nonzero and unit edge labels gives the nonneighbor pair sums, isolated nonzero matching and universal-vertex triangle sums. These are literal algebraic intermediates in the manuscript graph argument, not new assumptions about physical KL.'),
 (['eq:o20-epsilon','equation@15365','eq:o20-global-lastchar','eq:o20-blockchars'],roots('Orbit20DisplayCompletion','bottomWord','matchedTopWord','blockPattern','tail','epsilon','epsilon_checked','literal_matching','block_characters_of_data','physical_characters'),
  'The actual sixteen bottom words and matched top words have the printed block parity and tail complement relation. Actual pre-obstruction diagonal rows make every block uniform; all three tail characters are balanced and hence both the global/mixed and each individual block character sums vanish.'),
 (['eq:o20-rhopairs','eq:o20-oddtriangle'],roots('Orbit20PhaseCompletion','rho','ratio_unit_of_data','ratio_pairs_of_data','physical_ratio_pairs','oddTriangle','triangle_determinant','triangle_rows','physical_triangle'),
  'In any actual positive block, uniformity makes all four bottom amplitudes nonzero and matched physical norms make every displayed phase ratio unit modulus. The twenty-four actual pair rows imply all pairwise opposite-ratio equations. Three distinct actual ratios satisfy the displayed odd triangle whose literal coefficient determinant is minus two.'),
 (['eq:o12-bottomactive','eq:o12-topactive','eq:o12-bottomword'],roots('Orbit12BasisNotation','slot','bottomWord','topWord','bottomCoefficient','topCoefficient','active_patterns','physical_bottom_expansion','physical_top_expansion'),
  'The actual native fibers are exactly the empty/full/even two-subset active patterns with the stated opposite half-angle bits. Both bottom and top words in the align block are exact supported computational-basis expansions, including their actual zero-angle spinor coefficients.'),
 (['eq:o12-two-lines'],roots('Orbit12AnchorLines','actual_anchor_lines')+roots('Orbit12LineDimensions','span_pair_scalar','actual_line_dimensions'),
  'Actual cross-block cancellation and the four positive anchor norms make both pairs of anchor spinors proportional. The spans of the exact actual pairs equal their nonzero singleton spans and each has complex dimension one.'),
 (['eq:o12-anchor-scalars'],roots('Orbit12EdgeLines','physical_H1_frame','actual_edge_lines')+roots('Orbit12ScalarCompletion','ScalarData','actual_all_scalars'),
  'This align block includes all six edge scalars as well as the four anchors. The actual H=0 and independently derived H=1 positive frame identities force every edge spinor into the appropriate actual anchor line. Scaling each actual zero anchor by two gives unit directions and simultaneous scalar parameters for every displayed vector.'),
 (['eq:o12-anchor-cancellation'],roots('Orbit12ScalarCompletion','ScalarData','norm_one_coordinate','scalar_cancellation','actual_anchor_cancellation'),
  'With the actual simultaneous unit-direction parameterization, an entry of the actual AH cross-block equation at nonzero coordinates gives exactly beta0 times conjugate alpha0 plus beta4 times conjugate alpha4 equal to zero.'),
 (['eq:o12-pair-e','eq:o12-pair-ebar','eq:o12-scalar1','eq:o12-anchor-equality2'],roots('Orbit12PairCompletion','complementEdge','actual_complement_edges','actual_pair_rows','actual_scalar_rows','actual_eliminated_anchor_equality')+roots('Orbit12ScalarCompletion','pair_scalar_rows','eliminated_anchor_equality'),
  'All six actual edges and their complements are checked. Each printed two-incidence pairing follows from the sum or difference of two actual native weight-two KL rows. The full actual normalized scalar parameterization gives both equations in the scalar align block. Positive chosen edge mass makes its scalar nonzero, and direct elimination gives the displayed anchor-product equality before the final contradiction.'),
 (['eq:o13-X6errors','equation@15713'],roots('Orbit13DisplayCompletion','errors','error_weights','physical_error_rows','physical_trace_test'),
  'The eight literal X6/Y6 and dressed ZjX6/ZjY6 errors have physical weight at most two and their actual KL rows vanish. Actual block frame equality contracts with every two-by-two matrix to give the printed arbitrary-operator trace relation.'),
]

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--apply',action='store_true');args=parser.parse_args()
 for phase in ['display-route-completion-full-build-v1','display-route-completion-type-inspection-v1']:
  if json.loads((D/(phase+'-exit.json')).read_text(encoding='utf8'))['exit_code']!=0:raise ValueError('Not passed: '+phase)
 p=D/'kernel-types-display-route-completion-v1.json';types=json.loads(p.read_text(encoding='utf8'))
 if types['sources_sha256']!=SOURCES:raise ValueError('Changed manuscript binding')
 required={n for _,rs,_ in GROUPS for n in rs};missing=required-{r['name'] for r in types['declarations']}
 if missing:raise ValueError('Uninspected roots: '+str(sorted(missing)))
 apply_reviews('supplementary',GROUPS,'display-route-completion-review-v1',args.apply,
  expected_sources=SOURCES,review_prefix='20261005 actual display-route type/context review: ',
  evidence_directory='artifacts/manuscript-certification-20261005')
 if args.apply:
  (D/'display-route-completion-type-binding-v1.json').write_text(json.dumps({
   'sources_sha256':SOURCES,'type_evidence':p.relative_to(ROOT).as_posix(),
   'type_evidence_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
   'scope':'Only listed actual basis/spinor/scalar/matrix displays; other obligations and frozen main issues remain.'},indent=2)+'\n',encoding='utf8',newline='\n')
if __name__=='__main__':main()
