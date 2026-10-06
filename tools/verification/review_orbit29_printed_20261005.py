"""Bind the literal orbit-29 pair reduction, fifteen faces and eta argument."""
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
F='MainTheory.Orbit29PrintedFaceAudit.'
P='MainTheory.Orbit29PrintedSimplex.'
R='MainTheory.Orbit29PhysicalPairReduction.'
I='MainTheory.Orbit29SimplexRelativeInterior.'
D='MainTheory.Orbit29SimplexDimensions.'
U='MainTheory.Orbit29PhysicalRatios.'
G='MainTheory.Orbit29PhysicalPairGauge.'
E='MainTheory.Orbit29PrintedEta.'
GROUPS=[
 (['align@11295','align@11305'],[F+'bottomPairs',F+'topPairs',F+'literal_pairs',
      P+'literal_native_pairs',P+'physical_omitted_amplitudes'],
  'The literal displayed X5X6 pairs are actual native fiber words, with their printed order and partners checked by the kernel. The omitted bottom pair is proved to vanish from the actual diagonal moments.'),
 (['eq:q4o29bottomsimplex','eq:q4o29topsimplex'],[R+n for n in
      ('physical_moments','native_orth','bottom_mass','total_high_mass','high_mass_bound',
       'weighted_determinants','high_parallel','high_balanced','bottom_balanced')]+
      [P+n for n in ('omitted_zero','reduced_normal','physical_normal',
       'physical_printed_probabilities','physical_domain','physical_omitted_amplitudes')],
  'All per-string probabilities and the exact three-parameter nonnegative domain are derived from actual supported normalized physical code amplitudes, the complete native moment system, and physical Walsh orthogonality. No final impossibility theorem supplies an intermediate formula.'),
 (['equation@11337'],[F+'barycentric',F+'barycentric_domain',F+'barycentric_sum',
      F+'literal_vertex_probabilities',P+'physical_domain'],
  'The literal barycentric coordinates are nonnegative exactly on the printed parameter domain and sum to one eighth; the displayed graph probabilities are their actual subset sums.'),
 (['equation@11349','eq:q4o29graph'],[F+n for n in
      ('probabilityWords','baseEdges','bottomEdge','topEdge','flipCoordinate',
       'literal_graph_incidence','literal_pairs')]+[U+'edge_order',U+'indexed_orth',U+'physical_assignment'],
  'Every printed weight-one edge is an actual flip incidence between the specified pairs. Its signed internal-ratio equation follows from the physical Walsh rows, with the literal graph order retained.'),
 (['tab:q4o29faces'],[F+n for n in
      ('fifteen_masks','literal_counts','dimension_support','bit_overlap','vertex_positive_iff',
       'face_centers','distinct_faces','exhaustive_faces','checked_walks','anchors_active')]+
      [I+'relative_interior_iff',I+'fifteen_nonempty',I+'exhaustive_relative_interiors',
       D+'literal_face_dimensions',U+'amplitude_probabilities',U+'common_unit_phase'],
  'The fifteen rows exhaust the nonempty simplex faces. Their actual relative interiors, affine dimensions, zero vertices, vertex and edge counts, and signed paths are proved, and activity is equivalent to positive physical per-string probability.'),
 (['equation@11404'],[E+'targetPair',E+'flipQubit',E+'maskFive',E+'maskSix',
      E+'literal_target_errors',E+'actual_rows'],
  'The four target-pair/qubit assignments and the actual XjX5 and XjX6 masks are checked on the literal native words. Their four separating Walsh combinations are physical distance-three rows.'),
 (['equation@11412'],[E+'eta',E+'pinned_probability',E+'pinned_nonzero',E+'eta_unit',E+'eta_mul'],
  'The printed conjugate-amplitude quotient has a nonzero denominator, is a unit phase, and satisfies the exact cancellation identity used in the displayed equations.'),
 (['eq:q4o29etaeqs','proposition@11431'],[U+'common_unit_phase',G+'physical_pair_gauge',
      E+'aligned_bottom',E+'opposite_high',E+'actual_rows',E+'printed_eta_equations',
      E+'active_product_nonzero',E+'eta_contradiction',E+'physical_no_go'],
  'One actual local diagonal unitary removes the common phase while preserving complete physical KL. The four literal eta equations then follow from actual Walsh rows; the positive target product forces the two incompatible eta values at every boundary and interior.'),
]
PROSE=[
 (11289,11290,['MainTheory.Orbit29MomentRank.Orbit29.actual_matrix',
      'MainTheory.Orbit29MomentRank.Orbit29.rank_exact',
      'MainTheory.Orbit29MomentRank.Orbit29.kernel_dimension',
      'MainTheory.Orbit29MomentPolytope.full_actual_matrix',
      'MainTheory.Orbit29MomentPolytope.real_dual',
      'MainTheory.Orbit29MomentPolytope.forced_zero',
      'MainTheory.Orbit29MomentPolytope.full_center_feasible',
      'MainTheory.Orbit29MomentPolytope.full_center_positive',
      'MainTheory.Orbit29MomentPolytope.restricted_rank',
      'MainTheory.Orbit29MomentPolytope.full_diagonal_polytope_dimension'],
  'The full 32-coordinate nonnegative diagonal-moment polytope has actual affine dimension eight. A checked dual certificate forces the first two bottom coordinates to zero; the remaining 30 columns have rank 22 with signed minor minus 384 and a strictly positive feasible witness. The rank calculation is explicitly tied to the native physical bit strings.'),
 (11291,11334,[R+'high_parallel',R+'high_balanced',R+'bottom_balanced',
      P+'physical_printed_probabilities',P+'physical_domain',P+'physical_omitted_amplitudes'],
  'The printed pair reduction and every equal-probability assertion follow from the actual physical moment and non-diagonal constraints, including zero pairs.'),
 (11335,11393,[F+'literal_counts',F+'vertex_positive_iff',F+'checked_walks',
      I+'relative_interior_iff',I+'exhaustive_relative_interiors',D+'literal_face_dimensions'],
  'The barycentric three-simplex, all fifteen exact relative interiors and the complete literal face table are checked with actual affine dimensions and signed connectivity.'),
 (11394,11402,[U+'physical_assignment',U+'common_unit_phase',G+'diagonal_fullKL',
      G+'physical_pair_gauge'],
  'Every active internal ratio has unit modulus. Physical orthogonality gives signed graph propagation, and an actual single-qubit diagonal phase normalizes all active bottom and high-top ratios with complete KL retained.'),
 (11403,11436,[E+'literal_target_errors',E+'pinned_probability',E+'actual_rows',
      E+'printed_eta_equations',E+'active_product_nonzero',E+'eta_contradiction',E+'physical_no_go'],
  'The pinned anchor, positive high target and every one of the final printed Walsh equations are derived; the eta contradiction excludes all fifteen support strata.'),
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
    apply_reviews('supplementary',GROUPS,'orbit29-printed-review',args.apply,
        expected_sources=SOURCES,review_prefix='20261005 actual orbit-29 intermediate/type review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    path=ROOT/'results/prose-review-20261003.json'
    record=json.loads(path.read_text(encoding='utf8'))
    paper_release.validate_review(record,'20261003',ROOT)
    lines=(ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
    rows=[{'source':'supplementary.tex','line':lo,'end_line':hi,'kind':'covered','reason':reason,
       'declarations':names,'origin':'20261005 actual orbit-29 intermediate/type review',
       'context_sha256_lf':hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
       for lo,hi,names,reason in PROSE]
    keys={(r['source'],r['line'],r['end_line']) for r in rows}
    record['assertions']=[r for r in record['assertions'] if
        (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]+rows
    record['status']='partial'
    paper_release.validate_review(record,'20261003',ROOT)
    if args.apply:
        path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        (evidence.parent/'orbit29-printed-type-binding.json').write_text(json.dumps({
          'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
          'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),'prose_blocks':rows,
          'scope':'Scoped physical pair and literal fifteen-face correspondence; other manuscript review remains incomplete'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Explicit prose blocks:',len(record['assertions']),'status:',record['status'])
if __name__=='__main__':main()
