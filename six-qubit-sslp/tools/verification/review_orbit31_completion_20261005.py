"""Explicit type/context review of the literal orbit-31 completion and orbit 32.

The empty-mask exception remains a manuscript gap. No global completeness
flag follows from this scoped review or from the final no-code theorem.
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

P='MainTheory.'
R=P+'Orbit31ResidualTriangles.'
T=P+'Generated.Orbit31PrintedSupportOrbits.'
G=P+'Generated.Orbit31DirectTriangles.'
I=P+'Orbit31RelativeInterior.'
M=P+'Orbit32PrintedMomentNormal.'
L=P+'Orbit32PrintedLocalAlgebra.'
D=P+'Orbit32PrintedMinor.'
S=P+'Orbit3PrintedSplitMatrices.'
A=P+'ArbitrarySplitPerfectCode.'
X=P+'ArbitrarySplitSixQubit.'
F=P+'StandardFiveSyndromeDisplays.'
BRANCHES=[G+f'Type{k:02d}.physical_no_go' for k in (3,4,5,6,7,8,10,11,12,13,15)]
BRANCHES += [P+'Orbit31FinalCross.Type01.no_go',P+'Orbit31FinalSameState.final_no_go',
             R+'physical_type9_no_go',R+'physical_type14_no_go',R+'physical_type16_no_go']

GROUPS=[
    (['displaymath@5907','displaymath@5913'],
     ['MainTheory.Orbit2StandardFiveQubit.generators',F+'table',F+'literal_table',
      F+'all_nonzero_unique',F+'low_weight_nonzero',F+'low_weight_anticommutes',
      F+'commuting_generators',F+'generators_commute',F+'logical_X',F+'logical_anticommute'],
     'The literal four standard generators and all fifteen table entries are '
     'checked in their printed order. The syndrome set is exactly the fifteen '
     'nonzero four-bit words, without duplication. Every nonidentity Pauli '
     'of weight at most two has an actual anticommuting generator. Logical '
     'X and Z anticommute, and X exchanges the actual two seed words.'),
    (['q2fam:eq:split-lambda','o3gc:splittrace'],
     [A+'raw',A+'single_tail',A+'double_tail',A+'split_pair_compression',A+'split_trace',
      X+'basis',X+'operator_factor',X+'compression_transport',X+'code_isometry',
      X+'code_KL',X+'projector_KL',X+'unsplit_scalar_zero',X+'hilbert_orthonormal',
      X+'hilbert_distance_three',S+'trace_identity'],
     'An arbitrary complex four-by-two isometry applied to the actual standard '
     'five-qubit code is reindexed in the six-qubit computational basis. Every '
     'weight-at-most-two Pauli satisfies actual matrix and Hilbert KL, not '
     'merely a particular real one-parameter family. Every nonzero unsplit '
     'tail has scalar zero; split-pair scalars equal half the pullback trace '
     'and half the image-projector trace in either cyclic order.'),
    (['displaymath@5933'],[S+'a',S+'b'],
     'The two real half-angle coefficients are the printed cosine and sine.'),
    (['o3gc:split'],[S+'columns',S+'output_order',S+'isometry'],
     'The orbit-three subsection reverses the output-site order relative '
     'to W3 in Section 10. The literal columns, actual output swap and '
     'isometry are proved in this order.'),
    (['displaymath@5945'],[S+'logical',S+'projection',S+'isometry'],
     'In the orbit-three output order the logical factor is I tensor Z, '
     'and the projector is one half of I+cos(theta) Z tensor I '
     '+sin(theta) X tensor Z. Both literal matrix identities are proved.'),
    (['eq:q4o31supportwords'],[P+'Orbit31SupportBase.words',P+'Orbit31SupportBase.bottom_native',
                             P+'Orbit31SignedSupport.A',P+'Orbit31SignedSupport.B',T+'literal_words'],
     'The four words use consecutive A,B1,B2,B3 blocks and columns e0,e1,e2,e3. '
     'The table coordinates are checked against the actual six-bit words; '
     'the little-endian mask convention is an encoding of this literal order.'),
    (['equation@12030'],[P+'Orbit31PrintedMinor.printedColumns',P+'Orbit31PrintedMinor.real_cast',
                        P+'Orbit31PrintedMinor.real_determinant_abs'],
     'The exact specified seven complementary top columns, after all sixteen '
     'bottom columns, give the checked real minor of absolute determinant 128. '
     'The column list retains the native lexicographic-to-table permutation; '
     'an arbitrary rank witness is not substituted for the printed minor.'),
    (['eq:q4o31type9first'],[R+'column_rectangle',R+'type9_A_nonzero',R+'type9_B_nonzero'],
     'Actual type-nine support and vertical synchronization turn the '
     'column-(0,1) rectangle into the displayed phase-sum permanent equation.'),
    (['eq:q4o31type9opposite'],[R+'type9_opposite'],
     'The three actual row-pair permanents cannot all vanish with all B '
     'entries active, so the two nonzero synchronized phases are opposite.'),
    (['eq:q4o31type9proportional'],[R+'type9_weight_product',R+'ratio',R+'type9_proportional'],
     'The actual weight-one sums, zero inactive A entries and opposite phases '
     'give all three products a0*bi0=a1*bi1. The same nonzero ratio a1/a0 '
     'therefore works for every row.'),
    (['eq:q4o31type9second'],[R+'type9_propagated',R+'type9_permanents',R+'physical_type9_no_go'],
     'The literal (0,2) rectangle minus the common ratio times (1,2) '
     'cancels every unknown column-two phase. A proved nonzero ratio is '
     'canceled, giving the printed phase-difference permanent and contradiction.'),
    (['equation@12281'],[R+'column_rectangle',R+'column_opposition',R+'three_column_no_go',
                         R+'physical_type14_no_go',R+'physical_type16_no_go'],
     'The actual literal types fourteen and sixteen have all twelve B '
     'entries active and three active A columns. Each column pair forces '
     'opposition; three pairwise opposite nonzero phases are impossible.'),
    (['eq:q4o31oldsupport'],[P+'Orbit31HistoricalSupport.oldSupport',
                           P+'Orbit31HistoricalSupport.literal_support',
                           P+'Orbit31HistoricalSupport.physical_swap',
                           P+'Orbit31HistoricalSupport.physical_image'],
     'All twelve historical strings are checked. Swapping physical sites '
     'one and two maps the actual canonical type-two support exactly to '
     'this set; both the literal set and its physical transport are proved.'),
    (['equation@12354'],[P+'Orbit31FinalQuotients.common_quotients'],
     'The common-product equations give x_e=K/a_e on every active A column. '
     'All denominators and K are proved nonzero before division; in '
     'particular the printed e=0 and e=3 substitutions are valid.'),
    (['tab:q4o31supportorbits'],[T+n for n in ('literal_words','support_sizes','orbit_sizes',
                                             'size_sum','complete_survivor_set','unique_type')]+BRANCHES,
     'Checked every printed representative, support size, actual orbit size, '
     'disjointness and complete union of 311 masks. All sixteen literal '
     'certificate entries now have their stated derivation, including the '
     'propagated and column-phase triangles and the final same-state row.'),
    (['remark@12389'],[P+'Orbit31MomentVertices.vertex_count',P+'Orbit31MomentVertices.vertex_support_counts',
                      P+'Orbit31ExactSupportClassification.exact_support_count',
                      P+'Orbit31PhaseClassification.exact_count_chain',T+'complete_survivor_set',
                      P+'Orbit31BalancedMomentIff.feasible_iff_full_moments']+BRANCHES,
     'This finite-scope summary is supported by actual arbitrary-real moment '
     'and support semantics, 204-vertex completeness, exhaustive masks, '
     'physical cross rows, the actual quotient action and every literal '
     'branch certificate. Candidate arithmetic is checked by ordinary Lean '
     'proofs; the separate empty-mask wording issue is retained in prose review.'),
    (['eq:q4o32momentreflection'],[M+'actual_bottom_groups',M+'actual_top_groups',M+'reflected',
                                 M+'complete_normal_form',M+'physical_normal_form'],
     'All four actual middle strings and outer labels are checked against '
     'native codeword coordinates. The twelve reflected probabilities are '
     'derived from physical moments, and the printed normal form reconstructs '
     'the complete real nonnegative MomentSystem in the reverse direction.'),
    (['eq:q4o32rowsums'],[M+'rowsums',M+'physical_normal_form'],
     'Each of the three actual E,F,G rows sums to one quarter. These are '
     'literal real consequences of normalized physical diagonal KL, '
     'including all zero-amplitude boundaries.'),
    (['eq:q4o32oddweights'],[M+'actual_bottom_groups',M+'actual_top_groups',M+'oddweights',
                           M+'physical_normal_form'],
     'The complemented middle string is explicitly bound to bottom index '
     '15-e and top index 3-e. Both odd probabilities equal '
     'one eighth minus the corresponding E+F+G sum divided by three.'),
    (['equation@12476'],[D+'printedColumns',D+'actual_matrix',D+'real_determinant',D+'full_rank'],
     'The actual bit-coordinate moment matrix, in native lexicographic '
     'order, has exactly the specified seven top columns. The signed '
     'determinant is 3456, not merely its absolute value; rank is 23.'),
    (['eq:q4o32modulus'],[L+'moduli'],
     'Taking normSq of each of the three complex cross equations proves '
     'all three printed real product equalities without division or '
     'a final impossibility hypothesis.'),
    (['eq:q4o32factor1'],[L+'factors',L+'moduli',L+'positive_triple'],
     'The complete three-line align block has all three literal factors '
     'with coefficient two thirds. Squared-modulus equalities make each '
     'zero; a positive E and nonnegative F,G give positive total and '
     'equal positive probabilities for all six amplitudes.'),
    (['remark@12629'],[M+'physical_normal_form',M+'rowsums',L+'moduli',L+'factors',
                       L+'positive_triple',L+'triangle_identity','SixQubit.Orbit32.local_nogo'],
     'The actual moment row sums guarantee a positive E entry. The '
     'literal three weight-one cross equations and moment reflection '
     'then force all six local probabilities positive and the odd '
     'triangle contradiction. No probability alone is treated as full KL.'),
]

PROSE=[
    (5925,5931,'covered',[F+'all_nonzero_unique',F+'low_weight_anticommutes',
                         F+'generators_commute',F+'logical_X',F+'logical_anticommute',
                         P+'StandardFiveJointSpace.independent_generators',
                         P+'StandardFiveJointSpace.projector_checked',
                         P+'StandardFiveJointSpace.seed_gram',
                         P+'StandardFiveJointSpace.joint_range',
                         P+'StandardFiveJointSpace.joint_dimension'],
     'The literal four commuting standard generators have sixteen distinct '
     'stabilizer words. Their actual common +1 eigenspace equals the range '
     'of the actual two standard seed words, whose Gram matrix is 16 I. '
     'Its complex dimension is exactly two; the low-weight syndrome '
     'argument and both actual logical Pauli actions are separately proved.'),
    (4246,4263,'covered',[A+'split_pair_compression',A+'split_trace',
                        X+'code_isometry',X+'code_KL',X+'projector_KL',
                        X+'unsplit_scalar_zero',X+'hilbert_distance_three'],
     'The universal complex-isometry construction, full low-weight physical '
     'KL, zero unsplit scalars and both literal trace formulas are proved '
     'for the actual normalized standard five-qubit seed.'),
    (5952,5964,'covered',[X+'code_isometry',X+'code_KL',X+'projector_KL',
                        X+'unsplit_scalar_zero',X+'hilbert_distance_three',
                        A+'split_pair_compression',S+'trace_identity'],
     'All low-weight six-qubit Pauli errors are covered by the universal '
     'split-isometry proof, including the stated zero unsplit coefficients '
     'and the split-pair trace formula in this output order.'),
    (12026,12042,'covered',[P+'Orbit31PrintedMinor.real_determinant_abs',
                           'SixQubit.Orbit31.momentMatrix_rank'],
     'The specified minor and full moment rank are independently proved.'),
    (12115,12120,'covered',[P+'Orbit31SupportBase.actual_rows',P+'Orbit31MomentVertices.extreme_points',
                           P+'Orbit31MomentVertices.vertex_count',P+'Orbit31MomentVertices.vertex_support_counts'],
     'All actual real extreme points, and only those points, are the 204 '
     'checked primal vertices, with support counts 108 and 96.'),
    (12122,12123,'covered',[P+'Orbit31MomentFaces.convex_hull_supported_vertices'],
     'Every coordinate face is the convex hull of the actual supported vertices.'),
    (12124,12126,'gap',[I+'relative_interior_iff_vertexUnion',I+'empty_vertexUnion',I+'empty_mask_no_support'],
     'The stated iff needs a nonempty-mask or nonempty-face hypothesis. For '
     'the empty mask the vertex union is empty, but normalization excludes '
     'an exact empty support. The repository proves the corrected iff and '
     'this boundary obstruction; the authoritative SI source is unchanged.'),
    (12277,12290,'covered',[R+'column_rectangle',R+'column_opposition',R+'three_column_no_go']+BRANCHES,
     'Actual synchronized phases prove the literal type-14 and type-16 '
     'exclusions. Together with the other checked literal branches only '
     'type two remains at this stage.'),
    (12469,12479,'covered',[D+'actual_matrix',D+'real_determinant',D+'full_rank'],
     'The printed signed minor is checked in the actual lexicographic '
     'matrix, and proves rank twenty-three.'),
    (12513,12520,'covered',[M+'complete_normal_form',M+'parameter_injectivity',
                           D+'kernel_dimension',L+'reflection_involution'],
     'Both directions of the complete nonnegative real normal form are '
     'proved. The twelve displayed parameters determine the entire '
     'probability vector injectively, the actual moment kernel has '
     'dimension nine, and the literal reflection squares to identity.'),
]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    evidence=ROOT/'artifacts/manuscript-certification-20261005/kernel-types-orbit31-completion.json'
    types=json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Changed manuscript/type binding')
    required={n for row in GROUPS for n in row[1]}|{n for row in PROSE for n in row[3]}
    missing=required-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected roots: '+str(sorted(missing)))
    apply_reviews('supplementary',GROUPS,'orbit31-completion-review',args.apply,
        expected_sources=SOURCES,review_prefix='20261005 literal completion/current type review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    path=ROOT/'results/prose-review-20261003.json'
    record=json.loads(path.read_text(encoding='utf8'))
    paper_release.validate_review(record,'20261003',ROOT)
    lines=(ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
    rows=[{'source':'supplementary.tex','line':lo,'end_line':hi,'kind':kind,
           'reason':reason,'declarations':declarations,
           'origin':'20261005 literal completion, boundary and type review',
           'context_sha256_lf':hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
          for lo,hi,kind,declarations,reason in PROSE]
    keys={(r['source'],r['line'],r['end_line']) for r in rows}
    record['assertions']=[r for r in record['assertions']
                          if (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]+rows
    record['status']='partial'
    record['remaining']='Complete other current mathematical/prose correspondence; preserve five frozen main issues and the SI empty-mask qualification.'
    paper_release.validate_review(record,'20261003',ROOT)
    if args.apply:
        path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        (evidence.parent/'orbit31-completion-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'prose_blocks':rows,'scope':'Scoped current correspondence; full manuscript review remains incomplete'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Current explicit prose blocks:',len(record['assertions']),'status:',record['status'])

if __name__=='__main__':
    main()
