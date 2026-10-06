"""Review actual split enumerators and literal orbit probability/matrix displays."""
import argparse,hashlib,json,sys
from pathlib import Path
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES
ROOT=Path(__file__).resolve().parents[2]
D=ROOT/'artifacts/manuscript-certification-20261005'
sys.path.insert(0,str(ROOT/'tools'))
P='MainTheory.Orbit26PhysicalMatrices.'
B='MainTheory.Orbit28PrintedProbabilities.'
E='MainTheory.ArbitrarySplitEnumerators.'
T='MainTheory.OrderFourTableDisplays.'
GROUPS=[
 (['q2fam:eq:L-low'],[E+'A_three',E+'macwilliams','MainTheory.Orbit2SplitEnumerators.low_enumerators',
   'MainTheory.PrimitiveW3SplitEnumerators.low_enumerators','MainTheory.Orbit2SplitEnumerators.enumerator',
   'MainTheory.PrimitiveW3SplitEnumerators.enumerator'],
  'Both literal W2 and family W3 output conventions are applied to the actual standard perfect-code split. All normalized Pauli sums, including weight three, and all seven MacWilliams coefficients are derived directly for those physical encoders.'),
 (['displaymath@5966'],['MainTheory.Orbit3SplitScalarDisplays.physical_scalar',
   'MainTheory.Orbit3SplitEnumerators.sparse_scalar'],
  'For the actual orbit-three attainment encoder, the only nonidentity traces are the printed ZI and XZ terms with cos theta and sin theta. The theorem uses the attainment subsection output convention, including its swap relative to the family W3 convention.'),
 (['displaymath@5974'],['MainTheory.Orbit3SplitEnumerators.low_enumerators',
   'MainTheory.Orbit3SplitEnumerators.enumerator',E+'A_three'],
  'Actual normalized physical weight enumerators have A1=cos squared, A2=sin squared, A3=zero and the complete printed enumerator line, proved from actual Pauli traces and exact KL.'),
 (['tab:q4status'],[T+'displayed_data',T+'exhaustive',T+'row_injective',T+'no_completion']+
   [f'MainTheory.Generated.OrbitTableSemantics{o}.lp_affine_dimension' for o in (25,26,27,28,29,30,31,32,62,63)],
  'All ten row numbers, q values, representatives, order-four status and displayed dimensions match the finite orbit table. Each dimension root concerns the full nonnegative physical moment polytope, including forced-zero coordinates. The final physical no-completion results supply the status column; individual analytic intermediate equations remain separately reviewed.'),
 (['eq:q4alltenorbits'],[T+'exhaustive',T+'row_injective',T+'no_completion',T+'lift'],
  'The actual finite orbit keys of projective order four are exactly the ten listed distinct rows. The bounded physical lift leaves only denominators four and eight, and every listed key has a physical no-completion theorem.'),
 (['equation@12699'],[T+'displayed_data'],
  'The ninth zero-based row is exactly the printed orbit-63 q=8, m=4 representative (1,1,2,4,5,5), with the numeric display tied to the finite orbit key.'),
 (['eq:q4o26groupmatrices','eq:q4o26matrixmoment','eq:q4o26rho','eq:q4o26anchormatrix',
   'eq:q4o26outermatrix'],[P+n for n in ('C','D','groupIndex','physical_moment','physical_rho','physical_anchor','physical_outer')],
  'The actual supported six-qubit amplitudes form the literal printed 2 by 2 block matrices in the SI group order. All sixteen moment entries, twelve anchor entries and twelve outer-flip entries are derived from actual weight-at-most-two KL. No final no-code theorem or unproved matrix equation supplies any of these roots.'),
 (['align@11247','equation@11252','equation@11258'],[B+n for n in ('bottom','top','bottomProbability',
   'topProbability','complete_normal','physical_normal','bottomActive','topActive','literal_supports','physical_supports')],
  'The complete native real moment inequalities force all thirty-two literal probabilities. The normalized full-KL physical amplitudes therefore have the exact six-point bottom and top supports, including the zeros outside both fibers. These intermediate roots do not use the orbit-28 no-code conclusion.'),
 (['equation@12415','equation@12437'],['MainTheory.Orbit32ParityNotation.literal_parities',
   'MainTheory.Orbit32ParityNotation.coordinate_identity','MainTheory.Orbit32ParityNotation.literal_fibers'],
  'The actual six-bit residue is the printed outer-bit sum plus twice the inner three-bit Hamming weight, modulo four. The literal even and odd inner sets and the eight outer-label rows are kernel-checked against both physical native fibers.'),
]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    for phase in ('split-matrix-completion-full-build-v1','split-matrix-completion-type-inspection-v1'):
        if json.loads((D/(phase+'-exit.json')).read_text(encoding='utf8'))['exit_code']!=0:
            raise ValueError('Canonical verification has not passed: '+phase)
    evidence=D/'kernel-types-split-matrix-completion.json'
    types=json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256']!=SOURCES:raise ValueError('Changed manuscript/type binding')
    required={n for _,names,_ in GROUPS for n in names}
    missing=required-{r['name'] for r in types['declarations']}
    if missing:raise ValueError('Uninspected roots: '+str(sorted(missing)))
    apply_reviews('supplementary',GROUPS,'split-matrix-completion-review',args.apply,
      expected_sources=SOURCES,review_prefix='20261005 actual split/matrix type and context review: ',
      evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (D/'split-matrix-completion-type-binding.json').write_text(json.dumps({
          'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
          'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
          'scope':'Only the explicitly listed literal physical formulas. Other SI intermediate obligations remain incomplete.'},ensure_ascii=False,indent=2)+'\n',encoding='utf8',newline='\n')
if __name__=='__main__':main()
