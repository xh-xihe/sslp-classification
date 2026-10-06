"""Review actual physical anchor equations and literal parity-frame displays."""
import argparse, hashlib, json
from pathlib import Path
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT=Path(__file__).resolve().parents[2]
D=ROOT/'artifacts/manuscript-certification-20261005'
S='MainTheory.Orbit19ShellDisplays.'
N='MainTheory.Orbit26PhysicalNorms.'
A='MainTheory.Orbit26PhysicalDependentAnchors.'
U='MainTheory.Orbit26NormalizedRows.'
P='MainTheory.Orbit26NonmatchingPhysical.'
GROUPS=[
 (['eq:o19-shellcoords','eq:o19-shelltable'],[S+n for n in ('bit','w','literal_fibers')],
  'The actual six-bit orbit-19 fibers have exactly the printed shell/tail parity table, with the first-four Hamming weight and the two final bits in the SI order.'),
 (['eq:o19-shellprojectors','equation@14958'],[S+n for n in ('g0','g4','square_weight','shell_projectors')],
  'The literal quadratic shell indicators and Boolean Hamming-weight square expansion are checked on every supported six-bit word, with exact rational coefficients.'),
 (['eq:o19-u-restriction'],[S+n for n in ('u','h','u_restriction')],
  'The literal tail-mismatch polynomial equals one minus the shell indicator on the actual bottom fiber and the shell indicator on the actual top fiber.'),
 (['eq:o19-characters','eq:o19-Phi5','eq:o19-Phi5-anchor','eq:o19-Phi6'],
  [S+n for n in ('chi','sigma','sign','phi5','phi6','phi5_anchor','phi6_anchor','phi5_expansion','phi6_expansion')],
  'All character and point-indicator formulas use the printed sites and signs. The exact polynomial expansions and the four top-anchor indicators are kernel-checked on the actual top fiber.'),
 (['eq:o19-X5-anchor0','eq:o19-X6-anchor0','eq:o19-P0Q0',
   'eq:o19-anchor-equality','eq:o19-anchor-halfmass'],
  [S+n for n in ('AnchorData','anchor_data_of_rows','physical_anchor_data')],
  'Complete physical weight-at-most-two KL gives all eight individual half-angle-flip anchor monomials, equal bottom/top anchor masses, total anchor mass one half, and both zero mass products. These are extracted before the native no-go contradiction.'),
 (['lem:q4o26anchorsingular'],[N+'physical_anchor_singular'],
  'Both literal physical anchor determinants vanish, with every norm, moment, nonzero-column and coordinate-axis hypothesis of the algebraic anchor proof derived from the actual physical probabilities and KL matrices.'),
 (['eq:q4o26dependentanchors'],[A+'physical_anchor_vectors'],
  'The actual two anchor blocks are rank-one column matrices with unit-modulus phase ratios. Both first-column squared norms are exactly one eighth; no final no-code theorem supplies the decomposition.'),
 (['eq:q4o26D3rankone','eq:q4o26nonmatchanchor'],
  [A+'physical_anchor_projectors',P+'physical_normalized_data'],
  'The literal actual anchor Gram matrices equal one quarter of their unit-direction projectors. The normalized direction is the actual first column divided by square root of one eighth.'),
 (['equation@10939','equation@10961','equation@11009'],
  [U+'conjugate_row',A+'physical_rows'],
  'The row definitions are the actual Hermitian and conjugate-linear contractions of the printed block matrices. Conjugating a Hermitian row gives precisely the transposed-vector contraction with the entrywise conjugate matrix.'),
 (['eq:q4o26anchorrows'],[A+'physical_rows',A+'physical_nonmatching_rows'],
  'Both displayed phase-dependent row relations follow entry by entry from the actual physical anchor equation and the actual rank-one decompositions. Unequal phase ratios force both rows to vanish.'),
 (['equation@10983'],[N+'axis_bound',U+'row_nsq',N+'physical_column_masses'],
  'For a unit contraction vector each of the two actual column axes has total squared row norm at most three eighths, using the physical hexagon probability normal form.'),
 (['eq:q4o26nonmatchouter'],[P+'physical_nonmatching_projectors',P+'physical_normalized_data'],
  'In the nonmatching phase branch every actual nonanchor Gram matrix is one quarter of the complementary anchor-direction projector, and the two normalized anchor projectors sum to the identity.'),
 (['eq:q4o26rhoanchors'],[A+'physical_rho_anchors',P+'physical_normalized_data'],
  'The actual first-site reduced Gram sum equals one half of the sum of the two actual unit-anchor projectors, directly from the physical anchor moment equation.'),
]
for orbit in (14,15,24):
    F=f'MainTheory.Orbit{orbit}ParityFrames.'
    GROUPS.append(([f'eq:o{orbit}-parityfibers'],[F+n for n in
        ('effective','parity','literal_fibers','pack_reconstruction')],
        f'The actual orbit-{orbit} fibers are equivalent to the printed four-bit even/odd parity condition together with the fixed or repeated physical coordinate. Every supported word reconstructs uniquely from those effective coordinates.'))
    GROUPS.append(([f'eq:o{orbit}-bottomword'],[F+n for n in
        ('pack','spinor','pack_injective','bottom_coordinates','top_coordinates',
         'actual_bottom_spinor','actual_top_spinor','bottom_labels_exact','top_labels_exact')],
        f'The literal orbit-{orbit} effective-coordinate spinors reconstruct both physical state expansions in the SI order. The bottom and top labels are bijections onto the complete parity fibers, retaining the actual fixed/repetition sites.'))
    if orbit!=14:
        GROUPS.append(([f'eq:o{orbit}-frameequality'],[F+n for n in
            ('bottomFrame','topFrame','frame_data_of_rows','physical_frame_data','physical_frame_equality')],
            f'Every entry of the actual orbit-{orbit} two-by-two frame equality follows from native physical KL and moment rows before any no-go contradiction. The sums run over all eight literal parity labels.'))

T='MainTheory.Generated.Orbit31PrintedSupportOrbits.'
from review_orbit31_completion_20261005 import BRANCHES
GROUPS.append((['remark@10480'],[T+n for n in ('literal_words','complete_survivor_set','unique_type')]+BRANCHES,
    'The finite support-mask classification is exact and exhaustive, with sixteen literal symmetry types. Each type has its stated physical analytic exclusion. The computational-step qualification describes certificate generation; the accepted Lean kernel independently checks the finite coverage and every exclusion.'))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    for phase in ('frame-anchor-completion-full-build-v1','frame-anchor-completion-type-inspection-v1'):
        if json.loads((D/(phase+'-exit.json')).read_text(encoding='utf8'))['exit_code']!=0:
            raise ValueError('Canonical verification has not passed: '+phase)
    evidence=D/'kernel-types-frame-anchor-completion.json'
    types=json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256']!=SOURCES:raise ValueError('Changed manuscript/type binding')
    missing={n for _,names,_ in GROUPS for n in names}-{r['name'] for r in types['declarations']}
    if missing:raise ValueError('Uninspected roots: '+str(sorted(missing)))
    apply_reviews('supplementary',GROUPS,'frame-anchor-completion-review',args.apply,
        expected_sources=SOURCES,review_prefix='20261005 physical frame/anchor type and context review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (D/'frame-anchor-completion-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'scope':'Only listed actual physical formulas. Other SI intermediate obligations remain incomplete.'},
            ensure_ascii=False,indent=2)+'\n',encoding='utf8',newline='\n')

if __name__=='__main__':main()
