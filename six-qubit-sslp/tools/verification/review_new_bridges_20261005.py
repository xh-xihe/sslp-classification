#!/usr/bin/env python3
"""Explicit review of literal current-SI formulas and new physical bridges."""
import argparse
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
C='MainTheory.PrimitiveOrderTwoCatCompression.'
A='MainTheory.PrimitiveOrderTwoCatAlgebra.'
E='MainTheory.PrimitiveOrderTwoCatEncoder.'
W='MainTheory.Orbit3PrintedAmplitudes.'
R='MainTheory.Orbit3PrintedParityRelations.'
S='MainTheory.Orbit3PrintedScalarConsequences.'
GROUPS = [
    (['q2fam:eq:L'],['MainTheory.WImages.FI','MainTheory.WImages.FII'],
     'Compared all seven entries in both L and M definitions, including '
     'the signs of the weight-four/five entries. These are the literal '
     'normalized enumerator functions used by the actual image theorems.'),
    (['displaymath@192'],['MainTheory.BinaryMaskConvention.num_as_sum'],
     'The first printed coordinate is the least significant bit. The actual '
     'six-bit integer encoding equals the sum of bit i times 2^i; Lean indexes '
     'start at zero whereas the displayed mathematical indices start at one.'),
    (['q2fam:eq:cats'],[C+'cats',C+'orthonormal'],
     'These are the literal normalized unit-string/complement cats. The '
     'normalization factor is exactly inverse sqrt two and the actual physical '
     '32-by-5 matrix is an isometry.'),
    (['q2fam:eq:gamma'],[A+'gamma',A+'delta',A+'e',A+'two_h'],
     'Compared all five entries of gamma, delta and e. The retained real '
     'factor h=1/sqrt(2) satisfies 2*h=sqrt(2), including the printed '
     '-i*sqrt(2)*a coefficient and both signs in the first two entries.'),
    (['q2fam:eq:spinors'],[A+'x',A+'y'],
     'The first-qubit spinors are the two literal gamma/delta vectors, with '
     'complex conjugation and the minus sign in y retained.'),
    (['q2fam:eq:cat-code'],[E+'encoder_apply',E+'encoder_isometry'],
     'The actual six-qubit product-basis encoder has each displayed column '
     'equal to the sum of its spinor tensor the normalized cat. For arbitrary '
     'real a,b satisfying 2*a^2+b^2=1/4, its two columns are orthonormal. '
     'This row does not certify the subsequent full-KL or enumerator prose.'),
    (['q2fam:eq:bilinear-identities'],
     [A+'gamma_norm',A+'delta_norm',A+'hermitian_orthogonal',A+'bilinear',A+'real_gram'],
     'Checked the complete gather block: both norms, Hermitian orthogonality, '
     'all three bilinear zero identities and every entry of the real Gram '
     'matrix. The same real quadratic parameter premise supplies every identity.'),
    (['q2fam:eq:cat-ZZ'],[C+'single_zero',C+'ZZ',C+'XX_YY',C+'mixed_zero',E+'encoder_compression'],
     'Both align rows are compressions of the actual five-qubit tensor-Pauli '
     'matrices through the normalized physical cat isometry. All mixed '
     'two-site types and nonidentity single-site types vanish. The explicit '
     'six-qubit encoder compression connects these matrices to the code columns.'),
    (['q2fam:eq:tail-KL-symmetry'],[A+'gram_swap',A+'cross_formula',A+'cross_antisymmetric'],
     'Verified the swapped Hermitian Gram and the literal conjugated '
     'gamma-delta determinant, including its antisymmetry.'),
    (['displaymath@4400'],[A+'tail_symmetric'],
     'Both sums are proved for any real symmetric 5-by-5 matrix, without '
     'positivity, divisions, or nonzero coefficients. This algebraic row '
     'has the displayed H premise and is independent of a full-KL conclusion.'),
    (['q2fam:eq:first-KL'],[A+'first_KL'],
     'All three 2-by-2 outer-product sums are literal coefficient identities '
     'under the printed real parameter premise; both diagonal sums are '
     'one-half identity and the cross sum is zero.'),
    (['q2fam:eq:cat-path'],[A+'pathA',A+'pathB',A+'path_norm'],
     'The two displayed nonnegative square-root functions satisfy the '
     'quadratic normalization for every r in the closed unit interval.'),
    (['q2fam:eq:cat-t'],[A+'path_parameter',A+'path_surjective'],
     'The literal quartic coefficient expression on the printed path is '
     '2/3+r^2/3, and every t in [2/3,1] is attained by such a parameter r. '
     'The separate claim that this quartic is the physical A2 remains under review.'),
    (['o3gc:remaining'],[S+'remaining'],
     'The actual normalized encoder category masses give the three displayed '
     'weight sums after the five zero-category consequences. Category sizes '
     'and normalization are retained; no scalar-LP array is treated as a code.'),
    (['displaymath@5516'],[S+'fifth_dual_identity',S+'fifth_dual_row_metadata'],
     'The literal -A_(0,3,0)=10*e_diag_(0,2,0)-10*e_KL_(0,2,0) '
     'is a rational row identity for an arbitrary mass array. The metadata '
     'identifies exactly these two equality rows and the target category.'),
    (['o3gc:w'],[W+'w',W+'sector',W+'reconstruct',W+'raw_norm'],
     'The printed 1/sqrt(2) superposition reconstructs both original parity '
     'columns through the actual sector projections. The positive common '
     'column norm equals the norm of this amplitude vector. The expectation '
     'r_E is an actual physical Pauli expectation.'),
    (['displaymath@5333'],[W+'raw_projector',W+'raw_orthogonal'],
     'The normalized actual frame projector has the literal outer-product '
     'kernel (u*u-dagger+v*v-dagger)/N for the supplied positive common '
     'column norm. The identity Pauli in full KL gives orthogonality of '
     'the raw columns. N is retained and no column coefficient is divided out.'),
    (['displaymath@5565'],[R+'diagonal_is_pauli',R+'commuting_difference',W+'commuting_expectation'],
     'For a commuting Pauli, the original-column diagonal difference is twice '
     'the expectation of the actual operator product D*E. The mean diagonal '
     'element is the superposition expectation. D is proved equal to the '
     'physical Z-mask operator rather than an abstract sign variable.'),
    (['displaymath@5570'],[R+'diagonal_is_pauli',R+'anticommuting_cross'],
     'For an anticommuting physical Pauli, the off-diagonal element is '
     'r_E-i*r_(iDE). The actual product phase i is retained; the result '
     'holds for arbitrary parity-supported complex columns before imposing KL.'),
]


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    types=json.loads((ROOT/'artifacts/manuscript-certification-20261005/kernel-types.json').read_text(encoding='utf8'))
    if types['sources_sha256']!=SOURCES:
        raise ValueError('Type evidence source bindings changed')
    names={row['name'] for row in types['declarations']}
    missing={name for group in GROUPS for name in group[1]}-names
    if missing:
        raise ValueError('Uninspected declaration types: '+str(missing))
    apply_reviews('supplementary',GROUPS,'new-bridges-review',args.apply,
                  expected_sources=SOURCES,review_prefix='20261005 literal formula/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
