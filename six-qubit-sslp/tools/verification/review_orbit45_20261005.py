#!/usr/bin/env python3
"""Fixed-source, explicit mathematical review of the current orbit-45 formulas."""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
F = 'MainTheory.Orbit45PrintedFibers.'
M = 'MainTheory.Orbit45PrintedMoments.'
W = 'MainTheory.Orbit45PrintedWalsh.'
C = 'MainTheory.Orbit45PrintedConsequences.'
A = 'MainTheory.Orbit45PrintedAttainment.'
P = 'MainTheory.Orbit45TrianglePolynomial.'
L = 'MainTheory.Orbit45PrintedAlgebra.'
GROUPS = [
    (['eq:o45-record'], [F+'record', F+'residues'],
     'Compared q=6, m=2, all six angles and the actual residue gap 3. '
     'Paper orbit number 45 is the zero-based table index 44.'),
    (['thm:o45-weightimage', 'eq:o45-A-image', 'eq:o45-B-image', 'eq:o45-full-A'],
     ['MainTheory.PaperSupplementaryImages.o45_weight_image',
      'SixQubit.Orbit45Final.fully_certified',
      'SixQubit.Orbit45Family.IsFamilyA', 'SixQubit.Orbit45Family.IsFamilyB',
      P+'interval', P+'path_domain', P+'path_parameter'],
     'The image equality is for genuine normalized full-KL encoders on both '
     'complete fibers. Both directions include boundary supports and exact '
     'attainment throughout [2/3,1]. Read all seven A and B entries and divide '
     'the raw Aco/Bco values by four. The moment-triangle parameter gives the '
     'same enumerator interval, including its endpoints.'),
    (['eq:o45-bottom-fiber', 'eq:o45-top-fiber', 'eq:o45-half-angle-matching'],
     [F+'bottom', F+'top', F+'bit_transport', F+'full_fibers', F+'matching',
      F+'bottom_injective', F+'top_injective'],
     'Read all twenty printed six-bit strings in left-to-right physical '
     'qubit order. The explicit transport identifies this order with the '
     'library amplitudes, proves both complete fibers and matches them by '
     'flipping physical qubit four.'),
    (['eq:o45-probabilities', 'eq:o45-z-definition'], [L+'probability', L+'cross'],
     'These are literal squared-modulus probabilities and conjugated matched '
     'cross monomials. Definitions and all subsequent algebra retain complex '
     'amplitudes rather than treating the probabilities as an encoder.'),
    (['eq:o45-moment-normal-form', 'eq:o45-sigma-definition'],
     [M+'pattern', M+'probabilities', M+'bounds', M+'actual_rows',
      M+'kernel_iff', M+'rank_seventeen', M+'minor_determinant'],
     'The actual 23-by-20 moment matrix has exactly the printed affine '
     'probability pattern, including sigma=1/4-beta-gamma in entries 2 and 7 '
     'and all ten matched top entries. Its kernel has dimension three, rank '
     '17 and the specified minor determinant -108. Nonnegative boundary '
     'probabilities are included.'),
    (['eq:o45-half-angle-rows', 'displaymath@6601', 'eq:o45-Walsh-kernel'],
     [W+'masks', W+'actual_rows', W+'pattern', W+'kernel_iff',
      W+'selectedRows', W+'selectedCols', W+'rank_seven',
      W+'minor_absolute_determinant'],
     'Compared the twelve characters, their literal restrictions, the seven '
     'selected rows, columns 0,1,2,3,4,5,7 and the absolute determinant 256. '
     'The complex kernel is exactly the displayed three-parameter ten-vector '
     'with all four A signs and both copies of -B-C retained. This review '
     'does not replace the separate physical cross-equation derivation.'),
    (['eq:o45-z-magnitudes'], [L+'cross_magnitude'],
     'Equal matched squared moduli imply |conj(c)*d|=|c|^2, including c=0. '
     'The square-root expression is the same nonnegative product magnitude.'),
    (['equation@6635', 'eq:o45-alpha-fixed'], [W+'kernel_iff', C+'fixed_mass'],
     'The third and fourth zero-based matched entries have opposite cross '
     'monomials but magnitudes alpha and 1/4-alpha, so alpha and |A| are '
     'both 1/8. No full-enumerator conclusion is assumed.'),
    (['eq:o45-triangle-magnitudes'], [W+'pattern', W+'kernel_iff', L+'cross_magnitude'],
     'Entries 1,0,2 give |B|=beta, |C|=gamma and |B+C|=sigma from '
     'the matched probabilities. The signs have no effect on magnitude.'),
    (['eq:o45-triangle-domain'], [C+'triangle_bounds', P+'Domain'],
     'The norm triangle inequalities in both directions and beta+gamma+sigma '
     '=1/4 give the three upper bounds 1/8 and all three nonnegative bounds. '
     'The domain includes degenerate triangles; no positive-support premise '
     'is imposed in this assertion.'),
    (['eq:o45-triangle-phases-general', 'eq:o45-vector-triangle-general'],
     [C+'triangle_phases', C+'unitPhase_normSq', C+'unitPhase_value'],
     'The phase decomposition is proved with a total choice at zero magnitude. '
     'All three phases have normSq one, the first two reproduce B and C, '
     'and the third reproduces -(B+C). Their weighted sum is exactly zero.'),
    (['eq:o45-onebody-Z-zero'], [L+'one_body_Z'],
     'The printed ten-point probability pattern with alpha=1/8 gives zero '
     'for every actual single-coordinate Z character. This is proved before '
     'using the final full-KL enumerator theorem.'),
    (['eq:o45-A1-zero'], ['SixQubit.Orbit45Family.Aco_one_zero',
      'SixQubit.Orbit45Family.trProj_weight_one_zero'],
     'The physical weight-one trace vanishes for every Pauli, including X '
     'and Y via absent full-fiber incidences. Aco_1=0 gives normalized A1=0.'),
    (['eq:o45-reversal-relations'], [F+'complement_matching',
      L+'moment_reversal', L+'cross_reversal'],
     'Bit complementation matches bottom r to top 9-r. Both the exact '
     'probability and cross-Walsh patterns are invariant under this reversal.'),
    (['eq:o45-d-from-z'], [L+'recover'],
     'The two divisions require the displayed strictly positive probability. '
     'Complex conjugation and c*conj(c)=|c|^2 give both recovery expressions.'),
    (['eq:o45-paired-spinflip-products'], [L+'recover', L+'paired_products'],
     'Equal reversal probabilities and cross monomials give the endpoint '
     'product equality. The proof treats the zero-amplitude case explicitly '
     'and proves the displayed division only on positive probabilities.'),
    (['eq:o45-opposite-parity'], [F+'opposite_parity', F+'reverse_sign'],
     'All ten actual bottom strings have reversed partners of opposite '
     'Hamming parity, so their spin-flip signs are negatives.'),
    (['eq:o45-h'], [A+'h', A+'h_square'],
     'The literal positive factor is 1/sqrt(8) and has square 1/8.'),
    (['eq:o45-canonical-c'], [A+'canonical_bottom', A+'canonical_top',
      A+'normalized', A+'full_kl'],
     'The align inventory includes both canonical c and d vectors. Compared '
     'every square root, sign and conjugated phase in both ten-entry lists. '
     'Under the printed vector-triangle premise these are actual normalized '
     'physical states with all distance-three KL equations, including zero '
     'triangle sides.'),
    (['eq:o45-R'], [P+'R'],
     'R is exactly beta^2+gamma^2+sigma^2; no code-space conclusion is '
     'inferred from this scalar definition.'),
    (['eq:o45-triangle-identity1'], [L+'triangle_identity'],
     'The align inventory includes all three identities. Each follows from '
     'the literal complex vector-triangle equation and both unit phases. '
     'Their norm-square expansions retain the xi+eta sign and need no '
     'nonzero side length.'),
    (['eq:o45-A2-diagonal'], [L+'diagonal_sum', 'SixQubit.Orbit45A2.dressing_pure'],
     'Summing the nine nonzero diagonal coefficients gives 48R-1/2. The '
     'actual pure-Z Pauli sum has the same value with library block masses '
     '(g1,g2,g3)=4*(gamma,beta,sigma). This does not certify individual '
     'entries of the separate ZZ table.'),
    (['eq:o45-A2-off'], [L+'off_diagonal_sum'],
     'The printed three nonnegative coherence contributions sum to 1/2-16R '
     'using all three triangle identities and total mass 1/4. The '
     'calculation itself imposes no positive-support restriction.'),
    (['eq:o45-A2-final', 'eq:o45-t-from-triangle'],
     ['SixQubit.Orbit45A2.Aco_two_value',
      'SixQubit.Orbit45Universal.block_masses',
      'SixQubit.Orbit45Phase.phase_relations', F+'bit_transport',
      L+'diagonal_sum', L+'off_diagonal_sum'],
     'The physical universal Aco_2 identity gives normalized A2=32R, '
     'using g1=4*gamma, g2=4*beta and g3=4*sigma in the explicitly '
     'transported printed order. Support, actual KL and derived phase '
     'relations are retained and no amplitude is assumed nonzero.'),
    (['eq:o45-A3-final'], ['SixQubit.Orbit45Family.universal_family',
      'SixQubit.Orbit45Family.IsFamilyA'],
     'The universal physical seven-entry family gives A2=t and A3=1-t '
     'for every full-fiber code, including boundary supports.'),
    (['eq:o45-R-min', 'displaymath@7096'], [P+'lower', P+'lower_equality'],
     'The exact lower bound is 1/48 and equality holds precisely when '
     'all three masses are 1/12 under the full closed triangle domain.'),
    (['eq:o45-R-max'], [P+'upper', P+'upper_equality'],
     'The exact upper bound is 1/32. Equality holds at precisely the three '
     'permutations of (0,1/8,1/8), including every degenerate vertex.'),
    (['eq:o45-A2-range'], [P+'interval', 'SixQubit.Orbit45Final.fully_certified'],
     'The scalar triangle bounds give [2/3,1] and the actual full-KL '
     'converse and pointwise attainment prove both directions for A2.'),
    (['eq:o45-explicit-path', 'eq:o45-path-t'],
     [P+'beta', P+'gamma', P+'sigma', P+'path_domain', P+'path_parameter'],
     'Compared all three printed path functions. For every r in [0,1] '
     'they satisfy the closed triangle domain and give 2/3+r^2/3.'),
    (['displaymath@10276', 'eq:o33reflection'],
     ['MainTheory.Orbit33PrintedReflection.C',
      'MainTheory.Orbit33PrintedReflection.J',
      'MainTheory.Orbit33PrintedReflection.R',
      'MainTheory.Orbit33PrintedReflection.inverse',
      'MainTheory.Orbit33PrintedReflection.determinant',
      'MainTheory.Orbit33PrintedReflection.reflection'],
     'Compared all 36 entries of C, the diagonal J and the six masses R. '
     'Its actual rational determinant is 160, its explicit inverse is '
     'verified on both sides, and C-inverse*J*C=2R*1-transpose-I. '
     'These are unconditional matrix identities; no no-go hypothesis or '
     'inconsistent full-KL premise is used.'),
]

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    path = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-orbit45-algebra.json'
    types = json.loads(path.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('The inspected manuscript context changed')
    names = {r['name'] for r in types['declarations']}
    missing = {n for group in GROUPS for n in group[1]}-names
    if missing:
        raise ValueError('Uninspected declaration types: '+str(missing))
    apply_reviews('supplementary', GROUPS, 'orbit45-formula-review', args.apply,
                  expected_sources=SOURCES, review_prefix='20261005 actual formula/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        binding = {'sources_sha256': SOURCES, 'type_evidence': str(path.relative_to(ROOT)),
                   'type_evidence_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        (path.parent/'orbit45-type-binding.json').write_text(
            json.dumps(binding, indent=2)+'\n', encoding='utf8')
