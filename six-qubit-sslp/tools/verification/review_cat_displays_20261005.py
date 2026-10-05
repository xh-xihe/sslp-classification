"""Explicit current-SI review of physical cat KL/logicals and split matrices."""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
D = 'MainTheory.PrimitiveSplitDisplays.'
T = 'MainTheory.Orbit2TrigonometricSplit.'
E = 'MainTheory.PrimitiveOrderTwoCatEncoder.'
L = 'MainTheory.PrimitiveOrderTwoCatLogicals.'
K = 'MainTheory.PrimitiveOrderTwoCatKL.'
S = 'MainTheory.PrimitiveOrderTwoCatSpinFlip.'
GROUPS = [
    (['q2fam:eq:records'], [D+'records', D+'records_checked'],
     'Compared all four active vectors and weights 3,4,5,6. The kernel '
     'connects every vector to its actual q=m=2 paper-table row.'),
    (['q2fam:eq:W2'], [D+'W2_columns', D+'W3', D+'W3_isometry', T+'isometry'],
     'The entire two-row align includes both W2 and W3. Compared both '
     'columns in the ordered two-qubit basis 00,01,10,11, including the '
     'negative sin(theta/2) entry in W3. Both actual matrices are isometries.'),
    (['q2fam:eq:W2-identities'],
     [T+'projection', T+'logical_lift', D+'W3_projection', D+'W3_logical'],
     'The entire align includes both image-projector and intertwining '
     'identities for W2 and W3. All four equalities use the actual matrices '
     'and literal ZI/XX or IZ/ZX tensor factors, for every real theta.'),
    (['q2fam:eq:cat-code'],
     [E+'encoder_apply', E+'encoder_isometry', K+'full_KL',
      S+'projectors_orthogonal', S+'spin_trace_zero'],
     'Replaced the earlier normalization-only binding with the complete '
     'actual 64-by-2 encoder bridge. Arbitrary real a,b with 2*a^2+b^2=1/4 '
     'give an isometry, and every actual six-qubit tensor Pauli of weight '
     'at most two has scalar compression. The code projector and its actual '
     'six-Y conjugate spin flip are orthogonal. Zero coefficients are allowed. '
     'The separate A2 formula is not inferred from KL or spin flip alone.'),
    (['q2fam:eq:cat-logicals'],
     [L+'L3', L+'SX', L+'tailZ_raw', L+'tailZ_action', L+'stabilizer_action',
      L+'logical_weights'],
     'Compared the literal physical words Z1 Z5 Z6 and X2 X3 X4 X5 X6. '
     'The actual cat action has signs +,+,+,-,-; SX fixes both code columns.'),
    (['q2fam:eq:L3-action'], [L+'logical3_action', L+'logicalZ'],
     'Actual physical L3 times the encoder equals the encoder times '
     'diag(-1,+1), with the printed logical-color order. This is an '
     'operator action on both columns, not only an expectation value.'),
    (['q2fam:eq:L6'],
     [L+'L6', L+'product_phase', L+'logical6_action', L+'logical_weights'],
     'The exact physical product L3*SX is minus Z1 X2 X3 X4 Y5 Y6. '
     'Its weight is six and its action on the actual code is the same '
     'diag(-1,+1). The Gaussian multiplication phase is retained.'),
]

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    path = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-cats.json'
    types = json.loads(path.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Inspected source binding changed')
    missing = {n for group in GROUPS for n in group[1]}-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected types: '+str(missing))
    apply_reviews('supplementary', GROUPS, 'cat-displays-review', args.apply,
                  expected_sources=SOURCES, review_prefix='20261005 physical matrix/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        binding = {'sources_sha256': SOURCES, 'type_evidence': str(path.relative_to(ROOT)),
                   'type_evidence_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        (path.parent/'cat-displays-type-binding.json').write_text(
            json.dumps(binding, indent=2)+'\n', encoding='utf8')
