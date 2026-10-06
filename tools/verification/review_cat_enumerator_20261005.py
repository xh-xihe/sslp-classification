"""Review the printed physical cat Pauli coefficients and A1/A2 formulas."""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
N = 'MainTheory.PrimitiveOrderTwoCatEnumerator.'
GROUPS = [
    (['q2fam:eq:cat-lambdas'],
     [N+'ZZ_compression',N+'XX_YY_compression',N+'coefficient_projector',
      N+'coefficient_scalar',N+'tail_pair_compression',N+'tail_pair_coefficient',
      N+'first_tail_coefficient'],
     'The three displayed scalar coefficients come from the actual '
     'six-qubit encoder compression. The coefficient is proved equal '
     'to Tr(P*E)/2 for the actual code projector. Compared the ZZ sign '
     'and the common negative XX/YY sign. All mixed tail-pair types and '
     'all first-qubit/tail pairs vanish, including zero-parameter endpoints.'),
    (['q2fam:eq:cat-A2'],
     [N+'A1',N+'A2',N+'A1_zero',N+'pairSquaredSum',N+'A2_pair_sum',
      N+'tail_pair_squared',N+'e_squared_sum',N+'pair_squared_polynomial',N+'A2_formula'],
     'Checked every equality in the displayed block. A1 sums the three '
     'first-site and fifteen tail single-site physical coefficients. '
     'A2 sums the forty-five first/tail and ninety tail/tail physical '
     'weight-two coefficients, with i<j counted once. The actual '
     'normalized projector trace coefficient supplies each term; the '
     'squared sum is the printed pair sum, then 1/2+8*sum(e_j^4), '
     'then 1/2+8*(2*a^4+b^4) under the same real normalization premise.'),
]

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    path = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-cat-enumerator.json'
    types = json.loads(path.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Inspected source binding changed')
    missing = {n for g in GROUPS for n in g[1]}-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected types: '+str(missing))
    apply_reviews('supplementary',GROUPS,'cat-enumerator-review',args.apply,
                  expected_sources=SOURCES,review_prefix='20261005 actual Pauli coefficient/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (path.parent/'cat-enumerator-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(path.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(path.read_bytes()).hexdigest()
        },indent=2)+'\n',encoding='utf8')
