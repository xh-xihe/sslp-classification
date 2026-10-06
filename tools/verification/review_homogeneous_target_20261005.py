"""Review the current SI target identity with its actual positive common norm."""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
N = 'MainTheory.Orbit3PrintedHomogeneousTarget.'
GROUPS = [
    (['o3gc:homotarget'],
     [N+'w_expectation_scale',N+'normalized_target',N+'w_normalized',
      N+'raw_expectation',N+'homogeneous_target'],
     'The target is the literal physical Pauli category (1,0,2). The '
     'printed amplitude uses (u+v)/sqrt(2), with arbitrary positive common '
     'column norm N. Its actual expectation squares satisfy N*sum(r_E^2) '
     '=N^3*A3 for the normalized actual completion. The proof uses the '
     'target trace sum and common-norm normalization; it does not assume '
     'the final A3-vanishing conclusion or any nonzero individual amplitude.'),
]

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args = parser.parse_args()
    path = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-physical-formulas.json'
    types = json.loads(path.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Inspected source binding changed')
    missing = {n for g in GROUPS for n in g[1]}-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected types: '+str(missing))
    apply_reviews('supplementary',GROUPS,'homogeneous-target-review',args.apply,
                  expected_sources=SOURCES,review_prefix='20261005 actual homogeneous target/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (path.parent/'homogeneous-target-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(path.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(path.read_bytes()).hexdigest()
        },indent=2)+'\n',encoding='utf8')
