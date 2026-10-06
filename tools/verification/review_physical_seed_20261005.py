"""Explicit review of the printed standard perfect-code seed and projector."""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
GROUPS = [
    (['q2fam:eq:five-stabilizers'],
     ['MainTheory.Orbit2StandardFiveQubit.generators',
      'MainTheory.Orbit2StandardFiveQubit.fixed_generators',
      'MainTheory.StandardPerfectCodePhysical.generators_fix',
      'MainTheory.StandardPerfectCodePhysical.small_anticommuting_generator'],
     'Read all four literal XZZXI, IXZZX, XIXZZ and ZXIXZ words in the '
     'physical tensor basis. They fix both standard code columns. Every '
     'nonidentity Pauli of weight at most two has an anticommuting generator; '
     'the finite Gaussian multiplication phases retain its sign.'),
    (['q2fam:eq:five-pure'],
     ['MainTheory.StandardPerfectCodePhysical.compression',
      'MainTheory.StandardPerfectCodePhysical.isometry',
      'MainTheory.StandardPerfectCodePhysical.projector',
      'MainTheory.StandardPerfectCodePhysical.projector_idempotent',
      'MainTheory.StandardPerfectCodePhysical.pure_projector'],
     'The actual normalized 32-by-2 complex code matrix is standard/4. '
     'Its physical tensor-Pauli compression is identity only for the '
     'identity word and zero for every other word of weight at most two. '
     'The resulting actual projector is idempotent and satisfies the '
     'literal P5*E*P5=0 assertion for every weight-one/two physical Pauli.'),
]

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    path = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-orbit45-algebra.json'
    types = json.loads(path.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Inspected source binding changed')
    missing = {n for group in GROUPS for n in group[1]}-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected types: '+str(missing))
    apply_reviews('supplementary', GROUPS, 'physical-seed-review', args.apply,
                  expected_sources=SOURCES, review_prefix='20261005 physical matrix/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        binding = {'sources_sha256': SOURCES, 'type_evidence': str(path.relative_to(ROOT)),
                   'type_evidence_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        (path.parent/'physical-seed-type-binding.json').write_text(
            json.dumps(binding, indent=2)+'\n', encoding='utf8')
