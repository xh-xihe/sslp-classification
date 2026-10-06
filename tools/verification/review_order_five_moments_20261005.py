"""Review actual order-five moment consequences in the current SI indexing."""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
P = 'MainTheory.OrderFivePrintedMoments.'
GROUPS = [
    (['eq:o35momentcore'],
     [P+'Orbit35.physical_consequences']+[P+'Orbit35.consequence'+str(k) for k in range(4)],
     'The four literal relations hold for the squared magnitudes of the actual '
     'supported, normalized complex codewords under physical distance-three KL. '
     'The paper lexicographic bottom indices 5,7,8 and top indices 10,11,12 '
     'agree with native y5,y7,y8 and z10,z11,z12. Exact rational combinations '
     'use only the two normalizations and diagonal degree-two moment rows. '
     'No Walsh exclusion or final no-code theorem is used.'),
    (['eq:o37momentnormal'],
     [P+'Orbit37.A',P+'Orbit37.B',P+'Orbit37.printed_labels',
      P+'Orbit37.physical_display',P+'Orbit37.physical_consequences',P+'Orbit37.reconstruct'],
     'The printed star probability is 1/10, each actual three-column grid row '
     'sums to 1/5, and each A probability equals its grid column sum minus 1/10. '
     'The paper A order is native y2,y1,y0, while the B grid keeps y3 through '
     'y11 in row order; all literal strings and the star are kernel checked. '
     'The actual physical theorem is derived from KL moments. The rational '
     'multiplier proofs also give complementary equality and total A mass 3/10; '
     'reconstruct proves sufficiency for the complete real MomentSystem under '
     'the explicitly retained nonnegativity and complementary equalities.'),
    (['eq:o38momentnormal'],
     [P+'Orbit38.A',P+'Orbit38.B',P+'Orbit38.printed_labels',
      P+'Orbit38.physical_display',P+'Orbit38.physical_consequences',P+'Orbit38.reconstruct'],
     'Both directions of the complete diagonal moment normal form are now '
     'explicit. Actual normalized supported complex codewords under KL have '
     'star mass 1/5, grid row masses 3/10, A probabilities equal to column '
     'mass minus 1/10, and complementary equality. The printed A order is '
     'native y3,y2,y1,y0; all B and star strings are kernel checked. Conversely '
     'these real relations together with nonnegative probabilities rebuild '
     'every normalization, first moment and second moment field. This '
     'completeness concerns diagonal moments and does not assert full KL '
     'sufficiency or an exact-code construction.'),
    (['eq:o38columnpositive'],
     [P+'Orbit38.B',P+'Orbit38.printed_labels',P+'Orbit38.column_positive',
      P+'Orbit38.physical_column_positive'],
     'Every printed grid column of actual supported normalized physical '
     'codewords has mass at least 1/10 and strictly greater than zero. This '
     'follows from the exact column relation and nonnegativity of the actual '
     'A squared magnitude, and includes all zero-amplitude boundary supports. '
     'No individual grid amplitude is assumed positive.'),
]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args = parser.parse_args()
    evidence = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-order-five-moments.json'
    data = json.loads(evidence.read_text(encoding='utf8'))
    if data['sources_sha256'] != SOURCES:
        raise ValueError('Inspected types have a different manuscript binding')
    missing = {n for g in GROUPS for n in g[1]}-{r['name'] for r in data['declarations']}
    if missing:
        raise ValueError('Uninspected roots: '+str(missing))
    apply_reviews('supplementary',GROUPS,'order-five-moments-review',args.apply,
                  expected_sources=SOURCES,review_prefix='20261005 physical order-five moment/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (evidence.parent/'order-five-moments-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest()
        },indent=2)+'\n',encoding='utf8')
