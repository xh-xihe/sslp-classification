"""Bind the literal orbit-26 rank statement to inspected kernel types."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
import paper_release

M = 'MainTheory.Orbit26PrintedMoments.'
P = 'MainTheory.Orbit26PrintedProbabilities.'
GROUPS = [
    (['eq:q4o26equalweights'],
     [P+'P', P+'Q', P+'bottom_native', P+'top_native', P+'physical_probabilities',
      M+'actual_rows', M+'affine_iff', M+'rank_fourteen'],
     'The two aggregate probability vectors of the actual supported complex '
     'codewords equal the same printed pattern under normalized physical KL. '
     'The native-to-printed block ordering is kernel checked. The separate '
     'literal rational matrix now has a complete two-parameter affine solution '
     'and a rank-fourteen proof. This replaces the earlier review sentence '
     'which correctly recorded that the rank assertion had no Lean declaration.'),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    evidence = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-moment-rank.json'
    types = json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Type evidence manuscript binding changed')
    names = {row['name'] for row in types['declarations']}
    declarations = [M+n for n in ['actual', 'rows', 'actual_rows', 'M', 'kernel_iff',
                                 'affine_iff', 'kernel_dimension', 'rank_fourteen']]
    missing = set(declarations+GROUPS[0][1])-names
    if missing:
        raise ValueError('Uninspected declarations: '+str(missing))
    apply_reviews('supplementary', GROUPS, 'moment-rank-review', args.apply,
                  expected_sources=SOURCES, review_prefix='20261005 exact moment rank/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    path = ROOT/'results/prose-review-20261003.json'
    record = json.loads(path.read_text(encoding='utf8'))
    paper_release.validate_review(record, '20261003', ROOT)
    lo, hi = 10743, 10745
    lines = (ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
    row = {'source': 'supplementary.tex', 'line': lo, 'end_line': hi, 'kind': 'covered',
           'reason': 'The literal two-normalization, five-first-moment and ten-second-moment '
                     'matrix is checked against the actual bottom/top tail-bit coordinates. '
                     'Its rational kernel is linearly equivalent to two free parameters; '
                     'rank-nullity therefore proves rank fourteen. An independent affine '
                     'equivalence proves that every rational solution, and only those '
                     'solutions, has the printed two-parameter form. Physical real '
                     'probabilities are connected separately by physical_probabilities; '
                     'they are not assumed to be rational.',
           'declarations': declarations,
           'origin': '20261005 explicit literal matrix/rank context and kernel type review',
           'context_sha256_lf': hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
    record['assertions'] = [r for r in record['assertions']
                            if (r['source'], r['line'], r.get('end_line', r['line'])) !=
                            ('supplementary.tex', lo, hi)] + [row]
    record['status'] = 'partial'
    paper_release.validate_review(record, '20261003', ROOT)
    if args.apply:
        path.write_text(json.dumps(record, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
        (evidence.parent/'moment-rank-type-binding.json').write_text(json.dumps({
            'sources_sha256': SOURCES, 'type_evidence': str(evidence.relative_to(ROOT)),
            'type_evidence_sha256': hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'reviewed_prose_blocks': [row], 'scope': 'partial current manuscript correspondence'
        }, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
    print('Total explicit current prose blocks:', len(record['assertions']))


if __name__ == '__main__':
    main()
