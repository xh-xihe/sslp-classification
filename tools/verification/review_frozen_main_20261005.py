#!/usr/bin/env python3
"""Revalidate the immutable main source; retain its five author-held issues.

This is a decision about one fixed source, not a general coverage migration.
The source is byte-identical, its definitions and hypotheses are unchanged,
and the referenced declarations have been inspected in the checked environment.
"""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args = parser.parse_args()
    candidates = json.loads((ROOT/'results/correspondence-candidates-20261005.json').read_text(encoding='utf8'))
    types_path = ROOT/'artifacts/manuscript-certification-20261005/kernel-types.json'
    types = json.loads(types_path.read_text(encoding='utf8'))
    if candidates['sources_sha256'] != SOURCES or types['sources_sha256'] != SOURCES:
        raise ValueError('Current source/type bindings changed')
    if candidates['prior_sources_sha256']['documents/20261003/main.tex'] != SOURCES['documents/20261003/main.tex']:
        raise ValueError('The frozen main manuscript changed')
    declarations = {row['name'] for row in types['declarations']}
    groups = []
    for entry in candidates['candidates']:
        if not entry['current_id'].startswith('main.tex:') or entry['prior_status']=='unreviewed':
            continue
        if entry['current_statement_sha256'] != entry['prior_statement_sha256']:
            raise ValueError('A main statement changed')
        missing = set(entry['prior_lean_declarations'])-declarations
        if missing:
            raise ValueError('Uninspected main declaration types: '+str(missing))
        groups.append(([entry['current_id'].removeprefix('main.tex:')],
                       entry['prior_lean_declarations'],
                       'Frozen source is byte-identical. The fixed-basis groups, reduced '
                       'representatives, full KL frames and normalized enumerators retain '
                       'the reviewed meanings in the current SI. Referenced kernel '
                       'declaration types were checked in kernel-types.json. The five '
                       'author-held issues are excluded. Existing statement review: '+entry['prior_review'],
                       entry['prior_status']))
    if len(groups)!=204:
        raise ValueError('Expected exactly 204 unchanged reviewed main assertions')
    groups.append((['eq:quantum-Singleton'],
                   ['MainTheory.SingletonRankOneCounterexample.violates_unrestricted_singleton'],
                   'The unrestricted statement is false under the printed KL-distance '
                   'convention: the actual normalized n=3, K=1, d=3 code violates it. '
                   'The repository separately proves the K>=2 version. The author has '
                   'kept this correction on hold; this row remains partial, never covered.',
                   'partial'))
    apply_reviews('main',groups,'frozen-main-review',args.apply,expected_sources=SOURCES,
                  review_prefix='20261005 immutable-source/type revalidation: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        path=ROOT/'artifacts/manuscript-certification-20261005/frozen-main-type-binding.json'
        path.write_text(json.dumps({'sources_sha256':SOURCES,
            'kernel_types_sha256':hashlib.sha256(types_path.read_bytes()).hexdigest(),
            'scope':'204 immutable reviewed assertions plus the explicitly partial Singleton row; prose holds persist.'},indent=2)+'\n',encoding='utf8')


if __name__=='__main__':
    main()
