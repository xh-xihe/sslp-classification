#!/usr/bin/env python3
"""Generate review candidates across manuscript versions, never transfer certification.

The public report contains locators, hashes and existing review metadata only;
it does not redistribute the private manuscripts. Unlabelled objects receive
content-based keys; duplicate statements remain explicitly ambiguous.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import subprocess

import paper_claims as claims

ROOT = claims.ROOT


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stable_key(entry):
    name = Path(entry['source']).name
    if entry['labels']:
        return name + ':' + entry['labels'][0]
    return name + ':' + entry['kind'] + ':sha256:' + entry['statement_sha256']


def compare(old, new):
    by_label, by_hash = defaultdict(list), defaultdict(list)
    global_label, global_hash = defaultdict(list), defaultdict(list)
    for entry in old['claims']:
        for label in entry['labels']:
            by_label[(Path(entry['source']).name, label)].append(entry)
            global_label[label].append(entry)
        by_hash[(Path(entry['source']).name, entry['kind'], entry['statement_sha256'])].append(entry)
        global_hash[(entry['kind'], entry['statement_sha256'])].append(entry)
    rows, referenced = [], set()
    for entry in new['claims']:
        name = Path(entry['source']).name
        candidates = {x['id']: x for label in entry['labels']
                      for x in by_label[(name, label)]}
        if not candidates:
            candidates = {x['id']: x for label in entry['labels'] for x in global_label[label]}
        method = 'label' if candidates else 'statement_hash'
        if not candidates:
            candidates = {x['id']: x for x in
                          by_hash[(name, entry['kind'], entry['statement_sha256'])]}
        if not candidates:
            candidates = {x['id']: x for x in global_hash[(entry['kind'], entry['statement_sha256'])]}
        if not candidates:
            category = 'no_candidate'
        elif len(candidates) > 1:
            category = 'ambiguous'
        else:
            before = next(iter(candidates.values()))
            category = ('same_statement_review_required'
                        if before['statement_sha256'] == entry['statement_sha256']
                        else 'changed_statement_review_required')
        referenced.update(candidates)
        rows.append({
            'id': entry['id'], 'stable_key': stable_key(entry), 'source': entry['source'],
            'line': entry['line'], 'kind': entry['kind'], 'category': category,
            'match_method': method if candidates else None,
            'statement_sha256': entry['statement_sha256'],
            'certification_transferred': False,
            'cross_document_candidate': any(Path(x['source']).name != name for x in candidates.values()),
            'candidates': [{k: x[k] for k in
                            ('id', 'source', 'line', 'statement_sha256', 'status', 'lean_declarations')}
                           for x in candidates.values()],
        })
    return {'schema': 1, 'old_sources': old['sources'], 'new_sources': new['sources'],
            'counts': dict(sorted(Counter(x['category'] for x in rows).items())),
            'note': 'Candidates only. Identical text may have changed hypotheses, definitions or context. '
                    'Prose, errata and every semantic correspondence require fresh review.',
            'claims': rows,
            'old_claims_without_candidate': [x['id'] for x in old['claims']
                                              if x['id'] not in referenced]}


def render(report, version, previous):
    lines = [f'# Manuscript migration {previous} → {version}', '', report['note'], '',
             'No certification status has been transferred.', '', '| Category | Count |',
             '| --- | ---: |']
    lines += [f'| {key} | {value} |' for key, value in report['counts'].items()]
    lines += ['', 'Unmatched old locators are not automatically deletions; statements may have '
              'been split, combined or rewritten.', '',
              '## Named statements requiring attention', '',
              '| Locator | Category | Previous candidates |', '| --- | --- | --- |']
    for row in report['claims']:
        if row['kind'].rstrip('*') in {'theorem', 'lemma', 'proposition', 'corollary', 'conjecture', 'definition'}:
            candidates = ', '.join(x['id'] for x in row['candidates']) or '—'
            lines.append(f"| `{row['id']}` (line {row['line']}) | {row['category']} | {candidates} |")
    lines += ['', '## Scope', '', 'This is a structural inventory, not a complete prose audit or a Lean run.',
              'Stable keys use labels where available and statement hashes otherwise. Duplicate unlabelled '
              'statements need manual disambiguation; line numbers are locators only.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper-version', default='20260924')
    parser.add_argument('--previous-version', default='20260908')
    args = parser.parse_args()
    sources = claims.sources_for_version(args.paper_version)
    old_sources = claims.sources_for_version(args.previous_version)
    old = json.loads((ROOT / f'results/paper-claims-{args.previous_version}.json').read_text(encoding='utf-8'))
    claims.validate(old, sources=old_sources)
    new = claims.snapshot(sources=sources)
    report = compare(old, new)
    report['paper_version'] = args.paper_version
    report['previous_version'] = args.previous_version
    report['snapshot'] = {p: sha(ROOT / p) for p in (*sources, f'documents/{args.paper_version}/references.bib',
                                                    'lean-toolchain', 'lake-manifest.json', 'lakefile.lean')}
    git = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True, check=True)
    report['base_commit'] = git.stdout.strip()
    report['base_commit_is_not_a_complete_worktree_snapshot'] = True
    output = ROOT / f'results/paper-migration-{args.previous_version}-to-{args.paper_version}'
    output.with_suffix('.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    output.with_suffix('.md').write_text(render(report, args.paper_version, args.previous_version), encoding='utf-8')
    print(json.dumps(report['counts'], sort_keys=True))
    print('Wrote candidate report; no ledger reviews modified.')


if __name__ == '__main__':
    main()
