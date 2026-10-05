#!/usr/bin/env python3
"""Inventory assertions in the authoritative manuscripts, without guessing coverage.

This is a review ledger, not a proof checker. Coverage requires an explicit
statement review, named kernel declarations, the independent axiom gate, and
the full source build. Unlabelled prose requires a separate human/agent review.
Changing either manuscript invalidates semantic reviews for the release,
including unchanged statements whose definitions or context may have changed.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
SOURCES = ('documents/20260908/main.tex', 'documents/20260908/supplementary.tex')
LEDGER = ROOT / 'results/paper-claims-20260908.json'
KINDS = {'theorem', 'lemma', 'proposition', 'corollary', 'definition', 'example',
         'remark', 'conjecture', 'equation', 'align', 'gather', 'multline',
         'eqnarray', 'table', 'longtable', 'displaymath'}
TOKENS = re.compile(r'\\(begin|end)\{([^}]+)\}|(?<!\\)\\(\[|\])')
LABEL = re.compile(r'\\label\{([^}]+)\}')
STATUSES = {'unreviewed', 'partial', 'covered', 'conjecture', 'expository'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def uncomment(source):
    # Preserve offsets and line numbers. An odd preceding backslash escapes %.
    chars = list(source)
    for i, char in enumerate(source):
        if char != '%':
            continue
        j = i - 1
        while j >= 0 and source[j] == '\\':
            j -= 1
        if (i - j - 1) % 2:
            continue
        end = source.find('\n', i)
        if end < 0:
            end = len(source)
        chars[i:end] = ' ' * (end - i)
    return ''.join(chars)


def inventory(relative, source_dir=None):
    path = Path(source_dir) / Path(relative).name if source_dir else ROOT / relative
    data = path.read_bytes()
    original = data.decode('utf-8')
    source = uncomment(original)
    stack, spans = [], []
    for match in TOKENS.finditer(source):
        operation, kind, bracket = match.groups()
        if bracket:
            operation, kind = ('begin' if bracket == '[' else 'end'), 'displaymath'
        if kind.rstrip('*') not in KINDS:
            continue
        if operation == 'begin':
            stack.append((kind, match.start()))
        else:
            if not stack or stack[-1][0] != kind:
                raise ValueError(f'{relative}: unmatched end of {kind} at {match.start()}')
            _, start = stack.pop()
            spans.append((start, match.end(), kind))
    if stack:
        raise ValueError(f'{relative}: unclosed environments: {stack}')
    spans.sort()
    labels = [(m.start(), m.group(1)) for m in LABEL.finditer(source)]
    entries = []
    for start, end, kind in spans:
        own_labels = [label for position, label in labels if start <= position < end and
                      not any(start < a <= position < b <= end for a, b, _ in spans)]
        line = original.count('\n', 0, start) + 1
        anchor = own_labels[0] if own_labels else f'{kind}@{line}'
        entries.append({
            'id': f'{Path(relative).name}:{anchor}', 'source': relative,
            'kind': kind, 'labels': own_labels, 'line': line,
            'end_line': original.count('\n', 0, end) + 1,
            'statement_sha256': digest(source[start:end].encode('utf-8')),
            'status': 'unreviewed', 'lean_declarations': [], 'review': '',
        })
    for position, label in labels:
        if any(a <= position < b for a, b, _ in spans):
            continue
        if not re.match(r'(?:eq|thm|lem|lemma|cor|prop|ex|six:eq):', label):
            continue
        line = original.count('\n', 0, position) + 1
        # A label outside a mathematical environment is not a complete parsed
        # statement. Its enclosing prose must be inspected explicitly.
        entries.append({
            'id': f'{Path(relative).name}:{label}', 'source': relative,
            'kind': 'labelled_prose', 'labels': [label], 'line': line,
            'end_line': line,
            'statement_sha256': digest(source[max(0, position-1000):position+1000].encode('utf-8')),
            'status': 'unreviewed', 'lean_declarations': [], 'review': '',
        })
    entries.sort(key=lambda item: (item['line'], -item['end_line']))
    return digest(data), entries


def sources_for_version(version):
    if not re.fullmatch(r'\d{8}', version):
        raise ValueError('paper version must be an eight-digit date')
    return tuple(f'documents/{version}/{name}.tex' for name in ('main', 'supplementary'))


def snapshot(previous=None, sources=None, source_dir=None):
    old = {entry['id']: entry for entry in (previous or {}).get('claims', [])}
    result = {'schema': 1, 'sources': {}, 'prose_review': {}, 'claims': []}
    inventories = {relative: inventory(relative, source_dir) for relative in (SOURCES if sources is None else sources)}
    # Hypotheses can change outside a theorem's span or in the other document.
    # A changed manuscript therefore invalidates the release's semantic reviews,
    # even when an individual displayed statement is byte-identical.
    same_context = (previous or {}).get('sources', {}) == {
        relative: data[0] for relative, data in inventories.items()}
    for relative, (sha, entries) in inventories.items():
        result['sources'][relative] = sha
        result['prose_review'][relative] = {'status': 'unreviewed', 'review': ''}
        if same_context:
            result['prose_review'][relative] = previous.get('prose_review', {}).get(
                relative, result['prose_review'][relative])
        for entry in entries:
            before = old.get(entry['id'])
            if (same_context and before and before['source'] == relative and
                    before['statement_sha256'] == entry['statement_sha256']):
                for key in ('status', 'lean_declarations', 'review'):
                    entry[key] = before[key]
            result['claims'].append(entry)
    ids = [entry['id'] for entry in result['claims']]
    if len(ids) != len(set(ids)):
        raise ValueError('duplicate claim identifiers; disambiguate source labels')
    return result


def validate(ledger, require_complete=False, sources=None, source_dir=None):
    current = snapshot(ledger, sources, source_dir)
    if current != ledger:
        raise ValueError('manuscript/ledger drift: run refresh and review changed assertions')
    for entry in ledger['claims']:
        status = entry['status']
        if status not in STATUSES:
            raise ValueError(f"unknown status in {entry['id']}")
        if status != 'unreviewed' and not entry['review'].strip():
            raise ValueError(f"missing statement review in {entry['id']}")
        if status == 'covered' and not entry['lean_declarations']:
            raise ValueError(f"covered assertion has no kernel declarations: {entry['id']}")
    if not require_complete:
        return
    # Completeness is reported in full rather than at the first offender.  The
    # integrity errors above are faults and stop immediately; these are a
    # remaining workload, and a gate that names one of 320 reads as though one
    # assertion were all that stands in the way.
    incomplete = [e['id'] for e in ledger['claims']
                  if e['status'] in {'unreviewed', 'partial'}]
    prose = [relative for relative, review in ledger['prose_review'].items()
             if review['status'] != 'covered' or not review['review'].strip()]
    if not incomplete and not prose:
        return
    counts = Counter(e['status'] for e in ledger['claims']
                     if e['status'] in {'unreviewed', 'partial'})
    parts = []
    if incomplete:
        parts.append('%d incomplete assertions (%s)'
                     % (len(incomplete),
                        ', '.join('%s=%d' % kv for kv in sorted(counts.items()))))
    if prose:
        parts.append('%d prose reviews not complete (%s)'
                     % (len(prose), ', '.join(Path(p).name for p in prose)))
    head = ', '.join(incomplete[:5])
    if len(incomplete) > 5:
        head += ', ...'
    raise ValueError('; '.join(parts) + (f'; first: {head}' if incomplete else ''))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('refresh', 'check', 'summary'))
    parser.add_argument('--require-complete', action='store_true')
    parser.add_argument('--paper-version', default='20260908',
                        help='explicit manuscript date; historical default remains 20260908')
    parser.add_argument('--source-dir', type=Path, help='private manuscript directory bound to the ledger hashes')
    args = parser.parse_args()
    try:
        sources = sources_for_version(args.paper_version)
        ledger_path = ROOT / f'results/paper-claims-{args.paper_version}.json'
        previous = json.loads(ledger_path.read_text(encoding='utf-8')) if ledger_path.exists() else None
        if args.command == 'refresh':
            ledger = snapshot(previous, sources, args.source_dir)
            ledger_path.parent.mkdir(parents=True, exist_ok=True)
            ledger_path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
        else:
            if previous is None:
                raise ValueError('missing ledger; run refresh')
            ledger = previous
        validate(ledger, args.require_complete, sources, args.source_dir)
        print('Paper version: ' + args.paper_version)
        counts = Counter(entry['status'] for entry in ledger['claims'])
        print(f"Paper assertion inventory: {len(ledger['claims'])}; " +
              ', '.join(f'{key}={value}' for key, value in sorted(counts.items())))
        print('Separate prose review: ' + ', '.join(
            f"{Path(key).name}={value['status']}" for key, value in ledger['prose_review'].items()))
        if not args.require_complete:
            print('Inventory check only; this is not a claim of full certification.')
        return 0
    except (OSError, ValueError, KeyError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
