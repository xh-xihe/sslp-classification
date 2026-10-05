#!/usr/bin/env python3
"""Read-only claim/context dossiers for a new manuscript correspondence review.

Historical records are candidates, not carried coverage. The output deliberately
does not modify a ledger or certify a mathematical statement.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def dossier(version, source, offset, limit):
    current = json.loads((ROOT / f'results/paper-claims-{version}.json').read_text(encoding='utf8'))
    history = []
    for date in ('20260908', '20260924', '20260929'):
        data = json.loads((ROOT / f'results/paper-claims-{date}.json').read_text(encoding='utf8'))
        history.extend((date, entry) for entry in data['claims'])
    lines = (ROOT / f'documents/{version}/{source}.tex').read_text(encoding='utf8').splitlines()
    entries = [c for c in current['claims'] if Path(c['source']).stem == source]
    output = []
    for entry in entries[offset:offset + limit]:
        same = [(d, e) for d, e in history if e['id'].split(':', 1)[0] == source + '.tex'
                and e['statement_sha256'] == entry['statement_sha256']]
        labelled = [(d, e) for d, e in history if entry['labels']
                    and set(entry['labels']) & set(e['labels'])]
        candidates = same if same else labelled
        reviewed = [(d, e) for d, e in candidates if e['status'] != 'unreviewed']
        if reviewed:
            candidates = reviewed
        output.append({'claim': entry, 'statement': '\n'.join(lines[entry['line'] - 1:entry['end_line']]),
                       'context_before': '\n'.join(lines[max(0, entry['line'] - 9):entry['line'] - 1]),
                       'context_after': '\n'.join(lines[entry['end_line']:entry['end_line'] + 6]),
                       'same_statement_bytes': bool(same),
                       'historical_candidates': [{'version': d, **e} for d, e in candidates]})
    return {'paper_version': version, 'sources': current['sources'], 'source': source,
            'total': len(entries), 'offset': offset, 'claims': output}


if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf8')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper-version', default='20261003')
    parser.add_argument('--source', choices=('main', 'supplementary'), required=True)
    parser.add_argument('--offset', type=int, default=0)
    parser.add_argument('--limit', type=int, default=20)
    parser.add_argument('--compact', action='store_true',
                        help='Print current statements and candidate declaration names without historical prose.')
    args = parser.parse_args()
    data = dossier(args.paper_version, args.source, args.offset, args.limit)
    if args.compact:
        for item in data['claims']:
            print(item['claim']['id'], 'lines', item['claim']['line'], item['claim']['end_line'])
            print(item['context_before'])
            print(item['statement'])
            print(item['context_after'])
            for candidate in item['historical_candidates']:
                print('Candidate', candidate['version'], candidate['status'],
                      ', '.join(candidate['lean_declarations']))
            print()
    else:
        print(json.dumps(data, ensure_ascii=False, indent=2))
