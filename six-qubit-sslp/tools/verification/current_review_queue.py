"""Show version-bound review obligations without changing their status."""
import argparse
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf8')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', default='supplementary')
    p.add_argument('--start', type=int, default=0)
    p.add_argument('--end', type=int, default=20000)
    p.add_argument('--limit', type=int, default=80)
    a = p.parse_args()
    ledger = json.loads((ROOT/'results/paper-claims-20261003.json').read_text(encoding='utf8'))
    claims = [c for c in ledger['claims'] if c['id'].startswith(a.source+'.tex:')]
    print('Source statuses:', dict(Counter(c['status'] for c in claims)))
    selected = [c for c in claims if a.start <= c['line'] <= a.end]
    print('Selected statuses:', dict(Counter(c['status'] for c in selected)))
    for c in [c for c in selected if c['status'] not in ('covered','expository','conjecture')][:a.limit]:
        print(c['id'], c['line'], c['status'], ', '.join(c['lean_declarations']))
