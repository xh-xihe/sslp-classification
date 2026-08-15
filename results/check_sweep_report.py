"""Check sweep_report.tex against the sweep data it describes.

Every table in the report is re-derived from
    ../data/thm44_verification_results.json
Run this after editing the report. Exits nonzero on any mismatch.
"""

import io
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPORT = os.path.join(HERE, 'sweep_report.tex')
DATA = os.path.join(HERE, os.pardir, 'data', 'thm44_verification_results.json')

TRUTH_COUNTS = {'CONF': 30, 'CNTR': 0, 'INAP': 9, 'LIFT': 4}

fails = []


def note(ok, msg):
    print(('  ok   ' if ok else '  FAIL ') + msg)
    if not ok:
        fails.append(msg)


def strip_comments(src):
    """Drop everything after an unescaped % on each line."""
    out = []
    for line in src.split('\n'):
        cut, esc = None, False
        for k, ch in enumerate(line):
            if ch == '\\':
                esc = not esc
                continue
            if ch == '%' and not esc:
                cut = k
                break
            esc = False
        out.append(line if cut is None else line[:cut])
    return '\n'.join(out)


rows = json.load(io.open(DATA, encoding='utf-8'))
if isinstance(rows, dict):
    rows = rows.get('results', list(rows.values()))
truth = {r['name']: [bool(g.get('passed', True)) for g in r['rungs']] for r in rows}

live = strip_comments(io.open(REPORT, encoding='utf-8').read())

print('sweep_report.tex  (%d of %d chars live)'
      % (len(live), os.path.getsize(REPORT)))
print()

# 1. the scoreboard
board = re.findall(
    r'(\d+)\s*\\vCONF\{\}.{0,12}?(\d+)\s*\\vCNTR\{\}.{0,12}?'
    r'(\d+)\s*\\vINAP\{\}.{0,12}?(\d+)\s*\\vLIFT', live, re.S)
note(bool(board), 'scoreboard present')
for b in board:
    note(tuple(int(x) for x in b) == (30, 0, 9, 4),
         'scoreboard reads %s/%s/%s/%s' % b)

# 2. captions against the tables they caption
for m in re.finditer(r'\\caption\{The \$(\d+)\$ \\v(CONF|CNTR|INAP|LIFT)\{\}', live):
    claimed, kind = int(m.group(1)), m.group(2)
    ends = [live.find(e, m.end()) for e in (r'\end{longtable}', r'\end{tabular}')]
    ends = [e for e in ends if e >= 0]
    body = live[m.end():min(ends) if ends else len(live)]
    n = len(re.findall(r'\\texttt\{', body))
    note(claimed == n == TRUTH_COUNTS[kind],
         '%s caption %d, table %d rows, truth %d' % (kind, claimed, n, TRUTH_COUNTS[kind]))

# 3. superseded numbers must not reappear in live text
for pat, why in ((r'\$29\$\s*\\vCONF', '29 CONFIRMS'),
                 (r'\$10\$\s*\\vINAP', '10 INAPPLICABLE'),
                 (r'lists the \$10\$ codes', 'prose "the $10$ codes"')):
    note(len(re.findall(pat, live)) == 0, 'no live %s' % why)

# 4. the per-rung table, cell by cell
pat = re.compile(r'\\texttt\{([^}]*)\}[^&]*&[^&]*&\s*\\v(?:CONF|CNTR|INAP|LIFT)\s*'
                 r'((?:&\s*\\r(?:OK|FAIL|NA)\s*){2,})')
listed = {}
for m in pat.finditer(live):
    name = m.group(1).replace('\\_', '_')
    listed[name] = re.findall(r'\\r(OK|FAIL|NA)', m.group(2))

missing = sorted(set(truth) - set(listed))
extra = sorted(set(listed) - set(truth))
note(not missing, 'every sweep code listed (missing: %s)' % (', '.join(missing) or 'none'))
note(not extra, 'no unknown code listed (extra: %s)' % (', '.join(extra) or 'none'))

bad = []
for name, cells in listed.items():
    if name not in truth:
        continue
    real = [(c == 'OK', e) for c, e in zip(cells, truth[name]) if c != 'NA']
    if any(g != e for g, e in real):
        bad.append(name)
note(not bad, 'per-rung cells agree with the sweep (%s)' % (', '.join(bad) or 'all match'))

# 5. first-failing-rung table and the distribution the report quotes
def first_fail(name):
    for k, ok in enumerate(truth[name]):
        if not ok:
            return k
    return None


claimed = dict((m.group(1).replace('\\_', '_'), int(m.group(2)))
               for m in re.finditer(r'\\texttt\{([^}]*)\}[^&]*&\s*rung (\d)', live))
note(len(claimed) == 8, 'first-failing-rung table lists %d codes (expect 8)' % len(claimed))
for name, r0 in sorted(claimed.items()):
    note(first_fail(name) == r0,
         '%s first fails at rung %s, table says %d' % (name, first_fail(name), r0))
dist = {}
for name in claimed:
    dist[first_fail(name)] = dist.get(first_fail(name), 0) + 1
note(dist == {1: 4, 2: 3, 3: 1},
     'first-failure distribution %s (expect 4/3/1 at rungs 1/2/3)' % sorted(dist.items()))

print()
if fails:
    print('%d check(s) failed' % len(fails))
    sys.exit(1)
print('sweep_report.tex agrees with the data in every checked respect')
sys.exit(0)
