"""Regenerate results/orbit-table.tsv for every certified orbit.

The angle vector is read out of the Lean module and validated against
`tools/manifest.json`, from which the residue `delta = q/m` is taken; the fiber cardinalities are COMPUTED from
`(q, a, d)` rather than counted from `def y`/`def z` declarations.

That last point is the fix for a real defect: several modules index their top
fiber as `SS.complement y_i` and so declare no `def z` at all, which the old
regex-counting version reported as a top fiber of size zero. Others (orbit 26)
group amplitudes into blocks and declare fewer names than states. Counting
declarations measured the transcription style, not the mathematics.

Usage:  python tools/run.py verification/mktable.py
"""
import io
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools', 'core'))
from orbit import fiber

SQ = os.path.join(REPO, 'SixQubit')
MAN = json.loads(io.open(os.path.join(REPO, 'tools', 'manifest.json'),
                         encoding='utf-8').read())
S = r'\s+'

rows = [('orbit', 'q', 'm', 'a', 'delta', '|S0|', '|S1|', 'module', 'lines',
         'theorems')]
recs, warn = [], []
for f in sorted(os.listdir(SQ)):
    if not f.endswith('.lean') or f == 'Audit.lean':
        continue
    src = io.open(os.path.join(SQ, f), encoding='utf-8').read()
    if 'theorem no_go_of_moments' not in src:
        continue
    oid = '66' if f == 'Order9.lean' else re.sub(r'[^0-9]', '', f)
    ent = MAN.get(oid)
    if ent is None:
        warn.append('%s: orbit %s absent from the manifest' % (f, oid))
        continue
    mav = re.search(r'def' + S + r'av' + S + r':' + S + r'Fin' + S + r'6' + S +
                    r'->' + S + r'ZMod' + S + r'(\d+)' + S + r':=' + S +
                    r'!\[([^\]]*)\]', src)
    if mav:
        q = int(mav.group(1))
        a = [int(x.strip()) for x in mav.group(2).split(',')]
        if q != ent['q'] or sorted(a) != sorted(ent['a']):
            warn.append('%s: av disagrees with the manifest' % f)
    else:
        q, a = ent['q'], ent['a']
        warn.append('%s: no `av`; falling back to the manifest' % f)
    d = ent['d']
    n0, n1 = len(fiber(a, q, 0)), len(fiber(a, q, d))
    if (n0, n1) != (ent['n0'], ent['n1']):
        warn.append('%s: recomputed fibers (%d,%d) != manifest (%d,%d)'
                    % (f, n0, n1, ent['n0'], ent['n1']))
    recs.append((int(oid), q, ent['m'], a, d, n0, n1, f[:-5],
                 src.count(chr(10)), len(re.findall(r'^theorem ', src, re.M))))

for oid, q, m, a, d, n0, n1, mod, ln, th in sorted(recs):
    rows.append((str(oid), str(q), str(m), '(' + ','.join(map(str, a)) + ')',
                 str(d), str(n0), str(n1), mod, str(ln), str(th)))

io.open(os.path.join(REPO, 'results', 'orbit-table.tsv'), 'w',
        encoding='utf-8').write('\n'.join('\t'.join(r) for r in rows) + '\n')
print('orbit-table.tsv: %d orbits' % (len(rows) - 1))
print('total lines %d, total theorems %d'
      % (sum(int(r[8]) for r in rows[1:]), sum(int(r[9]) for r in rows[1:])))
if warn:
    print()
    print('WARNINGS:')
    for w in warn:
        print('  ' + w)
    sys.exit(1)
print('every row validated against the manifest')
