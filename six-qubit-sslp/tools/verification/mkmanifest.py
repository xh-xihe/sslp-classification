"""Build the authoritative orbit manifest from the paper, and nothing else.

Every later check validates the Lean against THIS file, so it is parsed from
`six_qubit_sslp.tex` Table tab:66orbits and never hand-edited.

For each orbit the manifest records:
  q   physical lift order
  m   projective (logical) order
  a   the angle vector of the representative
  d   the residue, defined as q/m
  ord the additive order of d in Z_q, which MUST equal m
  n0  size of the residue-0 fiber
  n1  size of the residue-d fiber

The paper fixes delta = q/m and requires its additive order in Z_q to be
exactly m; a module using any other residue is proving a no-go for a different
projective order.  Choosing delta by fiber size alone is what produced four
wrong-order modules, because the wrong residue can give the same fiber size.
"""
import io
import json
import os
import re
import sys
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools', 'core'))
from orbit import fiber

tex = io.open(os.path.join(REPO, 'six_qubit_sslp.tex'), encoding='utf-8').read()

rows = {}
for m in re.finditer(r'^\s*(\d+)\s*&\s*(\d+)\s*&\s*(\d+)\s*&\s*\$\(([0-9,]+)\)\$'
                     r'\s*&\s*\$\((\d+),(\d+)\)\$', tex, re.M):
    oid = int(m.group(1))
    q, mm = int(m.group(2)), int(m.group(3))
    a = [int(x) for x in m.group(4).split(',')]
    n0p, n1p = int(m.group(5)), int(m.group(6))
    rows[oid] = (q, mm, a, n0p, n1p)

print('parsed %d orbit rows from the paper table' % len(rows))
missing = [k for k in range(1, 67) if k not in rows]
if missing:
    print('  WARNING: orbits absent from the parse: %s' % missing)

man, bad = {}, []
for oid in sorted(rows):
    q, mm, a, n0p, n1p = rows[oid]
    if q % mm != 0:
        bad.append('orbit %d: q=%d not divisible by m=%d' % (oid, q, mm))
        continue
    d = q // mm
    order = q // gcd(d, q)
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    entry = dict(q=q, m=mm, a=a, d=d, ord=order, n0=len(S0), n1=len(S1))
    if order != mm:
        bad.append('orbit %d: delta=%d has additive order %d, need m=%d'
                   % (oid, d, order, mm))
    if {len(S0), len(S1)} != {n0p, n1p} and (len(S0), len(S1)) != (n0p, n1p):
        bad.append('orbit %d: recomputed fibers (%d,%d) != paper (%d,%d)'
                   % (oid, len(S0), len(S1), n0p, n1p))
    man[str(oid)] = entry

out = os.path.join(REPO, 'tools', 'manifest.json')
io.open(out, 'w', encoding='utf-8').write(json.dumps(man, indent=1, sort_keys=True))
print('wrote %s with %d orbits' % (out, len(man)))
print()
if bad:
    print('INTERNAL INCONSISTENCIES (paper vs recomputation):')
    for b in bad:
        print('  ' + b)
    sys.exit(1)
print('every entry self-consistent: delta = q/m, additive order = m, '
      'fiber sizes reproduce the paper table')
