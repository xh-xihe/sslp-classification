"""Orbit 29 endgame, symbolically.

Substitute the common pair phase into every weight-<=2 Knill-Laflamme equation:

    c_0 = c_1 = 0,
    c_{2m+1} = beta c_{2m}  (m = 1..6),   c_15 = eta c_14,
    d_{2n+1} = -beta d_{2n} (n = 0..7),

with |beta| = 1.  Conjugates are carried as independent symbols tied by
beta*bb = 1.  We then read off what the equations say about eta.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from relgen import setup
from scan import dot
from kl import conditions

a, q, d_, S0, S1 = setup(29)
n0, n1 = len(S0), len(S1)
be, bb, et, eb = sp.symbols('beta bbar eta ebar')
cl = [sp.Symbol('c%d' % m) for m in range(8)]
clb = [sp.Symbol('cb%d' % m) for m in range(8)]
dl = [sp.Symbol('d%d' % n) for n in range(8)]
dlb = [sp.Symbol('db%d' % n) for n in range(8)]

c, cb, dd, ddb = [0] * n0, [0] * n0, [0] * n1, [0] * n1
for m in range(8):
    c[2 * m], cb[2 * m] = cl[m], clb[m]
    r, rb = (et, eb) if m == 7 else (be, bb)
    c[2 * m + 1], cb[2 * m + 1] = r * cl[m], rb * clb[m]
GRAPH = {3, 5, 6, 7}          # top pairs carrying a live edge
for n in range(8):
    dd[2 * n], ddb[2 * n] = dl[n], dlb[n]
    if n in GRAPH:
        dd[2 * n + 1], ddb[2 * n + 1] = -be * dl[n], -bb * dlb[n]
    else:                      # no live edge: the ratio is not pinned
        dd[2 * n + 1] = sp.Symbol('e%d' % n)
        ddb[2 * n + 1] = sp.Symbol('eb%d' % n)
c[0] = c[1] = cb[0] = cb[1] = 0

red = {be * bb: 1}
def norm(e):
    e = sp.expand(e)
    for _ in range(4):
        e = sp.expand(e.subs(be * bb, 1))
    return sp.expand(e)

out = []
for e, z, off, db, dt in conditions(S0, S1):
    if not off:
        continue
    s = norm(sum((-1) ** dot(z, S1[t]) * cb[i] * dd[t] for i, t in off))
    if s != 0 and 'cb7' in str(s):
        out.append((e, z, sp.factor(s)))
print('equations touching the pinned pair: %d' % len(out))
seen = set()
for e, z, s in out:
    k = str(s) if str(s) < str(-s) else str(-s)
    if k in seen:
        continue
    seen.add(k)
    print('  [%s | %s]  %s' % (e, z, s))
