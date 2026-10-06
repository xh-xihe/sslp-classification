"""Orbit 29 after the support collapse.

The moment polytope forces the bottom pair (000000, 000011) to vanish, so those
two incidences drop out of every Walsh equation.  Recompute the two-term
structure on the reduced support.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from itertools import combinations

import sympy as sp

from relgen import setup
from scan import bits, xor, dot
from kl import dressings_full

a, q, d, S0, S1 = setup(29)
DEAD = {0, 1}                      # bottom indices forced to zero


def analyse(dead):
    forced, pairs = [], []
    for m in range(1, 64):
        e = bits(m)
        if e.count('1') > 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1)
               if xor(y, e) in S0 and S0.index(xor(y, e)) not in dead]
        if not inc:
            continue
        M = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc]
                       for z in dressings_full(e)])
        MT = M.T
        r = MT.rank()
        for u in range(len(inc)):
            tgt = sp.zeros(len(inc), 1)
            tgt[u] = 1
            if MT.row_join(tgt).rank() == r:
                forced.append((inc[u][0], inc[u][1], e))
        for u, v in combinations(range(len(inc)), 2):
            for sg in (1, -1):
                tgt = sp.zeros(len(inc), 1)
                tgt[u] = 1
                tgt[v] = sg
                if MT.row_join(tgt).rank() == r:
                    pairs.append((inc[u][0], inc[u][1], inc[v][0], inc[v][1], sg, e))
    return forced, pairs


dead = set(DEAD)
for rnd in range(6):
    forced, pairs = analyse(dead)
    print('round %d: dead bottom %s -> %d forced-zero products, %d two-term'
          % (rnd, sorted(dead), len(forced), len(pairs)))
    for i, t, e in sorted(set((i, t, e) for i, t, e in forced)):
        print('    star(c_%d) d_%d = 0   [%s]' % (i, t, e))
    # a bottom point dies when every product against it is forced to zero
    tops = {t for i, t, e in forced}
    new = set()
    for i in range(len(S0)):
        if i in dead:
            continue
        need = {t for t in range(len(S1))
                if any(xor(S0[i], S1[t]).count('1') <= 2 for _ in [0])}
        got = {t for j, t, e in forced if j == i}
        if need and need <= got:
            new.add(i)
    if not new:
        break
    dead |= new
