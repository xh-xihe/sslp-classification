"""Two-term relations among the incidence products, without assuming that the
two fibers are complementary.

`relations.analyse` indexes everything through the complement map `hat`, which
only exists when `S1` is the bitwise complement of `S0`.  Orbits whose angle
vector sums to zero have `S1` disjoint from that complement, so this module
works directly with the products `star(c_x) d_y` instead.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from itertools import combinations

import sympy as sp

from orbit import fiber
from scan import ORBITS, bits, xor, dot
from kl import dressings_full
from propagate import pdim, DLP


def setup(oid):
    a, q, sz = ORBITS[oid]
    S0 = fiber(a, q, 0)
    ds = [x for x in range(1, q) if fiber(a, q, x)
          and (sz is None or (len(S0), len(fiber(a, q, x))) == sz)
          and pdim(S0, fiber(a, q, x)) == DLP[oid]]
    return a, q, ds[0], S0, fiber(a, q, ds[0])


def two_term(S0, S1):
    """All (i,t,k,u,sign,mask) with star(c_i) d_t + sign*star(c_k) d_u in a row space."""
    out = []
    for m in range(1, 64):
        e = bits(m)
        if e.count('1') > 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        if len(inc) < 2:
            if len(inc) == 1:
                out.append((inc[0][0], inc[0][1], None, None, 0, e))
            continue
        M = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in dressings_full(e)])
        MT = M.T
        r = MT.rank()
        for u, v in combinations(range(len(inc)), 2):
            for sg in (1, -1):
                tgt = sp.zeros(len(inc), 1)
                tgt[u] = 1
                tgt[v] = sg
                if MT.row_join(tgt).rank() == r:
                    out.append((inc[u][0], inc[u][1], inc[v][0], inc[v][1], sg, e))
    return out


if __name__ == '__main__':
    for oid in [int(v) for v in sys.argv[1:]] or [29]:
        a, q, d, S0, S1 = setup(oid)
        rel = two_term(S0, S1)
        forced = [r for r in rel if r[4] == 0]
        pairs = [r for r in rel if r[4] != 0]
        print('=== orbit %d  a=%s q=%d delta=%d  |S0|=%d |S1|=%d ==='
              % (oid, a, q, d, len(S0), len(S1)))
        print('single-incidence masks (forced-zero products): %d' % len(forced))
        for i, t, _, _, _, e in forced:
            print('    star(c_%d) d_%d = 0   [mask %s]' % (i, t, e))
        print('two-term relations: %d' % len(pairs))
        seen = set()
        for i, t, k, u, sg, e in pairs:
            key = tuple(sorted([(i, t), (k, u)]))
            if key in seen:
                continue
            seen.add(key)
            print('    P(%d,%d) %s P(%d,%d) = 0   [%s]'
                  % (i, t, '+' if sg == 1 else '-', k, u, e))
