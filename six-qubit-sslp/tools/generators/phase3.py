"""Phase 3: orbits closed by an odd triangle of reciprocal flip relations.

Needs, for three indices a,b,c:
  * complementary fibers, so index t by  y_t = complement(x_t);
  * three row-reduced relations  z_ij + z_ji = 0  on the pairs (a,b),(a,c),(b,c);
  * all three probabilities forced positive on the whole moment polytope.
"""
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
sys.path.insert(0, '.')
from orbit import fiber

ORB = [(49, 6, [1, 1, 1, 3, 3, 5], 2), (50, 6, [1, 1, 1, 3, 4, 4], 2),
       (51, 6, [1, 1, 2, 3, 3, 4], 2), (20, 4, [1, 1, 1, 2, 2, 2], 2),
       (17, 4, [1, 1, 1, 1, 1, 1], 2), (19, 4, [1, 1, 1, 1, 2, 2], 2)]

bits = lambda s: [int(c) for c in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
comp = lambda s: ''.join('01'[1 - int(c)] for c in s)
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]


def momentexpr(S0, S1):
    n0, n1 = len(S0), len(S1)
    rows, rhs = [[1] * n0 + [0] * n1, [0] * n0 + [1] * n1], [1, 1]
    for T in [(i,) for i in range(6)] + list(combinations(range(6), 2)):
        rows.append([1 if all(S0[r][j] == '1' for j in T) else 0 for r in range(n0)]
                    + [-1 if all(S1[r][j] == '1' for j in T) else 0 for r in range(n1)])
        rhs.append(0)
    v = sp.Matrix(sp.symbols('t0:%d' % (n0 + n1)))
    sol = sp.solve([sp.Eq(x, y) for x, y in
                    zip(sp.Matrix(rows) * v, sp.Matrix(rhs))], list(v), dict=True)
    if not sol:
        return None
    return [sp.expand(sol[0].get(v[k], v[k])) for k in range(n0 + n1)]


def positive_always(e, free):
    """Is the affine expression e strictly positive on its whole domain?
    Constant positive is the only case we certify here."""
    return e.is_number and e > 0


for oid, q, a, d in ORB:
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    n0 = len(S0)
    if sorted(comp(x) for x in S0) != sorted(S1):
        print('orbit %-3d  fibers NOT complementary -> different route' % oid)
        continue
    tidx = {comp(x): r for r, x in enumerate(S0)}      # top index by bottom label
    perm = [tidx[y] for y in S1]                        # S1[t] is complement of S0[perm[t]]
    expr = momentexpr(S0, S1)
    if expr is None:
        print('orbit %-3d  moment system inconsistent' % oid)
        continue
    # reciprocal relations available:  z_{ij} + z_{ji} = 0
    rec = set()
    for e in ALL:
        if not 1 <= len(supp(e)) <= 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        if not inc:
            continue
        Z = dress(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        # look for a row-space vector supported on exactly one reciprocal pair
        for k1, k2 in combinations(range(len(inc)), 2):
            i1, t1 = inc[k1]
            i2, t2 = inc[k2]
            if not (perm[t1] == i2 and perm[t2] == i1):
                continue                    # not a reciprocal pair
            for sgn in (1, -1):
                tgt = sp.Matrix([1 if r == k1 else (sgn if r == k2 else 0)
                                 for r in range(len(inc))])
                try:
                    W.T.gauss_jordan_solve(tgt)
                except ValueError:
                    continue
                rec.add((min(i1, i2), max(i1, i2), sgn))
                break
    minus = {(i, j) for i, j, s in rec if s == 1}   # z_ij + z_ji = 0
    pos = [k for k in range(n0) if positive_always(expr[k], None)]
    tri = None
    for a1, b1, c1 in combinations(sorted(set(x for p in minus for x in p)), 3):
        if all(tuple(sorted(p)) in minus for p in ((a1, b1), (a1, c1), (b1, c1))):
            if all(k in pos for k in (a1, b1, c1)):
                tri = (a1, b1, c1)
                break
    print('orbit %-3d  complementary, %d reciprocal(-) pairs, %d forced-positive '
          'indices, triangle %s'
          % (oid, len(minus), len(pos), tri if tri else 'NONE (needs pinning)'))
    if tri:
        print('        indices %s -> probabilities %s'
              % (str(tri), [expr[k] for k in tri]))
