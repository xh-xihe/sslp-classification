"""Phase 2: orbits closed by isolating SEVERAL incidences whose endpoint
probabilities are linearly tied by the moment system, so each case split
collapses and the vanishing set contradicts a linear moment relation.
"""
import io
import json
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
sys.path.insert(0, '.')
from orbit import fiber

ORB = [
    (52, 6, [1, 2, 3, 3, 4, 4], 2), (44, 6, [1, 1, 2, 3, 3, 4], 3),
    (46, 6, [1, 2, 2, 2, 3, 3], 3), (49, 6, [1, 1, 1, 3, 3, 5], 2),
    (50, 6, [1, 1, 1, 3, 4, 4], 2), (51, 6, [1, 1, 2, 3, 3, 4], 2),
    (17, 4, [1, 1, 1, 1, 1, 1], 2), (12, 4, [0, 1, 1, 1, 1, 2], 2),
    (13, 4, [0, 1, 1, 1, 2, 2], 2), (14, 4, [0, 1, 1, 2, 2, 2], 2),
    (15, 4, [0, 1, 2, 2, 2, 2], 2), (19, 4, [1, 1, 1, 1, 2, 2], 2),
    (20, 4, [1, 1, 1, 2, 2, 2], 2), (24, 4, [1, 2, 2, 2, 2, 3], 2),
    (5, 3, [0, 0, 1, 1, 1, 1], 1), (6, 3, [0, 1, 1, 1, 1, 1], 1),
]
bits = lambda s: [int(ch) for ch in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
supp = lambda s: {i for i, ch in enumerate(s) if ch == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dressings = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]


def momsys(S0, S1):
    n0, n1 = len(S0), len(S1)
    rows, rhs = [[1] * n0 + [0] * n1, [0] * n0 + [1] * n1], [1, 1]
    names = ['n0', 'n1']
    for T in [(i,) for i in range(6)] + list(combinations(range(6), 2)):
        L = [1 if all(S0[r][j] == '1' for j in T) else 0 for r in range(n0)]
        R = [-1 if all(S1[r][j] == '1' for j in T) else 0 for r in range(n1)]
        rows.append(L + R)
        rhs.append(0)
        names.append('m%s' % ''.join(str(j + 1) for j in T))
    return sp.Matrix(rows), sp.Matrix(rhs), names


def solveaffine(M, rhs, n):
    v = sp.Matrix(sp.symbols('t0:%d' % n))
    s = sp.solve([sp.Eq(a, b) for a, b in zip(M * v, rhs)], list(v), dict=True)
    if not s:
        return None, None
    s = s[0]
    expr = [sp.expand(s.get(v[k], v[k])) for k in range(n)]
    free = sorted({y for e in expr for y in e.free_symbols}, key=lambda y: y.name)
    return expr, free


for oid, q, a, d in ORB:
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    n0, n1 = len(S0), len(S1)
    M, rhs, names = momsys(S0, S1)
    expr, free = solveaffine(M, rhs, n0 + n1)
    if expr is None:
        print('orbit %-3d  moment system inconsistent?!' % oid)
        continue
    best = None
    for e in ALL:
        if not 1 <= len(supp(e)) <= 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1)
               if xor(y, e) in S0]
        if not inc:
            continue
        Z = dressings(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        iso = []
        for k in range(len(inc)):
            tgt = sp.Matrix([1 if r == k else 0 for r in range(len(inc))])
            try:
                W.T.gauss_jordan_solve(tgt)
            except ValueError:
                continue
            iso.append(k)
        if not iso:
            continue
        # which isolated incidences have linearly tied endpoints?
        tied = []
        for k in iso:
            i2, t2 = inc[k]
            pe, qe = expr[i2], expr[n0 + t2]
            if pe == 0 or qe == 0:
                continue
            lam = sp.simplify(pe / qe) if qe != 0 else None
            if lam is not None and lam.is_number and lam > 0:
                tied.append((k, i2, t2, sp.Rational(lam)))
        if not tied:
            continue
        # does forcing every tied endpoint to zero break the moment system?
        subs = {}
        for _, i2, t2, _ in tied:
            subs[i2] = 0
        rem = [expr[k] for k in range(n0) if k not in subs]
        eqs = [sp.Eq(expr[i2], 0) for _, i2, _, _ in tied]
        sol2 = sp.solve(eqs, free, dict=True)
        broken = False
        if not sol2:
            broken = True
        else:
            tot = sp.simplify(sum(expr[k] for k in range(n0)).subs(sol2[0]))
            broken = (tot != 1)
        if broken and (best is None or len(tied) < len(best[2])):
            best = (e, inc, tied, len(iso))
    if best:
        e, inc, tied, niso = best
        print('orbit %-3d  flip %s  %2d inc, %2d isolable, %d tied -> '
              'contradiction   %s'
              % (oid, e, len(inc), niso, len(tied),
                 ' '.join('(%s|%s,x%s)' % (S0[i2], S1[t2], lam)
                          for _, i2, t2, lam in tied[:4])))
    else:
        print('orbit %-3d  no phase-2 certificate' % oid)
