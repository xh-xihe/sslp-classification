"""Block analysis for orbits whose first angle is zero.

The zero-angle qubit is kept as a two-component index, so each fiber splits into
blocks of two amplitudes.  This module builds the block structure and reports
what the diagonal Knill-Laflamme conditions say about the block outer products.
"""
import sys
sys.path.insert(0, '.')
from itertools import combinations

import sympy as sp

from orbit import fiber
from scan import ORBITS, bits, xor, dot
from kl import dressings_full
from propagate import pdim, DLP


def structure(oid):
    a, q, sz = ORBITS[oid]
    assert a[0] == 0, 'orbit %d has no zero angle' % oid
    S0 = fiber(a, q, 0)
    ds = [x for x in range(1, q) if fiber(a, q, x)
          and (sz is None or (len(S0), len(fiber(a, q, x))) == sz)
          and pdim(S0, fiber(a, q, x)) == DLP[oid]]
    S1 = fiber(a, q, ds[0])
    tails0 = sorted({x[1:] for x in S0})
    tails1 = sorted({y[1:] for y in S1})
    BOT = [(S0.index('0' + u), S0.index('1' + u)) for u in tails0]
    TOP = [(S1.index('0' + u), S1.index('1' + u)) for u in tails1]
    return a, q, ds[0], S0, S1, tails0, tails1, BOT, TOP


def diag_span(oid):
    """Row space of the diagonal conditions in the block outer-product monomials."""
    a, q, d, S0, S1, t0s, t1s, BOT, TOP = structure(oid)
    n = len(BOT)
    Pc = {(x, y, i): sp.Symbol('Pc%d%d_%d' % (x, y, i))
          for x in (0, 1) for y in (0, 1) for i in range(n)}
    Pd = {(x, y, i): sp.Symbol('Pd%d%d_%d' % (x, y, i))
          for x in (0, 1) for y in (0, 1) for i in range(n)}
    E0, EX = '000000', '100000'
    ZS = [bits(0)] + [bits(1 << j) for j in range(1, 6)] \
         + [bits(1)] + [bits(1 | (1 << j)) for j in range(1, 6)]
    conds = []
    for e in (E0, EX):
        for z in ZS:
            ex = 0
            for i in range(n):
                b0, b1 = BOT[i]
                u, v = ((0, 0), (1, 1)) if e == E0 else ((0, 1), (1, 0))
                ex += (-1) ** dot(z, S0[b0]) * Pc[(u[0], u[1], i)]
                ex += (-1) ** dot(z, S0[b1]) * Pc[(v[0], v[1], i)]
            for i in range(n):
                c0, c1 = TOP[i]
                u, v = ((0, 0), (1, 1)) if e == E0 else ((0, 1), (1, 0))
                ex -= (-1) ** dot(z, S1[c0]) * Pd[(u[0], u[1], i)]
                ex -= (-1) ** dot(z, S1[c1]) * Pd[(v[0], v[1], i)]
            conds.append((e, z, sp.expand(ex)))
    return Pc, Pd, conds, n, (a, q, d, S0, S1, t0s, t1s, BOT, TOP)


def report(oid):
    Pc, Pd, conds, n, st = diag_span(oid)
    a, q, d, S0, S1, t0s, t1s, BOT, TOP = st
    print('=== orbit %d  a=%s q=%d delta=%d  %d blocks ===' % (oid, a, q, d, n))
    print('bottom tails', t0s)
    print('top    tails', t1s)
    mons = sorted(set(Pc.values()) | set(Pd.values()), key=str)
    M = sp.Matrix([[c[2].coeff(m) for m in mons] for c in conds])
    print('diagonal conditions: %d rows, %d monomials, rank %d'
          % (M.rows, len(mons), M.rank()))
    # which off-diagonal (0,1) consequences are available
    for pair in [(0, 0), (0, 1)]:
        sub = [k for k, c in enumerate(conds)
               if (c[0] == '000000') == (pair == (0, 0))]
        Ms = sp.Matrix([[conds[k][2].coeff(m) for m in mons] for k in sub])
        print('  block %s family: %d rows rank %d' % (pair, Ms.rows, Ms.rank()))


if __name__ == '__main__':
    for oid in [int(v) for v in sys.argv[1:]] or [33, 26]:
        report(oid)
