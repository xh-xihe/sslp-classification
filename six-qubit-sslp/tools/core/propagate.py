"""Fixpoint propagation between the moment polytope and the Walsh systems.

Orbit identity is read from ``tools/manifest.json``. In particular, the second
residue is always ``delta = q/m`` with additive order ``m``; fiber size and
polytope dimension are diagnostics only and never select a residue.

The earlier scans asked for a single certificate: one edge whose product is
forced to vanish and whose two endpoint probabilities the polytope forces to be
strictly positive.  That is too narrow.  The paper's own argument for orbit 27
runs differently:

    one anchor amplitude is forced positive;
    a Walsh system forces a product through that anchor to vanish;
    hence the *other* endpoint amplitude vanishes;
    feeding that zero back into the polytope forces more, and the accumulated
    zeros finally contradict a positive sum of probabilities.

So the right object is a fixpoint.  Maintain a set Z of coordinates known to
vanish.  Re-solve the polytope with those coordinates pinned to zero; that
yields both new forced zeros and new forced positives.  Then run every Walsh
system with the known-zero products eliminated; each product it forces to
vanish, paired with a forced-positive endpoint, yields a new zero.  Iterate.

If at any round the polytope becomes infeasible, the orbit is impossible, and
the accumulated derivation is the certificate.
"""
import io
import json
import os
from fractions import Fraction
from itertools import combinations
from math import gcd

import numpy as np
from scipy.optimize import linprog
from sympy import Matrix

from orbit import fiber, ind
from scan import ORBITS, bits, xor, dot, dressings

HERE = os.path.dirname(os.path.abspath(__file__))
MANIFEST = json.loads(io.open(os.path.join(HERE, '..', 'manifest.json'),
                              encoding='utf-8').read())

TOL = 1e-9


def moment_matrix(S0, S1):
    rows, rhs = [], []
    rows.append([1] * len(S0) + [0] * len(S1)); rhs.append(1)
    rows.append([0] * len(S0) + [1] * len(S1)); rhs.append(1)
    for i in range(6):
        rows.append([ind(x, i) for x in S0] + [-ind(y, i) for y in S1]); rhs.append(0)
    for i, j in combinations(range(6), 2):
        rows.append([ind(x, i) * ind(x, j) for x in S0] + [-ind(y, i) * ind(y, j) for y in S1])
        rhs.append(0)
    return np.array(rows, float), np.array(rhs, float)


def polytope(A, b, Z, n):
    """Per-coordinate min/max over {x >= 0 : Ax = b, x_i = 0 for i in Z}."""
    bounds = [(0, 0) if k in Z else (0, None) for k in range(n)]
    probe = linprog(np.zeros(n), A_eq=A, b_eq=b, bounds=bounds)
    if not probe.success:
        return None                                    # infeasible: the orbit is dead
    lo, hi = [], []
    for k in range(n):
        c = np.zeros(n); c[k] = 1
        r1 = linprog(c, A_eq=A, b_eq=b, bounds=bounds)
        r2 = linprog(-c, A_eq=A, b_eq=b, bounds=bounds)
        lo.append(r1.fun if r1.success else 0.0)
        hi.append(-r2.fun if r2.success else 0.0)
    return np.array(lo), np.array(hi)


def walsh_zeros(S0, S1, deadProd):
    """Products every admissible Walsh system forces to vanish."""
    n0 = len(S0)
    out = set()
    for m in range(1, 64):
        e = bits(m)
        if e.count('1') > 2:
            continue
        inc = []
        for j, y in enumerate(S1):
            x = xor(y, e)
            if x in S0:
                i = S0.index(x)
                if (i, j) not in deadProd:
                    inc.append((i, j, y))
        if not inc:
            continue
        zs = dressings(e)
        M = Matrix([[(-1) ** dot(z, y) for _, _, y in inc] for z in zs])
        MT = M.T
        r = MT.rank()
        for col in range(len(inc)):
            tgt = Matrix([1 if t == col else 0 for t in range(len(inc))])
            if r == MT.row_join(tgt).rank():
                out.add((inc[col][0], inc[col][1], e))
    return out


def run(oid, a, q, delta, verbose=False):
    S0, S1 = fiber(a, q, 0), fiber(a, q, delta)
    n0, n1 = len(S0), len(S1)
    n = n0 + n1
    A, b = moment_matrix(S0, S1)
    Z = set()
    deadProd = set()
    trace = []
    for rnd in range(12):
        pt = polytope(A, b, Z, n)
        if pt is None:
            trace.append('round %d: polytope infeasible' % rnd)
            return True, trace, len(Z)
        lo, hi = pt
        newZ = {k for k in range(n) if hi[k] < TOL} - Z
        if newZ:
            Z |= newZ
            trace.append('round %d: polytope forces %d more coordinates to zero' % (rnd, len(newZ)))
            continue
        pos = {k for k in range(n) if lo[k] > TOL}
        # products already known to vanish because an endpoint does
        deadProd |= {(i, j) for i in range(n0) for j in range(n1)
                     if i in Z or (n0 + j) in Z}
        wz = walsh_zeros(S0, S1, deadProd)
        gained = set()
        for i, j, e in wz:
            if i in pos and (n0 + j) not in Z:
                gained.add(n0 + j)
            if (n0 + j) in pos and i not in Z:
                gained.add(i)
            deadProd.add((i, j))
        gained -= Z
        if not gained:
            trace.append('round %d: fixpoint, %d zeros, %d forced positive' % (rnd, len(Z), len(pos)))
            return False, trace, len(Z)
        Z |= gained
        trace.append('round %d: Walsh + anchors force %d more amplitudes to zero' % (rnd, len(gained)))
    return False, trace + ['round limit'], len(Z)


REMAINING = [25, 29, 31, 32, 38, 54, 56, 26, 27, 33, 35, 37, 58]
DLP = {25:6, 26:12, 27:5, 29:8, 31:9, 32:9, 33:6, 35:2, 37:6, 38:6,
       54:2, 56:3, 58:2}


def pdim(S0, S1):
    """Dimension of {x >= 0 : Ax = b}: support size minus the rank there."""
    A, b = moment_matrix(S0, S1)
    n = A.shape[1]
    pt = polytope(A, b, set(), n)
    if pt is None:
        return None
    lo, hi = pt
    sup = [k for k in range(n) if hi[k] > TOL]
    if not sup:
        return None
    return len(sup) - np.linalg.matrix_rank(A[:, sup])


def pick_delta(oid, a, q, sizes):
    """Return the manifest's authoritative delta after independent validation."""
    ent = MANIFEST.get(str(oid))
    if ent is None:
        raise ValueError('orbit %s is absent from tools/manifest.json' % oid)
    if ent['q'] != q or sorted(ent['a']) != sorted(a):
        raise ValueError('orbit %s legacy data disagree with the manifest' % oid)
    m = ent['m']
    if m <= 0 or q % m != 0:
        raise ValueError('orbit %s has invalid q=%s, m=%s' % (oid, q, m))
    d = q // m
    if ent['d'] != d or q // gcd(q, d) != m:
        raise ValueError('orbit %s manifest delta does not have order m' % oid)
    S0 = fiber(a, q, 0)
    S1 = fiber(a, q, d)
    got_sizes = (len(S0), len(S1))
    if sizes is not None and got_sizes != sizes:
        raise ValueError('orbit %s legacy fiber sizes %s != manifest fiber %s'
                         % (oid, sizes, got_sizes))
    if got_sizes != (ent['n0'], ent['n1']):
        raise ValueError('orbit %s recomputed fiber sizes disagree with manifest' % oid)
    if oid in DLP and pdim(S0, S1) != DLP[oid]:
        raise ValueError('orbit %s d_LP diagnostic disagrees with recorded value' % oid)
    return [d]


if __name__ == '__main__':
    print('%-5s %-6s %-9s %-6s %s' % ('orbit', 'delta', 'fibers', 'verdict', 'trace'))
    print('-' * 80)
    solved, unsolved = [], []
    for oid in sorted(REMAINING):
        a, q, sizes = ORBITS[oid]
        ds = pick_delta(oid, a, q, sizes)
        S0 = fiber(a, q, 0)
        results = []
        for delta in ds:
            S1 = fiber(a, q, delta)
            ok, trace, nz = run(oid, a, q, delta)
            results.append((delta, S1, ok, trace))
        allok = all(r[2] for r in results)
        delta, S1, ok, trace = results[0]
        print('%-5d %-6s %-9s %-6s %s'
              % (oid, ','.join(str(r[0]) for r in results),
                 '(%d,%d)' % (len(S0), len(S1)),
                 'DEAD' if allok else 'open', trace[-1]))
        (solved if allok else unsolved).append(oid)
    print('-' * 80)
    print('propagation closes: %d / %d' % (len(solved), len(REMAINING)), sorted(solved))
    print('still open       :', sorted(unsolved))
