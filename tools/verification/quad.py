"""Walsh kernels as magnitude identities: the quadratic closure of the polytope.

A flip mask whose Walsh system has a one-dimensional kernel does not force any
product to vanish, so the linear scans see nothing.  But it does pin the
products to each other: if the kernel is spanned by v then P_j = v_j lambda for
a single scalar lambda, hence

    |P_j|^2 / v_j^2   is the same for every j with v_j nonzero,

and since |P_j|^2 = |conj(c_x) d_y|^2 = q_x r_y, this is a *quadratic* identity
among the probabilities.  Adding those identities to the linear moment system
collapses the polytope -- typically to a single point at which every amplitude
is an explicit positive rational.  That is where the nonvanishing comes from in
the orbits that resist every linear argument.

This script computes the identities, substitutes them into a parametrization of
the linear solution set, and solves the resulting small polynomial system
exactly.
"""
import sys
from itertools import combinations

import numpy as np
import sympy as sp

sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from orbit import fiber, ind
from scan import ORBITS, bits, xor, dot, dressings
from propagate import moment_matrix, polytope, TOL
from deriv import derive


def linear_system(S0, S1):
    rows, rhs = [], []
    rows.append([1] * len(S0) + [0] * len(S1)); rhs.append(1)
    rows.append([0] * len(S0) + [1] * len(S1)); rhs.append(1)
    for i in range(6):
        rows.append([ind(x, i) for x in S0] + [-ind(y, i) for y in S1]); rhs.append(0)
    for i, j in combinations(range(6), 2):
        rows.append([ind(x, i) * ind(x, j) for x in S0] + [-ind(y, i) * ind(y, j) for y in S1])
        rhs.append(0)
    return sp.Matrix(rows), sp.Matrix(rhs)


def kernels(S0, S1):
    """Every flip mask whose Walsh system has a one-dimensional kernel."""
    out = []
    for m in range(1, 64):
        e = bits(m)
        if e.count('1') > 2:
            continue
        inc = [(S0.index(xor(y, e)), j, y) for j, y in enumerate(S1) if xor(y, e) in S0]
        if len(inc) < 2:
            continue
        zs = dressings(e)
        M = sp.Matrix([[(-1) ** dot(z, y) for _, _, y in inc] for z in zs])
        ns = M.nullspace()
        if len(ns) == 1:
            v = ns[0]
            den = sp.lcm([sp.Rational(x).q for x in v])
            v = [sp.Rational(x) * den for x in v]
            g = sp.gcd([abs(x) for x in v if x != 0]) or 1
            v = [x / g for x in v]
            out.append((e, inc, v))
    return out


def solve_orbit(oid, a, q, delta):
    S0, S1 = fiber(a, q, 0), fiber(a, q, delta)
    n0, n1 = len(S0), len(S1)
    n = n0 + n1
    A, b = linear_system(S0, S1)
    # parametrize the affine solution set
    sol, params = A.gauss_jordan_solve(b)
    ts = sorted(sol.free_symbols, key=lambda s: s.name)
    ker = kernels(S0, S1)
    # quadratic identities: q_i r_j / v^2 equal along each kernel
    quad = []
    for e, inc, v in ker:
        base = None
        for t, (i, j, y) in enumerate(inc):
            if v[t] == 0:
                continue
            expr = sol[i] * sol[n0 + j] / (v[t] ** 2)
            if base is None:
                base = expr
            else:
                quad.append(sp.simplify(sp.expand(base - expr)))
    quad = [z for z in quad if z != 0]
    if not quad:
        return None
    gb = sp.groebner(quad, *ts, order='lex')
    sols = sp.solve(list(gb.exprs), ts, dict=True)
    good = []
    for s in sols:
        if any(not sp.im(val).is_zero for val in s.values() if val.is_number):
            continue
        pt = [sp.nsimplify(sp.simplify(sol[k].subs(s))) for k in range(n)]
        if any(not x.is_number for x in pt):
            continue
        if all(x >= 0 for x in pt):
            good.append(pt)
    return S0, S1, ker, quad, ts, good


CASES = [(54, [1, 1, 2, 2, 2, 5], 6, 1), (58, [1, 1, 2, 3, 3, 5], 7, 1),
         (25, [0, 1, 1, 1, 1, 1], 4, 1), (33, [0, 1, 1, 3, 3, 3], 5, 1),
         (56, [1, 2, 2, 2, 3, 3], 6, 1), (32, [1, 1, 2, 2, 2, 3], 4, 1)]

if __name__ == '__main__':
    for oid, a, q, delta in CASES:
        try:
            r = solve_orbit(oid, a, q, delta)
        except Exception as exc:
            print('orbit %-3d  failed: %s' % (oid, str(exc)[:70]))
            continue
        if r is None:
            print('orbit %-3d  no one-dimensional Walsh kernel' % oid)
            continue
        S0, S1, ker, quad, ts, good = r
        print('=' * 74)
        print('orbit %d  q=%d delta=%d  fibers (%d,%d)  free params %d  1-dim kernels %d  quadratics %d'
              % (oid, q, delta, len(S0), len(S1), len(ts), len(ker), len(quad)))
        print('  nonnegative solutions: %d' % len(good))
        for pt in good[:2]:
            pos = sum(1 for x in pt if x > 0)
            print('    %d/%d coordinates strictly positive' % (pos, len(pt)))
            print('    bottom:', [str(x) for x in pt[:len(S0)]])
            print('    top   :', [str(x) for x in pt[len(S0):]])
