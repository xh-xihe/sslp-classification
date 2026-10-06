"""Rigorous rational lower bounds for every probability over the moment polytope.

scipy solves  min v_k  s.t.  M v = rhs, v >= 0  in floating point; the dual
vector is then rationalised and turned into an EXACT Farkas bound

    v_k = y^T M v + (e_k - M^T y)^T v
        >= y^T rhs + 2 * min(0, min_j (e_k - M^T y)_j)

using sum(v) = 2 (the two normalisations).  Only the exact right-hand side is
reported, so a sloppy dual weakens the bound but can never invalidate it.
`linarith` reproves any bound produced here from the `MomentSystem` fields.
"""
from fractions import Fraction as F
from itertools import combinations

import numpy as np
from scipy.optimize import linprog

IDX = [(i,) for i in range(6)] + list(combinations(range(6), 2))


def system(S0, S1):
    """The two normalisations and the twenty-one moment equalities, exactly."""
    n0, n1 = len(S0), len(S1)
    rows = [[1] * n0 + [0] * n1, [0] * n0 + [1] * n1]
    rhs = [F(1), F(1)]
    for T in IDX:
        rows.append([1 if all(S0[r][j] == '1' for j in T) else 0 for r in range(n0)]
                    + [-1 if all(S1[r][j] == '1' for j in T) else 0 for r in range(n1)])
        rhs.append(F(0))
    return [[F(x) for x in r] for r in rows], rhs


def lower_bounds(S0, S1, den=2 ** 14 * 3 ** 3 * 5 ** 2 * 7):
    M, rhs = system(S0, S1)
    m, n = len(M), len(M[0])
    Mf = np.array([[float(x) for x in r] for r in M])
    bf = np.array([float(x) for x in rhs])
    out = []
    for k in range(n):
        c = np.zeros(n)
        c[k] = 1.0
        res = linprog(c, A_eq=Mf, b_eq=bf, bounds=[(0, None)] * n, method='highs')
        if not res.success:
            out.append(F(0))
            continue
        y = [F(v).limit_denominator(den) for v in res.eqlin.marginals]
        slack = [(F(1) if j == k else F(0)) - sum(y[i] * M[i][j] for i in range(m))
                 for j in range(n)]
        val = sum(y[i] * rhs[i] for i in range(m)) + 2 * min(F(0), min(slack))
        out.append(max(F(0), val))
    return out


def functional_bound(S0, S1, coeff, den=2 ** 14 * 3 ** 3 * 5 ** 2 * 7):
    """Exact rational lower bound of a linear functional over the polytope."""
    M, rhs = system(S0, S1)
    m, n = len(M), len(M[0])
    Mf = np.array([[float(x) for x in r] for r in M])
    bf = np.array([float(x) for x in rhs])
    c = np.array([float(x) for x in coeff])
    res = linprog(c, A_eq=Mf, b_eq=bf, bounds=[(0, None)] * n, method='highs')
    if not res.success:
        return F(0)
    y = [F(v).limit_denominator(den) for v in res.eqlin.marginals]
    slack = [coeff[j] - sum(y[i] * M[i][j] for i in range(m)) for j in range(n)]
    return sum(y[i] * rhs[i] for i in range(m)) + 2 * min(F(0), min(slack))
