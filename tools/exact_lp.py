#!/usr/bin/env python3
"""Exact rational phase-1 simplex, with the Farkas dual read off the tableau.

Written after a hand-rolled version got the objective-row update wrong: it
used `z[pivot]` where the reduced cost `z[pivot] - c_pivot` was required,
which agree only while the entering column is non-artificial.  When an
artificial column entered, the maintained dual row drifted, the entering rule
picked a non-improving column, and the loop could leave through the "no
positive ratio" escape -- reporting a feasible system as infeasible.

This version keeps only the tableau, which ordinary pivoting cannot corrupt,
and recomputes `z_j = sum_k c_{basis k} * T[k][j]` from the basis each
iteration.  The artificial block of the tableau is `B^{-1}`, so the phase-1
dual is `y_i = z_{n+i}`.
"""
from fractions import Fraction as F


def solve(A, b):
    """Phase-1 simplex on `{A z = b, z >= 0}` with exact rationals.

    Returns `(status, x, y)`:
      * `('feasible', x, None)` -- `x >= 0` with `A x = b`, a basic solution;
      * `('infeasible', None, y)` -- `y . A <= 0` componentwise, `y . b > 0`.
    """
    m = len(A)
    n = len(A[0])
    A = [row[:] for row in A]
    b = list(b)
    sign = [1] * m
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]
            b[i] = -b[i]
            sign[i] = -1
    N = n + m
    T = [A[i] + [F(1) if j == i else F(0) for j in range(m)] + [b[i]]
         for i in range(m)]
    basis = [n + i for i in range(m)]
    cost = lambda j: F(1) if j >= n else F(0)      # noqa: E731

    while True:
        cb = [cost(basis[k]) for k in range(m)]
        inbasis = set(basis)
        entering = -1
        for j in range(N):                          # Bland: smallest index
            if j in inbasis:
                continue
            zj = sum(cb[k] * T[k][j] for k in range(m) if cb[k])
            if cost(j) - zj < 0:
                entering = j
                break
        if entering < 0:
            break
        ratios = [(T[i][N] / T[i][entering], basis[i], i)
                  for i in range(m) if T[i][entering] > 0]
        if not ratios:
            raise RuntimeError('phase-1 reported an unbounded column; '
                               'the objective is bounded below by zero, so '
                               'this means the tableau is corrupt')
        _, _, r = min(ratios)
        pv = T[r][entering]
        T[r] = [v / pv for v in T[r]]
        for i in range(m):
            if i != r and T[i][entering] != 0:
                f = T[i][entering]
                T[i] = [a - f * c for a, c in zip(T[i], T[r])]
        basis[r] = entering

    obj = sum(T[i][N] for i in range(m) if basis[i] >= n)
    if obj == 0:
        x = [F(0)] * n
        for i in range(m):
            if basis[i] < n:
                x[basis[i]] = T[i][N]
        return 'feasible', x, None
    cb = [cost(basis[k]) for k in range(m)]
    y = [sum(cb[k] * T[k][n + i] for k in range(m) if cb[k]) * sign[i]
         for i in range(m)]
    return 'infeasible', None, y


def check(A, b, status, x, y):
    """Independent verification of whichever certificate came back."""
    m, n = len(A), len(A[0])
    if status == 'feasible':
        assert all(v >= 0 for v in x)
        for i in range(m):
            assert sum(A[i][j] * x[j] for j in range(n)) == b[i]
        return True
    for j in range(n):
        assert sum(y[i] * A[i][j] for i in range(m)) <= 0, 'y.A <= 0 fails'
    assert sum(y[i] * b[i] for i in range(m)) > 0, 'y.b > 0 fails'
    return True
