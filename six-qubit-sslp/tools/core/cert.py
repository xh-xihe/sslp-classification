"""Exact linear_combination certificates for the quadratic closure.

Each Walsh kernel gives a quadratic identity q_i r_j = q_k r_l.  Modulo the
linear moment ideal that quadratic reduces to a LINEAR relation -- the quadratic
parts cancel identically.  To hand Lean a `linear_combination`, we need the
cofactors, so we row-reduce the moment system while tracking the transformation
matrix and then divide the quadratic by the reduced rows.
"""
import sys
sys.path.insert(0, '.')
from itertools import combinations

import sympy as sp

from orbit import fiber, ind


def build(S0, S1):
    n0, n1 = len(S0), len(S1)
    Q = sp.symbols('q0:%d' % n0)
    R = sp.symbols('r0:%d' % n1)
    V = list(Q) + list(R)
    rows, rhs, names = [], [], []
    rows.append([1] * n0 + [0] * n1); rhs.append(1); names.append('n0')
    rows.append([0] * n0 + [1] * n1); rhs.append(1); names.append('n1')
    for i in range(6):
        rows.append([ind(x, i) for x in S0] + [-ind(y, i) for y in S1])
        rhs.append(0); names.append('m%d' % (i + 1))
    for i, j in combinations(range(6), 2):
        rows.append([ind(x, i) * ind(x, j) for x in S0] + [-ind(y, i) * ind(y, j) for y in S1])
        rhs.append(0); names.append('c%d%d' % (i + 1, j + 1))
    return Q, R, V, sp.Matrix(rows), sp.Matrix(rhs), names


def reduce_mod_linear(expr, V, A, b):
    """Return (cofactors over the ORIGINAL equations, remainder).

    Row-reduce [A | b | I] so that the reduced equations are known combinations
    of the original ones, divide by them, then push the quotients back through
    the transformation.
    """
    m, n = A.shape
    aug = A.row_join(b).row_join(sp.eye(m))
    R = aug.rref()[0]
    gens, T = [], []
    for i in range(m):
        row = R[i, :n]
        if all(x == 0 for x in row):
            continue
        gens.append(sum(row[k] * V[k] for k in range(n)) - R[i, n])
        T.append([R[i, n + 1 + j] for j in range(m)])
    quo, rem = sp.reduced(sp.expand(expr), gens, *V, order='lex')
    cof = [sp.expand(sum(quo[i] * T[i][j] for i in range(len(gens)))) for j in range(m)]
    return cof, sp.expand(rem)
