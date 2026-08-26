"""Search every no-go orbit for a mechanizable Walsh certificate.

For a distance-three code the Knill-Laflamme conditions kill the off-diagonal
matrix element of every Pauli of weight at most two.  Writing such a Pauli as
X^e Z^z, the constraint is supp(e) union supp(z) of size at most two, and the
resulting equation is

    sum over y in S1 with y xor e in S0  of  (-1)^{z . y} conj(c_{y xor e}) d_y = 0.

Fix e.  The incidences of e give a list of unknown products P_1..P_k, and each
admissible dressing z gives one linear equation with coefficients +-1.  If the
resulting sign matrix determines some P_j to be zero, and the moment polytope
forces both endpoints of edge j to have strictly positive probability, the orbit
is impossible -- and the proof is a single `linear_combination`.

This is exactly the two-edge argument when k = 2, and it covers the four-, five-
and six-edge variants without any new idea.
"""
import sys
from fractions import Fraction
from itertools import combinations

import numpy as np
from scipy.optimize import linprog
from sympy import Matrix, Rational

sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from orbit import fiber, ind

ORBITS = {
    25: ([0, 1, 1, 1, 1, 1], 4, (12, 12)), 26: ([0, 1, 1, 2, 2, 3], 4, (16, 16)),
    27: ([1, 1, 1, 1, 1, 1], 4, (16, 12)), 28: ([1, 1, 1, 1, 1, 2], 4, (16, 16)),
    29: ([1, 1, 1, 1, 2, 2], 4, (16, 16)), 30: ([1, 1, 1, 1, 2, 3], 4, (16, 16)),
    31: ([1, 1, 1, 2, 2, 2], 4, (16, 16)), 32: ([1, 1, 2, 2, 2, 3], 4, (16, 16)),
    33: ([0, 1, 1, 3, 3, 3], 5, (12, 12)), 34: ([1, 1, 1, 1, 1, 1], 5, (7, 7)),
    35: ([1, 1, 1, 2, 2, 3], 5, (12, 13)), 37: ([1, 1, 1, 2, 3, 3], 5, (13, 13)),
    38: ([1, 1, 2, 2, 2, 3], 5, (13, 13)), 39: ([1, 1, 2, 3, 3, 3], 5, (12, 13)),
    40: ([1, 2, 2, 2, 2, 2], 5, (12, 12)), 53: ([1, 1, 1, 3, 3, 4], 6, (10, 10)),
    54: ([1, 1, 2, 2, 2, 5], 6, (9, 9)), 55: ([1, 1, 2, 2, 3, 4], 6, (11, 11)),
    56: ([1, 2, 2, 2, 3, 3], 6, (10, 10)), 57: ([1, 1, 1, 4, 4, 4], 7, (7, 7)),
    58: ([1, 1, 2, 3, 3, 5], 7, (9, 9)), 59: ([1, 1, 5, 5, 5, 5], 7, (7, 7)),
    60: ([1, 2, 2, 2, 4, 4], 7, (9, 9)), 61: ([1, 2, 2, 3, 3, 4], 7, (9, 9)),
    62: ([1, 1, 1, 5, 5, 5], 8, (7, 7)), 63: ([1, 1, 2, 4, 5, 5], 8, (8, 8)),
    64: ([1, 1, 3, 3, 3, 6], 8, (7, 7)), 65: ([1, 2, 2, 3, 4, 5], 8, (8, 8)),
    66: ([1, 2, 2, 4, 4, 6], 9, (7, 7)),
}


def bits(m):
    return ''.join('1' if m >> i & 1 else '0' for i in range(6))


def xor(s, t):
    return ''.join('1' if (s[i] == '1') != (t[i] == '1') else '0' for i in range(6))


def dot(z, y):
    return sum(1 for i in range(6) if z[i] == '1' and y[i] == '1') % 2


def lp_status(S0, S1):
    """forced-zero / forced-positive / undetermined, per coordinate."""
    rows, rhs = [], []
    rows.append([1] * len(S0) + [0] * len(S1)); rhs.append(1)
    rows.append([0] * len(S0) + [1] * len(S1)); rhs.append(1)
    for i in range(6):
        rows.append([ind(x, i) for x in S0] + [-ind(y, i) for y in S1]); rhs.append(0)
    for i, j in combinations(range(6), 2):
        rows.append([ind(x, i) * ind(x, j) for x in S0] + [-ind(y, i) * ind(y, j) for y in S1])
        rhs.append(0)
    A, b = np.array(rows, float), np.array(rhs, float)
    n = A.shape[1]
    st = []
    for k in range(n):
        c = np.zeros(n); c[k] = 1
        r1 = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * n)
        r2 = linprog(-c, A_eq=A, b_eq=b, bounds=[(0, None)] * n)
        if not (r1.success and r2.success):
            return None
        lo, hi = r1.fun, -r2.fun
        st.append(('zero', Fraction(0)) if hi < 1e-9 else
                  ('pos', Fraction(lo).limit_denominator(10000)) if lo > 1e-9 else
                  ('free', None))
    return st


def dressings(e):
    """Admissible Z-dressings for the flip e: supp(e) u supp(z) has size <= 2."""
    sup = [i for i in range(6) if e[i] == '1']
    if len(sup) == 1:
        return [bits(0)] + [bits(1 << j) for j in range(6)]
    if len(sup) == 2:
        i, j = sup
        return [bits(0), bits(1 << i), bits(1 << j), bits((1 << i) | (1 << j))]
    return []


def certify(S0, S1, st, e):
    """Try to force one live edge product to zero. Returns (edge, coeffs, eqs)."""
    n0 = len(S0)
    inc = [(k, S1[k], xor(S1[k], e)) for k in range(len(S1)) if xor(S1[k], e) in S0]
    if not inc:
        return None
    unknown, dead = [], []
    for k, y, x in inc:
        sy, sx = st[n0 + k], st[S0.index(x)]
        if sy[0] == 'zero' or sx[0] == 'zero':
            dead.append((k, y, x))          # product known to vanish, drops out
        else:
            unknown.append((k, y, x, sy[0] == 'pos' and sx[0] == 'pos'))
    if not unknown:
        return None
    zs = dressings(e)
    # One equation per admissible dressing, over the unknown products only.
    M = Matrix([[(-1) ** dot(z, y) for _, y, _, _ in unknown] for z in zs])
    for col in range(len(unknown)):
        if not unknown[col][3]:             # target must have both endpoints forced positive
            continue
        tgt = Matrix([1 if i == col else 0 for i in range(len(unknown))])
        if M.T.rank() == M.T.row_join(tgt).rank():
            lam = M.T.gauss_jordan_solve(tgt)[0]
            lam = lam.subs({p: 0 for p in lam.free_symbols})
            live = [(k, y, x) for k, y, x, _ in unknown]
            return live[col], [Rational(v) for v in lam], zs, live, dead
    return None


if __name__ == '__main__':
    print('%-5s %-4s %-6s %-9s %-6s %-5s %s' % ('轨道', 'q', 'delta', '纤维', '掩码', '边数', '证书'))
    print('-' * 78)
    hits, misses = [], []
    for oid in sorted(ORBITS):
        a, q, sizes = ORBITS[oid]
        S0 = fiber(a, q, 0)
        cands = [d for d in range(1, q)
                 if sizes is None or (len(S0), len(fiber(a, q, d))) == sizes]
        if not cands:
            cands = [d for d in range(1, q) if fiber(a, q, d)]
        done = False
        for delta in cands:
            S1 = fiber(a, q, delta)
            if not S1:
                continue
            st = lp_status(S0, S1)
            if st is None:
                continue
            for w in (1, 2):
                for m in range(1, 64):
                    e = bits(m)
                    if e.count('1') != w:
                        continue
                    r = certify(S0, S1, st, e)
                    if r:
                        (k, y, x), lam, zs, live, dead = r
                        print('%-5d %-4d %-6d %-9s %-6s %-5d 是  (%d 死边, %d 个 dressing)'
                              % (oid, q, delta, '(%d,%d)' % (len(S0), len(S1)), e, len(live),
                                 len(dead), sum(1 for c in lam if c != 0)))
                        hits.append((oid, q, delta, e, len(live), len(dead)))
                        done = True
                        break
                if done:
                    break
            if done:
                break
        if not done:
            print('%-5d %-4d %-6s %-9s %-6s %-5s 否' % (oid, q, '?', '', '', ''))
            misses.append(oid)
    print('-' * 78)
    print('可机械化: %d / %d' % (len(hits), len(ORBITS)))
    print('剩余    :', misses)
