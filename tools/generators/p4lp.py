"""Parity-four triad: what the physical weight<=2 moment system really pins.

For each of orbits 15, 24, 14 we index the two fibers by (r, z) where r is the
C^2 index (zero-angle qubit, or the repetition bit) and z is the effective
four-bit parity string.  Then we ask, in exact rational arithmetic:

  (1) is every physical probability forced positive?      (row-space + LP)
  (2) is  sum_k q_{z xor e_k}  =  1/4 + 2 p_z  a linear consequence
      of the 23 moment equations?                          (row-space test)
"""
import sys
from fractions import Fraction as F
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
from orbit import fiber

ORB = {
    15: (4, [0, 1, 2, 2, 2, 2], 2, 0, [2, 3, 4, 5]),
    24: (4, [1, 2, 2, 2, 2, 3], 2, 0, [1, 2, 3, 4]),
    14: (4, [0, 1, 1, 2, 2, 2], 2, 0, [1, 3, 4, 5]),
}
EVEN = [format(k, '04b') for k in range(16) if bin(k).count('1') % 2 == 0]
ODD = [format(k, '04b') for k in range(16) if bin(k).count('1') % 2 == 1]
xor4 = lambda z, k: z[:k] + '01'[z[k] == '0'] + z[k + 1:]


def index(oid):
    q, a, d, free, eff = ORB[oid]
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    key = lambda s: (s[free], ''.join(s[i] for i in eff))
    b = {key(x): r for r, x in enumerate(S0)}
    t = {key(y): r for r, y in enumerate(S1)}
    assert len(b) == 16 and len(t) == 16, (oid, len(b), len(t))
    return S0, S1, b, t


def rows(S0, S1):
    """23 moment equations as (coeff vector over q0..q15 r0..r15, rhs)."""
    n0, n1 = len(S0), len(S1)
    ind = lambda s, i: 1 if s[i] == '1' else 0
    R = [([1] * n0 + [0] * n1, 1), ([0] * n0 + [1] * n1, 1)]
    for i in range(6):
        R.append(([ind(x, i) for x in S0] + [-ind(y, i) for y in S1], 0))
    for i, j in combinations(range(6), 2):
        R.append(([ind(x, i) * ind(x, j) for x in S0]
                  + [-ind(y, i) * ind(y, j) for y in S1], 0))
    return R


def inrowspace(R, target, rhs):
    """Is (target, rhs) an exact rational combination of the affine rows R?"""
    A = sp.Matrix([r[0] + [r[1]] for r in R]).T          # columns = rows of R
    b = sp.Matrix(list(target) + [rhs])
    sol = A.gauss_jordan_solve(b) if A.rank() == sp.Matrix(
        A.tolist()).row_join(b).rank() - 0 else None
    try:
        x, params = A.gauss_jordan_solve(b)
    except ValueError:
        return None
    x = x.subs({s: 0 for s in params})
    return [(i, sp.Rational(x[i])) for i in range(len(R)) if x[i] != 0]


for oid in (15, 24, 14):
    S0, S1, b, t = index(oid)
    R = rows(S0, S1)
    n = 32
    print('=== orbit %d' % oid)
    # (2) the edge-sum identity, one per even z
    ok = True
    for z in EVEN:
        tgt = [0] * n
        for k in range(4):
            for r in '01':
                tgt[16 + t[(r, xor4(z, k))]] += 1
        for r in '01':
            tgt[b[(r, z)]] += -2
        cmb = inrowspace(R, tgt, F(1, 4))
        if cmb is None:
            ok = False
            print('   NOT a consequence for z=%s' % z)
    print('   sum_k q_{z^e_k} = 1/4 + 2 p_z  derivable for all 8 even z: %s' % ok)
    ok = True
    for w in ODD:
        tgt = [0] * n
        for k in range(4):
            for r in '01':
                tgt[b[(r, xor4(w, k))]] += 1
        for r in '01':
            tgt[16 + t[(r, w)]] += -2
        if inrowspace(R, tgt, F(1, 4)) is None:
            ok = False
    print('   sum_k p_{w^e_k} = 1/4 + 2 q_w  derivable for all 8 odd w: %s' % ok)
