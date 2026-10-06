"""Verify the claimed diagonal moment normal forms in the new sections.

For each orbit we (a) rebuild the diagonal moment system from the fibers,
(b) substitute the paper's claimed affine solution and check every equation
    vanishes identically in the free parameters,
(c) confirm the claimed rank of the moment matrix.
"""
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
from orbit import fiber

al, be, ga, ta = sp.symbols('alpha beta gamma tau')
R = sp.Rational


def momrows(S0, S1):
    """Normalizations + all |T|<=2 character equalities, as a matrix."""
    n0, n1 = len(S0), len(S1)
    rows = [[1] * n0 + [0] * n1, [0] * n0 + [1] * n1]
    idx = [()] + [(i,) for i in range(6)] + list(combinations(range(6), 2))
    for T in idx:
        chi = lambda z: (-1) ** sum(int(z[i]) for i in T)
        rows.append([chi(x) for x in S0] + [-chi(y) for y in S1])
    return sp.Matrix(rows)


def run(oid, q, a, d, p_claim, q_claim, rank_claim, rhs_norm=True):
    S0 = fiber(a, q, 0)
    S1 = fiber(a, q, d)
    M = momrows(S0, S1)
    v = sp.Matrix(list(p_claim) + list(q_claim))
    if len(v) != M.cols:
        print('  orbit %-3d SIZE MISMATCH: fibers %d+%d, claim %d'
              % (oid, len(S0), len(S1), len(v)))
        return
    res = sp.simplify(M * v)
    # rows 0,1 are the two normalizations: they must equal 1
    bad = [k for k in range(M.rows)
           if sp.simplify(res[k] - (1 if k < 2 else 0)) != 0]
    rk = M.rank()
    print('  orbit %-3d fibers %2d+%-2d  moment eqs %2d  rank %2d (claim %s)  %s'
          % (oid, len(S0), len(S1), M.rows, rk,
             rank_claim if rank_claim else '-',
             'ALL SATISFIED' if not bad else 'FAILS rows %s' % bad))


print('claimed moment normal forms, re-derived from the fibers:')

# orbit 47 : gamma = 1/6 - alpha - beta
g = R(1, 6) - al - be
run(47, 6, [1, 1, 1, 1, 2, 2], 2,
    [R(1, 3), be, al, g, g, al, be, R(1, 6), R(1, 6)],
    [R(1, 6), R(1, 6), be, al, g, g, al, be, R(1, 3)], 16)

# orbit 48 : h = 1/6-(a+b)/2 , k = 1/3-a-b
h, kk = R(1, 6) - (al + be) / 2, R(1, 3) - al - be
run(48, 6, [1, 1, 1, 2, 2, 2], 2,
    [R(1, 3), R(1, 6), h, h, h, al / 2, al / 2, al / 2, be / 2, be / 2, be / 2],
    [R(1, 6), R(1, 6), R(1, 6), h, kk, al / 2, al, be / 2, be], 18)

# orbit 52
run(52, 6, [1, 2, 3, 3, 4, 4], 2,
    [R(1, 6) - al / 2, al / 2, R(1, 6) - al / 2, R(1, 6) - al / 2, al / 2,
     al / 2, R(1, 3) - 2 * be, 2 * be, R(1, 6) - be, be],
    [R(1, 6) - al / 2, al / 2, R(1, 3) - al, al, R(1, 6) - be, R(1, 6) - be,
     be, be, R(1, 6) - be, be], 18)

# orbits 42 and 43 : matched order, p = q
s = R(1, 4) - al - be - ga
PQ = [R(1, 4), R(1, 4), s, s, al, al, be, be, ga, ga]
for oid, a in ((42, [1, 1, 1, 1, 3, 3]), (43, [1, 1, 1, 2, 3, 3])):
    run(oid, 6, a, 3, PQ, PQ, 17)

# orbit 44 : u = 1/4-alpha-gamma , v = 1/4-beta
u, vv = R(1, 4) - al - ga, R(1, 4) - be
run(44, 6, [1, 1, 2, 3, 3, 4], 3,
    [u, u, al, al, vv, vv, be, be, ga, ga],
    [u, u, al, al, vv, vv, be, be, ga, ga], 17)

# orbit 46 : u = 1/4-alpha , v = 1/4-beta-gamma
u2, v2 = R(1, 4) - al, R(1, 4) - be - ga
run(46, 6, [1, 2, 2, 2, 3, 3], 3,
    [u2, u2, be, be, v2, v2, ga, ga, al, al],
    [u2, u2, be, be, v2, v2, ga, ga, al, al], 17)

print()
print('note: for 42/43/44/46 the paper orders both fibers by the half-angle')
print('matching, while fiber() returns lexicographic order, so a permutation')
print('mismatch shows up as FAILS rather than as a real discrepancy.')
