"""Orbit 17: verify the degree-4 hafnian certificate symbolically.

With  a_i = c_0i  and  T_ijk = H_{0ijk} = a_i c_jk + a_j c_ik + a_k c_ij,

    3 a1 a2 a3 c45 = a4 a5 T123
        - (a1/2)(a5 T234 + a4 T235 - a3 T245 - a2 T345)
        - (a2/2)(a5 T134 + a4 T135 - a3 T145 - a1 T345)
        - (a3/2)(a5 T124 + a4 T125 - a2 T145 - a1 T245)

identically in the fifteen edge variables.
"""
from itertools import combinations

from sympy import expand, symbols, Rational

V = list(range(6))
EDGES = list(combinations(V, 2))
c = {e: symbols('c%d%d' % e) for e in EDGES}


def C(i, j):
    return c[(i, j) if i < j else (j, i)]


def H(i, j, k, l):
    return C(i, j) * C(k, l) + C(i, k) * C(j, l) + C(i, l) * C(j, k)


def a(i):
    return C(0, i)


def T(i, j, k):
    return H(0, i, j, k)


half = Rational(1, 2)
rhs = (a(4) * a(5) * T(1, 2, 3)
       - half * a(1) * (a(5) * T(2, 3, 4) + a(4) * T(2, 3, 5) - a(3) * T(2, 4, 5) - a(2) * T(3, 4, 5))
       - half * a(2) * (a(5) * T(1, 3, 4) + a(4) * T(1, 3, 5) - a(3) * T(1, 4, 5) - a(1) * T(3, 4, 5))
       - half * a(3) * (a(5) * T(1, 2, 4) + a(4) * T(1, 2, 5) - a(2) * T(1, 4, 5) - a(1) * T(2, 4, 5)))
lhs = 3 * a(1) * a(2) * a(3) * C(4, 5)
print('certificate identity holds:', expand(lhs - rhs) == 0)

# the same certificate as coefficients on the fifteen structure fields, for the
# goal  c01*c02*c03*c45 = 0
coeff = {}


def add(key, val):
    coeff[key] = coeff.get(key, 0) + val


third = Rational(1, 3)
add((0, 1, 2, 3), third * a(4) * a(5))
for (i, jkl) in [(1, [(2, 3, 4), (2, 3, 5), (2, 4, 5), (3, 4, 5)]),
                 (2, [(1, 3, 4), (1, 3, 5), (1, 4, 5), (3, 4, 5)]),
                 (3, [(1, 2, 4), (1, 2, 5), (1, 4, 5), (2, 4, 5)])]:
    sgn = {0: 1, 1: 1, 2: -1, 3: -1}
    mult = {1: [a(5), a(4), a(3), a(2)],
            2: [a(5), a(4), a(3), a(1)],
            3: [a(5), a(4), a(2), a(1)]}[i]
    for t, (j, k, l) in enumerate(jkl):
        add((0, j, k, l), -third * half * a(i) * sgn[t] * mult[t])

tot = 0
for key, val in coeff.items():
    tot += val * H(*key)
print('scaled certificate holds:', expand(C(0, 1) * C(0, 2) * C(0, 3) * C(4, 5) - tot) == 0)
print()
for key in sorted(coeff):
    if coeff[key] != 0:
        print('  h%d%d%d%d : %s' % (key + (coeff[key],)))
