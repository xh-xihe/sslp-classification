"""Verify the paper's explicit orbit-9 witness against the COMPLETE
weight-<=2 Knill-Laflamme system, exactly, in the cyclotomic field.

Coefficient on |x> is zeta_6^k / sqrt(d), with zeta_6 = exp(i pi / 3).
"""
import sys

import sympy as sp

sys.path.insert(0, 'tools/core')
from orbit import fiber
from scan import dot
from kl import conditions, dressings_full

Q, A, D = 3, [1, 1, 1, 1, 1, 2], 1

L0 = [('000000', 5, 12), ('000111', 2, 12), ('001110', 3, 12),
      ('010110', 3, 12), ('011001', 2, 6), ('100001', 0, 12),
      ('101000', 3, 12), ('101111', 2, 12), ('110000', 5, 12),
      ('110111', 0, 12), ('111110', 5, 12)]
L1 = [('000001', 5, 12), ('001000', 4, 12), ('001111', 5, 12),
      ('010000', 2, 12), ('010111', 1, 12), ('011110', 4, 12),
      ('100110', 5, 6), ('101001', 1, 12), ('110001', 1, 12),
      ('111000', 2, 12), ('111111', 5, 12)]

S0, S1 = fiber(A, Q, 0), fiber(A, Q, D)
print('fiber sizes: |S_0| = %d, |S_1| = %d   (witness lists %d and %d)'
      % (len(S0), len(S1), len(L0), len(L1)))
print('L_0 sits inside S_0 :', sorted(x for x, _, _ in L0) == sorted(S0))
print('L_1 sits inside S_1 :', sorted(x for x, _, _ in L1) == sorted(S1))

z6 = sp.exp(sp.I * sp.pi / 3)
amp = lambda k, d: sp.nsimplify(z6 ** k / sp.sqrt(d))
c = {x: amp(k, d) for x, k, d in L0}
d_ = {y: amp(k, dd) for y, k, dd in L1}
cv = [sp.expand(c.get(x, 0)) for x in S0]
dv = [sp.expand(d_.get(y, 0)) for y in S1]

n0 = sp.simplify(sum(sp.Abs(v) ** 2 for v in cv))
n1 = sp.simplify(sum(sp.Abs(v) ** 2 for v in dv))
print('normalisations: <0|0> = %s , <1|1> = %s' % (n0, n1))

probs0 = sorted(sp.simplify(sp.Abs(v) ** 2) for v in cv)
print('bottom probabilities:', probs0)

C = conditions(S0, S1)
print('weight-<=2 Pauli conditions supplied by kl.py: %d' % len(C))
tot = sum(1 for e, z, off, db, dt in C if off) \
    + sum(1 for e, z, off, db, dt in C if db or dt)

bad_off, bad_diag = [], []
for e, z, off, db, dt in C:
    if off:
        s = sp.expand(sum(((-1) ** dot(z, S1[t])) * sp.conjugate(cv[i]) * dv[t]
                          for i, t in off))
        if sp.simplify(s) != 0:
            bad_off.append((e, z, sp.simplify(s)))
    if db or dt:
        b = sum(((-1) ** dot(z, S0[i])) * sp.conjugate(cv[k]) * cv[i]
                for k, i in db)
        u = sum(((-1) ** dot(z, S1[j])) * sp.conjugate(dv[k]) * dv[j]
                for k, j in dt)
        if sp.simplify(sp.expand(b - u)) != 0:
            bad_diag.append((e, z, sp.simplify(sp.expand(b - u))))

print()
print('off-diagonal  <0|E|1> = 0      : %d checked, %d violated'
      % (sum(1 for x in C if x[2]), len(bad_off)))
print('diagonal      <0|E|0> = <1|E|1>: %d checked, %d violated'
      % (sum(1 for x in C if x[3] or x[4]), len(bad_diag)))
for e, z, v in (bad_off + bad_diag)[:6]:
    print('   VIOLATED  flip=%s dress=%s  residual %s' % (e, z, v))
if not bad_off and not bad_diag and n0 == 1 and n1 == 1:
    print()
    print('>>> the witness is an EXACT ((6,2,3)) code, verified symbolically.')
