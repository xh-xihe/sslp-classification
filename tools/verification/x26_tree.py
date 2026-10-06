"""Exhaustiveness of the case tree, plus an INDEPENDENT numerical cross-check.

Part A enumerates every possible pair (Z_6, Z_7) of subsets of {0,1,2} and shows
each one is caught by exactly one branch of the tree.

Part B re-runs the verified-facts least-squares model of t26_facts_fast with the
branch hypotheses imposed as extra quadratic equations.  This is a completely
independent route: it does not use any of the reasoning in x26_branches.py.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from itertools import combinations

import numpy as np

print('=' * 76)
print('PART A.  every (Z_6, Z_7) is covered exactly once')
print('=' * 76)
subs = [frozenset(s) for k in range(4) for s in combinations((0, 1, 2), k)]


def branch(z6, z7):
    hit = []
    if len(z6) >= 2 or len(z7) >= 2:
        hit.append(1)
    if len(z6) <= 1 and len(z7) <= 1 and (z6 & z7):
        hit.append(2)
    if len(z6) <= 1 and len(z7) <= 1 and not (z6 & z7) and (z6 or z7):
        hit.append(3)
    if not z6 and not z7:
        hit.append(4)
    return hit


bad = []
for z6 in subs:
    for z7 in subs:
        h = branch(z6, z7)
        if len(h) != 1:
            bad.append((sorted(z6), sorted(z7), h))
print('  %d ordered pairs (Z_6, Z_7) enumerated' % (len(subs) ** 2))
print('  pairs hit by a number of branches other than exactly one:', bad)
tally = {}
for z6 in subs:
    for z7 in subs:
        tally.setdefault(branch(z6, z7)[0], 0)
        tally[branch(z6, z7)[0]] += 1
print('  branch occupancy:', dict(sorted(tally.items())))
print('  branch 4 splits further into 4a (mixed axes) and 4b (aligned axes),')
print('  an exhaustive two-way split because each anchor picks exactly one axis.')

print()
print('=' * 76)
print('PART B.  independent numerical infeasibility of each branch hypothesis')
print('=' * 76)
import t26_facts_fast as F
from scipy.optimize import least_squares

rs = np.random.RandomState(20260819)


def go(extra_zero, nstart=250, nfev=1500):
    M, c = F.build(list(extra_zero), False)
    r = lambda x: np.einsum('kij,i,j->k', M, x, x) + c
    j = lambda x: 2.0 * np.einsum('kij,j->ki', M, x)
    best = np.inf
    for _ in range(nstart):
        x0 = rs.randn(64) * rs.choice([0.15, 0.25, 0.35, 0.5, 0.8])
        s = least_squares(r, x0, jac=j, method='lm', xtol=1e-15, ftol=1e-15,
                          gtol=1e-15, max_nfev=nfev)
        best = min(best, np.linalg.norm(s.fun))
    return best


ODD, EVEN = [1, 3, 5], [0, 2, 4]
CASES = [
    ('BRANCH 1  Z_6 contains {0,1}', [(6, 0), (6, 1), (6, 2), (6, 3)]),
    ('BRANCH 2  Z_6 = Z_7 = {0}', [(6, 0), (6, 1), (7, 0), (7, 1)]),
    ('BRANCH 3  Z_6 = {0} (d_0 free)', [(6, 0), (6, 1)]),
    ('BRANCH 4a MIXED odd(6), even(7)', [(6, i) for i in ODD] + [(7, i) for i in EVEN]),
    ('BRANCH 4a MIXED even(6), odd(7)', [(6, i) for i in EVEN] + [(7, i) for i in ODD]),
    ('BRANCH 4b ALIGNED odd(6), odd(7)', [(6, i) for i in ODD] + [(7, i) for i in ODD]),
    ('BRANCH 4b ALIGNED even(6), even(7)', [(6, i) for i in EVEN] + [(7, i) for i in EVEN]),
]
for tag, ex in CASES:
    v = go(ex)
    print('  %-38s  %s   best residual 2-norm = %.4e'
          % (tag, 'FEASIBLE' if v < 1e-8 else 'infeasible', v))

print()
print('  positive control (the machinery does find solutions when they exist):')
M, c = F.build([], False)
Msub, csub = M[:33], c[:33]          # (M) + (N) + (E) only, no (A)/(T2)/R1/R2
r = lambda x: np.einsum('kij,i,j->k', Msub, x, x) + csub
j = lambda x: 2.0 * np.einsum('kij,j->ki', Msub, x)
best = np.inf
for _ in range(60):
    s = least_squares(r, rs.randn(64) * 0.3, jac=j, method='lm', xtol=1e-15,
                      ftol=1e-15, gtol=1e-15, max_nfev=2000)
    best = min(best, np.linalg.norm(s.fun))
print('    facts (M)+(N)+(E) alone, no branch constraint: residual %.3e' % best)
