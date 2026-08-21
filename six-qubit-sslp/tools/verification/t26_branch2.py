"""Task 3 (fast): which R_g = 0 branches, and which axis branches, are compatible
with the verified facts?

Two fact sets are used:
   FACTS      = (M) (N) (E) (A) (T2) (R1) (R2)          -- what the argument has
   FACTS+R3   = FACTS plus the six weight-one scalar relations that R1 u R2 miss
"""
import sys, time
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from itertools import combinations

import numpy as np
from scipy.optimize import least_squares

import t26_facts_fast as F

rs = np.random.RandomState(4242)


def go(extra_zero=(), use_R3=False, nstart=250, nfev=1200):
    M, c = F.build(extra_zero, use_R3)
    r = lambda x: np.einsum('kij,i,j->k', M, x, x) + c
    j = lambda x: 2.0 * np.einsum('kij,j->ki', M, x)
    best, bx = np.inf, None
    for k in range(nstart):
        x0 = rs.randn(64) * rs.choice([0.15, 0.25, 0.35, 0.5, 0.8])
        s = least_squares(r, x0, jac=j, method='lm', xtol=1e-15, ftol=1e-15,
                          gtol=1e-15, max_nfev=nfev)
        v = np.linalg.norm(s.fun)
        if v < best:
            best, bx = v, s.x.copy()
    return best, bx


def dump(x):
    C, D = F.report(x)
    P = np.round([np.vdot(C[i], C[i]).real for i in range(8)], 5)
    X6 = np.round(np.abs([np.vdot(C[6], D[i]) for i in range(6)]), 5)
    X7 = np.round(np.abs([np.vdot(C[7], D[i]) for i in range(6)]), 5)
    cr = abs(C[6][0] * C[7][1] - C[6][1] * C[7][0])
    return P, X6, X7, cr


def line(tag, extra, R3=False, ns=400):
    t0 = time.time()
    v, x = go(extra, R3, ns)
    st = 'FEASIBLE  ' if v < 1e-8 else 'infeasible'
    out = '  %-40s %s  resid %.3e  (%.0fs)' % (tag, st, v, time.time() - t0)
    print(out)
    if v < 1e-8:
        P, X6, X7, cr = dump(x)
        print('        P=%s  |C6xC7|=%.2e' % (P, cr))
        print('        |X6|=%s  |X7|=%s' % (X6, X7))
    return v


ODD, EVEN = [1, 3, 5], [0, 2, 4]

print('=== A. base facts model, no branch constraint ===')
line('FACTS', (), False, 300)
line('FACTS + R3', (), True, 300)

print()
print('=== B. R_g = 0 branches (needed for the J-orthogonality lemma) ===')
for j in (6, 7):
    for g in range(3):
        line('FACTS, R_%d^{(%d)} = 0' % (g, j), [(j, 2 * g), (j, 2 * g + 1)], False, 250)

print()
print('=== C. axis branches, all R_g nonzero ===')
for tag, ex in [('aligned  odd(6) & odd(7)', [(6, i) for i in ODD] + [(7, i) for i in ODD]),
                ('aligned  even(6) & even(7)', [(6, i) for i in EVEN] + [(7, i) for i in EVEN]),
                ('MIXED    odd(6) & even(7)', [(6, i) for i in ODD] + [(7, i) for i in EVEN]),
                ('MIXED    even(6) & odd(7)', [(6, i) for i in EVEN] + [(7, i) for i in ODD]),
                ('odd(6) only', [(6, i) for i in ODD]),
                ('even(6) only', [(6, i) for i in EVEN])]:
    line('FACTS, ' + tag, ex, False, 250)
