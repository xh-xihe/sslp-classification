"""Orbit 29: does the moment system plus the modulus consequences force the
probabilities in each X5X6 pair to agree?"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import numpy as np
from scipy.optimize import least_squares

from relgen import setup, two_term
from scan import ind
from itertools import combinations

a, q, d, S0, S1 = setup(29)
n0, n1 = len(S0), len(S1)
EDGES = sorted({(i // 2, t // 2) for i, t, k, u, sg, e in two_term(S0, S1) if sg})

rows, rhs = [], []
rows.append([1] * n0 + [0] * n1); rhs.append(1)
rows.append([0] * n0 + [1] * n1); rhs.append(1)
for i in range(6):
    rows.append([ind(x, i) for x in S0] + [-ind(y, i) for y in S1]); rhs.append(0)
for i, j in combinations(range(6), 2):
    rows.append([ind(x, i) * ind(x, j) for x in S0] + [-ind(y, i) * ind(y, j) for y in S1])
    rhs.append(0)
A, b = np.array(rows, float), np.array(rhs, float)


def resid(v):
    w = v ** 2                       # enforce nonnegativity by squaring
    out = list(A @ w - b)
    for m, n in EDGES:
        out.append(w[2 * m] * w[n0 + 2 * n] - w[2 * m + 1] * w[n0 + 2 * n + 1])
    return np.array(out)


rng = np.random.default_rng(3)
found, viol = 0, 0
worst = 0.0
for _ in range(400):
    r = least_squares(resid, rng.random(n0 + n1) * 0.4, xtol=1e-14, ftol=1e-14,
                      gtol=1e-14, max_nfev=3000)
    if np.sum(r.fun ** 2) > 1e-18:
        continue
    found += 1
    w = r.x ** 2
    gap = max(max(abs(w[2 * m] - w[2 * m + 1]) for m in range(n0 // 2)),
              max(abs(w[n0 + 2 * n] - w[n0 + 2 * n + 1]) for n in range(n1 // 2)))
    worst = max(worst, gap)
    if gap > 1e-7:
        viol += 1
print('solutions found: %d   pair-equality violations: %d   worst gap %.3e'
      % (found, viol, worst))
print('EDGES:', EDGES)
