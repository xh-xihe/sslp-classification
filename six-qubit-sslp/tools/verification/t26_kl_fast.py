"""Task 4, fast version: every KL residual is a real quadratic form x^T M x + const,
so the Jacobian 2 M x is exact and least_squares converges quickly.

x = (Re c, Im c, Re d, Im d) in R^64,  c indexed by S0, d by S1.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import time

import numpy as np
from scipy.optimize import least_squares

from o26 import S0, S1
from scan import dot
from kl import conditions

n0, n1 = len(S0), len(S1)
N = 2 * (n0 + n1)
A_ = lambda j: j                 # Re c_j
B_ = lambda j: n0 + j            # Im c_j
E_ = lambda t: 2 * n0 + t        # Re d_t
F_ = lambda t: 2 * n0 + n1 + t   # Im d_t

Ms, cs, lab = [], [], []


def add(pairs, const, tag):
    M = np.zeros((N, N))
    for (p, q), w in pairs:
        M[p, q] += w / 2.0
        M[q, p] += w / 2.0
    Ms.append(M); cs.append(const); lab.append(tag)


# normalisations
add([((A_(j), A_(j)), 1.0) for j in range(n0)] + [((B_(j), B_(j)), 1.0) for j in range(n0)],
    -1.0, 'norm0')
add([((E_(t), E_(t)), 1.0) for t in range(n1)] + [((F_(t), F_(t)), 1.0) for t in range(n1)],
    -1.0, 'norm1')

CONDS = conditions(S0, S1)
noff = ndia = 0
for e, z, off, db, dt in CONDS:
    if off:                       # <psi0| X^e Z^z |psi1> = 0
        re, im = [], []
        for j, t in off:
            s = (-1.0) ** dot(z, S1[t])
            re += [((A_(j), E_(t)), s), ((B_(j), F_(t)), s)]
            im += [((A_(j), F_(t)), s), ((B_(j), E_(t)), -s)]
        add(re, 0.0, ('off_re', e, z)); add(im, 0.0, ('off_im', e, z)); noff += 1
    if db or dt:                  # <psi0|E|psi0> - <psi1|E|psi1> = 0
        re, im = [], []
        for j, i in db:
            s = (-1.0) ** dot(z, S0[i])
            re += [((A_(j), A_(i)), s), ((B_(j), B_(i)), s)]
            im += [((A_(j), B_(i)), s), ((B_(j), A_(i)), -s)]
        for j, i in dt:
            s = (-1.0) ** dot(z, S1[i])
            re += [((E_(j), E_(i)), -s), ((F_(j), F_(i)), -s)]
            im += [((E_(j), F_(i)), -s), ((F_(j), E_(i)), s)]
        add(re, 0.0, ('dia_re', e, z)); add(im, 0.0, ('dia_im', e, z)); ndia += 1

M = np.array(Ms); cvec = np.array(cs)
print('Paulis %d   off-diagonal eqs %d   diagonal eqs %d   real residuals %d'
      % (len(CONDS), noff, ndia, M.shape[0]))


def resid(x):
    return np.einsum('kij,i,j->k', M, x, x) + cvec


def jac(x):
    return 2.0 * np.einsum('kij,j->ki', M, x)


NST = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
rs = np.random.RandomState(20260819)
best, bx = np.inf, None
t0 = time.time()
hist = []
for k in range(NST):
    x0 = rs.randn(N)
    x0[:2 * n0] /= np.linalg.norm(x0[:2 * n0])
    x0[2 * n0:] /= np.linalg.norm(x0[2 * n0:])
    sol = least_squares(resid, x0, jac=jac, method='lm', xtol=1e-15, ftol=1e-15,
                        gtol=1e-15, max_nfev=5000)
    v = np.linalg.norm(sol.fun)
    hist.append(v)
    if v < best:
        best, bx = v, sol.x.copy()
print('%d starts in %.1f s' % (NST, time.time() - t0))
h = np.sort(np.array(hist))
print('residual 2-norm  min %.6e   1%%-ile %.6e   median %.6e'
      % (h[0], h[max(0, len(h) // 100)], h[len(h) // 2]))
print('BEST residual 2-norm : %.8e' % best)
print('BEST residual max-abs: %.8e' % np.max(np.abs(resid(bx))))
print('norms at best point  : %.8f  %.8f'
      % (np.sum(bx[:2 * n0] ** 2), np.sum(bx[2 * n0:] ** 2)))

# polish the best point hard, from several perturbations
print()
print('--- polishing the best point ---')
pb = best
for s in (1e-1, 1e-2, 1e-3):
    for _ in range(80):
        sol = least_squares(resid, bx + s * rs.randn(N), jac=jac, method='lm',
                            xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=20000)
        pb = min(pb, np.linalg.norm(sol.fun))
print('best after polishing : %.8e' % pb)

# --- controls ---------------------------------------------------------------
print()
print('--- control A: drop the off-diagonal equations (diagonal-only relaxation) ---')
keep = [k for k in range(M.shape[0]) if lab[k] in ('norm0', 'norm1') or lab[k][0].startswith('dia')]
Md, cd = M[keep], cvec[keep]
rd = lambda x: np.einsum('kij,i,j->k', Md, x, x) + cd
jd = lambda x: 2.0 * np.einsum('kij,j->ki', Md, x)
bd = np.inf
for k in range(300):
    sol = least_squares(rd, rs.randn(N), jac=jd, method='lm', xtol=1e-15, ftol=1e-15,
                        gtol=1e-15, max_nfev=5000)
    bd = min(bd, np.linalg.norm(sol.fun))
print('best residual: %.8e  (expect ~0 -- the solver and model are not the obstruction)' % bd)

print()
print('--- control B: weight-<=1 Paulis only (a genuinely solvable subsystem?) ---')
keep = [k for k in range(M.shape[0]) if lab[k] in ('norm0', 'norm1')
        or (isinstance(lab[k], tuple) and len(set(i for i in range(6) if lab[k][1][i] == '1')
                                              | set(i for i in range(6) if lab[k][2][i] == '1')) <= 1)]
M1, c1 = M[keep], cvec[keep]
r1 = lambda x: np.einsum('kij,i,j->k', M1, x, x) + c1
j1 = lambda x: 2.0 * np.einsum('kij,j->ki', M1, x)
b1 = np.inf
for k in range(300):
    sol = least_squares(r1, rs.randn(N), jac=j1, method='lm', xtol=1e-15, ftol=1e-15,
                        gtol=1e-15, max_nfev=5000)
    b1 = min(b1, np.linalg.norm(sol.fun))
print('weight-<=1 subsystem, %d residuals, best: %.8e' % (M1.shape[0], b1))
