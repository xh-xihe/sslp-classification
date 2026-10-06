"""Task 4: is orbit 26 really excluded by the FULL weight-<=2 Knill-Laflamme system?

Unknowns: c_x for x in S0 (16 complex), d_y for y in S1 (16 complex).
For every Pauli E = X^e Z^z with |supp(e) u supp(z)| <= 2:
    off-diagonal   <psi0|E|psi1> = 0
    diagonal       <psi0|E|psi0> = <psi1|E|psi1>
plus <psi0|psi0> = <psi1|psi1> = 1.
Least squares from many random starts; a residual near 0 would mean the orbit is
NOT excluded.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import numpy as np
from scipy.optimize import least_squares

from o26 import S0, S1
from scan import dot
from kl import conditions

n0, n1 = len(S0), len(S1)
CONDS = conditions(S0, S1)
print('admissible Paulis (weight <= 2): %d' % len(CONDS))

OFF, DIA = [], []
for e, z, off, db, dt in CONDS:
    if off:
        OFF.append((np.array([o[0] for o in off]), np.array([o[1] for o in off]),
                    np.array([(-1.0) ** dot(z, S1[t]) for _, t in off])))
    rb = (np.array([p[0] for p in db]), np.array([p[1] for p in db]),
          np.array([(-1.0) ** dot(z, S0[i]) for _, i in db])) if db else None
    rt = (np.array([p[0] for p in dt]), np.array([p[1] for p in dt]),
          np.array([(-1.0) ** dot(z, S1[j]) for _, j in dt])) if dt else None
    if rb or rt:
        DIA.append((rb, rt))
print('non-trivial off-diagonal equations: %d' % len(OFF))
print('non-trivial diagonal   equations: %d' % len(DIA))
print('real residual count: %d' % (2 * len(OFF) + 2 * len(DIA) + 2))


def unpack(x):
    c = x[0:n0] + 1j * x[n0:2 * n0]
    d = x[2 * n0:2 * n0 + n1] + 1j * x[2 * n0 + n1:2 * n0 + 2 * n1]
    return c, d


def resid(x):
    c, d = unpack(x)
    out = [np.sum(np.abs(c) ** 2) - 1.0, np.sum(np.abs(d) ** 2) - 1.0]
    for jj, tt, sg in OFF:
        v = np.sum(sg * np.conj(c[jj]) * d[tt])
        out += [v.real, v.imag]
    for rb, rt in DIA:
        v = 0j
        if rb is not None:
            v += np.sum(rb[2] * np.conj(c[rb[0]]) * c[rb[1]])
        if rt is not None:
            v -= np.sum(rt[2] * np.conj(d[rt[0]]) * d[rt[1]])
        out += [v.real, v.imag]
    return np.array(out)


rs = np.random.RandomState(20260819)
best, bestx = np.inf, None
NSTART = int(sys.argv[1]) if len(sys.argv) > 1 else 400
for k in range(NSTART):
    x0 = rs.randn(2 * (n0 + n1))
    c, d = unpack(x0)
    x0[0:2 * n0] /= np.linalg.norm(c)
    x0[2 * n0:] /= np.linalg.norm(d)
    sol = least_squares(resid, x0, method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15,
                        max_nfev=20000)
    v = np.linalg.norm(sol.fun)
    if v < best:
        best, bestx = v, sol.x.copy()
print()
print('starts: %d' % NSTART)
print('BEST residual 2-norm over all starts: %.6e' % best)
print('BEST residual max-abs               : %.6e' % np.max(np.abs(resid(bestx))))
c, d = unpack(bestx)
print('||c||^2 = %.6f   ||d||^2 = %.6f' % (np.sum(abs(c) ** 2), np.sum(abs(d) ** 2)))

# --- control: the same code on an orbit that IS known to admit a solution -----
print()
print('--- control: relax to the DIAGONAL-only system (should be solvable) ---')
def resid_diag(x):
    c, d = unpack(x)
    out = [np.sum(np.abs(c) ** 2) - 1.0, np.sum(np.abs(d) ** 2) - 1.0]
    for rb, rt in DIA:
        v = 0j
        if rb is not None:
            v += np.sum(rb[2] * np.conj(c[rb[0]]) * c[rb[1]])
        if rt is not None:
            v -= np.sum(rt[2] * np.conj(d[rt[0]]) * d[rt[1]])
        out += [v.real, v.imag]
    return np.array(out)

bd = np.inf
for k in range(60):
    x0 = rs.randn(2 * (n0 + n1))
    sol = least_squares(resid_diag, x0, method='lm', xtol=1e-15, ftol=1e-15,
                        gtol=1e-15, max_nfev=20000)
    bd = min(bd, np.linalg.norm(sol.fun))
print('best residual for diagonal-only relaxation: %.6e' % bd)
