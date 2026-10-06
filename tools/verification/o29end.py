"""Orbit 29 endgame: with equal probabilities in every pair and one common pair
phase, do the equations touching the pinned pair (111100,111111) contradict?

Amplitudes are parameterised as  c_{2m+1} = beta * c_{2m}  for m != 7 and
c_15 = eta * c_14, with d_{2n+1} = -beta * d_{2n}.  The free data are the
moduli (a point of the 3-simplex), the phases of each pair leader, beta, and
eta.  We ask the optimizer to satisfy every weight-<=2 KL condition.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import numpy as np
from scipy.optimize import least_squares

from relgen import setup
from scan import dot
from kl import conditions

a, q, d, S0, S1 = setup(29)
n0, n1 = len(S0), len(S1)
C = conditions(S0, S1)


def build(v):
    """v = [8 bottom leaders (re,im)] + [8 top leaders] + [beta] + [eta]."""
    k = 0
    cl = v[k:k + 16:2] + 1j * v[k + 1:k + 16:2]; k += 16
    dl = v[k:k + 16:2] + 1j * v[k + 1:k + 16:2]; k += 16
    beta = v[k] + 1j * v[k + 1]; k += 2
    eta = v[k] + 1j * v[k + 1]
    c = np.zeros(n0, complex); dd = np.zeros(n1, complex)
    for m in range(8):
        c[2 * m] = cl[m]
        c[2 * m + 1] = (eta if m == 7 else beta) * cl[m]
    for n in range(8):
        dd[2 * n] = dl[n]
        dd[2 * n + 1] = -beta * dl[n]
    return c, dd, beta, eta


def resid(v):
    c, dd, beta, eta = build(v)
    out = [np.sum(np.abs(c) ** 2) - 1.0, np.sum(np.abs(dd) ** 2) - 1.0,
           abs(beta) ** 2 - 1.0, abs(eta) ** 2 - 1.0]
    for e, z, off, db, dt in C:
        if off:
            s = sum(((-1) ** dot(z, S1[t])) * np.conj(c[i]) * dd[t] for i, t in off)
            out += [s.real, s.imag]
        if db or dt:
            b = sum(((-1) ** dot(z, S0[i])) * np.conj(c[k]) * c[i] for k, i in db)
            u = sum(((-1) ** dot(z, S1[j])) * np.conj(dd[k]) * dd[j] for k, j in dt)
            out += [(b - u).real, (b - u).imag]
    return np.array(out)


rng = np.random.default_rng(11)
best = None
for _ in range(25):
    r = least_squares(resid, rng.normal(size=36) * 0.3, xtol=1e-15, ftol=1e-15,
                      gtol=1e-15, max_nfev=1200)
    v = float(np.sum(r.fun ** 2))
    if best is None or v < best:
        best, bx = v, r.x
print('orbit 29, pair-phase ansatz: best residual %.4e -> %s'
      % (best, 'SATISFIABLE (ansatz too weak)' if best < 1e-16 else 'CONTRADICTORY'))
c, dd, beta, eta = build(bx)
print('beta = %.4f%+.4fi   eta = %.4f%+.4fi' % (beta.real, beta.imag, eta.real, eta.imag))
