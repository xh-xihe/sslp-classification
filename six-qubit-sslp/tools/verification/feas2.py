"""Feasibility of the COMPLETE weight-<=2 Knill-Laflamme system.

Certified orbits are included as controls: a kernel-checked Lean proof says they
have no solution, so the optimizer must fail on them.
"""
import sys
sys.path.insert(0, '.')
import numpy as np
from scipy.optimize import least_squares
from orbit import fiber
from scan import ORBITS, dot
from kl import conditions
from propagate import pdim, DLP


def make(S0, S1):
    n0, n1 = len(S0), len(S1)
    C = conditions(S0, S1)

    def f(p):
        c = p[:n0] + 1j * p[n0:2 * n0]
        d = p[2 * n0:2 * n0 + n1] + 1j * p[2 * n0 + n1:]
        out = [np.sum(np.abs(c) ** 2) - 1.0, np.sum(np.abs(d) ** 2) - 1.0]
        for e, z, off, db, dt in C:
            if off:
                s = sum(((-1) ** dot(z, S1[t])) * np.conj(c[i]) * d[t] for i, t in off)
                out += [s.real, s.imag]
            if db or dt:
                b = sum(((-1) ** dot(z, S0[i])) * np.conj(c[k]) * c[i] for k, i in db)
                u = sum(((-1) ** dot(z, S1[j])) * np.conj(d[k]) * d[j] for k, j in dt)
                out += [(b - u).real, (b - u).imag]
        return np.array(out)
    return f, 2 * (n0 + n1)


if __name__ == '__main__':
    rng = np.random.default_rng(7)
    todo = [int(a) for a in sys.argv[1:]] or [25, 38, 33, 31, 26, 29]
    for oid in todo:
        a, q, sz = ORBITS[oid]
        S0 = fiber(a, q, 0)
        ds = [x for x in range(1, q) if fiber(a, q, x)
              and (sz is None or (len(S0), len(fiber(a, q, x))) == sz)
              and pdim(S0, fiber(a, q, x)) == DLP[oid]]
        S1 = fiber(a, q, ds[0])
        f, dim = make(S0, S1)
        best = None
        for _ in range(30):
            r = least_squares(f, rng.normal(size=dim) * 0.4,
                              xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=2000)
            v = float(np.sum(r.fun ** 2))
            if best is None or v < best:
                best = v
        tag = 'certified no-go' if oid in (25, 38) else 'TARGET'
        print('orbit %-3d [%-15s] delta=%d  best residual %.3e  -> %s'
              % (oid, tag, ds[0], best,
                 'satisfiable' if best < 1e-16 else 'EXCLUDED'), flush=True)
