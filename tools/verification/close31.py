"""Orbit 31: solve directly in the phase parametrisation against the RAW
Knill-Laflamme conditions, with the column phases as free unit-modulus unknowns.

No reduced system, no derived families -- this settles satisfiability without
any risk of having mis-derived an intermediate step.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import numpy as np
from scipy.optimize import least_squares

from o31 import S0, S1, POS
from scan import dot
from kl import conditions

COND = conditions(S0, S1)
comp = lambda s: ''.join('1' if ch == '0' else '0' for ch in s)
TOPIDX = [S1.index(comp(S0[v])) for v in range(16)]


def build(v):
    c = (v[:16] + 1j * v[16:32])
    ph = v[32:36] + 1j * v[36:40]
    cv = np.zeros(16, complex)
    dv = np.zeros(16, complex)
    for p in range(16):
        cv[p] = c[p]
        dv[TOPIDX[p]] = ph[POS[p][1]] * np.conj(c[p])
    return cv, dv, ph


def resid(v):
    cv, dv, ph = build(v)
    out = [np.sum(np.abs(cv) ** 2) - 1.0]
    out += [abs(z) ** 2 - 1.0 for z in ph]
    for e, z, off, db, dt in COND:
        if off:
            s = sum(((-1) ** dot(z, S1[t])) * np.conj(cv[i]) * dv[t] for i, t in off)
            out += [s.real, s.imag]
        if db or dt:
            B = sum(((-1) ** dot(z, S0[i])) * np.conj(cv[k]) * cv[i] for k, i in db)
            T = sum(((-1) ** dot(z, S1[j])) * np.conj(dv[k]) * dv[j] for k, j in dt)
            out += [(B - T).real, (B - T).imag]
    return np.array(out)


if __name__ == '__main__':
    rng = np.random.default_rng(23)
    best = None
    for _ in range(int(sys.argv[1]) if len(sys.argv) > 1 else 150):
        v0 = np.concatenate([rng.normal(size=32) * 0.3, rng.normal(size=8)])
        r = least_squares(resid, v0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=1200)
        val = float(np.sum(r.fun ** 2))
        if best is None or val < best:
            best, bx = val, r.x
    print('orbit 31, phase parametrisation vs RAW KL: best residual %.4e -> %s'
          % (best, 'SATISFIABLE' if best < 1e-16 else 'EXCLUDED'), flush=True)
    cv, dv, ph = build(bx)
    print('column phases:', np.round(ph, 4))
