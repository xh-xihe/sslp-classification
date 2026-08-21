"""Orbit 31: are the phase branches satisfiable under the CORRECTED families?"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import itertools

import numpy as np
from scipy.optimize import least_squares


def resid(v, rho):
    c = (v[:16] + 1j * v[16:32]).reshape(4, 4)      # rows A,B1,B2,B3 ; cols 0..3
    a, b = c[0], c[1:]
    out = []
    for i in range(3):                               # family 1
        s = sum(np.conj(rho[e]) * a[e] * b[i, e] for e in range(4))
        out += [s.real, s.imag]
    for e, f in itertools.combinations(range(4), 2):  # family 2
        k = np.conj(rho[e]) + np.conj(rho[f])
        for i, j in itertools.combinations(range(3), 2):
            s = k * (b[i, e] * b[j, f] + b[i, f] * b[j, e])
            out += [s.real, s.imag]
    for e, f in itertools.combinations(range(4), 2):  # family 3, CORRECTED
        t = rho[f] * np.conj(rho[e]) - 1
        G = sum(c[r, e] * np.conj(c[r, f]) for r in range(4))
        H = sum(c[r, e] * np.conj(c[r, f]) for r in range(1, 4)) - c[0, e] * np.conj(c[0, f])
        out += [(G * t).real, (H * t).imag]
    P = np.abs(c) ** 2
    for i in range(3):
        out.append(P[1 + i].sum() - 0.25)
    for e in range(4):
        out.append(P[0, e] - (P[1:, e].sum() - 0.125))
    return np.array(out)


CASES = {
    'all equal  (s,s,s,s)': [1, 1, 1, 1],
    'K22        (s,s,-s,-s)': [1, 1, -1, -1],
    'K13        (s,s,s,-s)': [1, 1, 1, -1],
    '2 edges    (s,-s,t,-t)': [1, -1, 1j, -1j],
    '1 edge     (s,-s,t,u)': [1, -1, 1j, np.exp(0.7j)],
    'generic    (all distinct)': [1, np.exp(0.9j), np.exp(1.9j), np.exp(2.7j)],
}
rng = np.random.default_rng(17)
for nm, ph in CASES.items():
    ph = np.array(ph, dtype=complex)
    best = None
    for _ in range(120):
        r = least_squares(lambda v: resid(v, ph), rng.normal(size=32) * 0.3,
                          xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=600)
        val = float(np.sum(r.fun ** 2))
        if best is None or val < best:
            best = val
    print('  %-26s best residual %.3e -> %s'
          % (nm, best, 'SATISFIABLE' if best < 1e-16 else 'EXCLUDED'), flush=True)
