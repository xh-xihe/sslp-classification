"""End-to-end numerical check of the 22 newly excluded orbits.

For each orbit we minimise the residual of the COMPLETE weight-<=2
Knill-Laflamme system over all complex amplitudes.  Claimed no-go orbits must
fail to reach zero; the realizable orbits 7, 8, 9, 36 are included as POSITIVE
controls -- the optimiser must find exact solutions for them, otherwise the
test proves nothing.
"""
import sys

import numpy as np
from scipy.optimize import least_squares

sys.path.insert(0, 'tools/core')
from orbit import fiber
from scan import dot
from kl import conditions

# (q, angle vector, delta) exactly as printed in the paper
NEW = [
    (5, 3, [0, 0, 1, 1, 1, 1], 1), (6, 3, [0, 1, 1, 1, 1, 1], 1),
    (47, 6, [1, 1, 1, 1, 2, 2], 2), (48, 6, [1, 1, 1, 2, 2, 2], 2),
    (49, 6, [1, 1, 1, 3, 3, 5], 2), (50, 6, [1, 1, 1, 3, 4, 4], 2),
    (51, 6, [1, 1, 2, 3, 3, 4], 2), (52, 6, [1, 2, 3, 3, 4, 4], 2),
    (12, 4, [0, 1, 1, 1, 1, 2], 2), (13, 4, [0, 1, 1, 1, 2, 2], 2),
    (14, 4, [0, 1, 1, 2, 2, 2], 2), (15, 4, [0, 1, 2, 2, 2, 2], 2),
    (17, 4, [1, 1, 1, 1, 1, 1], 2), (18, 4, [1, 1, 1, 1, 1, 2], 2),
    (19, 4, [1, 1, 1, 1, 2, 2], 2), (20, 4, [1, 1, 1, 2, 2, 2], 2),
    (24, 4, [1, 2, 2, 2, 2, 3], 2), (41, 6, [1, 1, 1, 1, 2, 3], 3),
    (42, 6, [1, 1, 1, 1, 3, 3], 3), (43, 6, [1, 1, 1, 2, 3, 3], 3),
    (44, 6, [1, 1, 2, 3, 3, 4], 3), (46, 6, [1, 2, 2, 2, 3, 3], 3),
]
CONTROLS = [
    (7, 3, [0, 1, 1, 1, 2, 2], 1), (8, 3, [1, 1, 1, 1, 1, 1], 1),
    (9, 3, [1, 1, 1, 1, 1, 2], 1), (36, 5, [1, 1, 1, 2, 2, 4], 1),
]


def residual(S0, S1):
    n0, n1 = len(S0), len(S1)
    C = conditions(S0, S1)

    def f(p):
        c = p[:n0] + 1j * p[n0:2 * n0]
        d = p[2 * n0:2 * n0 + n1] + 1j * p[2 * n0 + n1:]
        out = [np.sum(np.abs(c) ** 2) - 1.0, np.sum(np.abs(d) ** 2) - 1.0]
        for e, z, off, db, dt in C:
            if off:
                s = sum(((-1) ** dot(z, S1[t])) * np.conj(c[i]) * d[t]
                        for i, t in off)
                out += [s.real, s.imag]
            if db or dt:
                b = sum(((-1) ** dot(z, S0[i])) * np.conj(c[k]) * c[i]
                        for k, i in db)
                u = sum(((-1) ** dot(z, S1[j])) * np.conj(d[k]) * d[j]
                        for k, j in dt)
                out += [(b - u).real, (b - u).imag]
        return np.array(out)
    return f, 2 * (n0 + n1), len(C)


def run(tag, table, tries=40):
    rng = np.random.default_rng(11)
    print('%s' % tag)
    for oid, q, a, d in table:
        S0, S1 = fiber(a, q, 0), fiber(a, q, d)
        if not S0 or not S1:
            print('  orbit %-3d EMPTY FIBER' % oid)
            continue
        f, dim, nc = residual(S0, S1)
        best = np.inf
        for _ in range(tries):
            r = least_squares(f, rng.normal(size=dim) * 0.4, xtol=1e-15,
                              ftol=1e-15, gtol=1e-15)
            best = min(best, float(np.sum(r.fun ** 2)))
            if best < 1e-20:
                break
        verdict = 'SOLVABLE   ' if best < 1e-16 else 'no solution'
        print('  orbit %-3d  fibers %2d+%-2d  %3d Pauli conds   best residual '
              '%.3e   %s' % (oid, len(S0), len(S1), nc, best, verdict))


run('POSITIVE CONTROLS (paper says these are realizable -- must be SOLVABLE):',
    CONTROLS)
print()
run('NEWLY EXCLUDED ORBITS (paper proves no-go -- must be unsolvable):', NEW)
