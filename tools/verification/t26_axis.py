"""Extra: does the mixed-axis branch survive the verified facts?

The cross-anchor contraction the repair proposes is a CONTRACTION OF R1 using R2,
so it is a logical consequence of facts already in the model below.  Therefore:
  * if the mixed branch is FEASIBLE here, no consequence of (M,N,E,A,T2,R1,R2)
    -- in particular not the cross-anchor contraction -- can close it;
  * if it is INFEASIBLE here, some consequence of those facts does close it.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import numpy as np
from scipy.optimize import least_squares

from t26_branch_core import unpack, base_res, NV


def search(extra, nstart=200, seed=5, scale=0.35):
    rs = np.random.RandomState(seed)

    def f(x):
        C, D = unpack(x)
        r = list(base_res(C, D))
        for (j, i) in extra:
            v = np.vdot(C[j], D[i])
            r += [v.real, v.imag]
        return np.array(r)
    best, bx = np.inf, None
    for _ in range(nstart):
        sol = least_squares(f, rs.randn(NV) * scale, method='lm', xtol=1e-15,
                            ftol=1e-15, gtol=1e-15, max_nfev=8000)
        v = np.linalg.norm(sol.fun)
        if v < best:
            best, bx = v, sol.x.copy()
    return best, bx


ODD, EVEN = [1, 3, 5], [0, 2, 4]


def show(name, extra, seed):
    v, x = search(extra, seed=seed)
    C, D = unpack(x)
    P = np.round([np.vdot(C[i], C[i]).real for i in range(8)], 5)
    # is C_6 parallel to C_7 ?
    par = abs(C[6][0] * C[7][1] - C[6][1] * C[7][0])
    X6 = np.round(np.abs([np.vdot(C[6], D[i]) for i in range(6)]), 6)
    X7 = np.round(np.abs([np.vdot(C[7], D[i]) for i in range(6)]), 6)
    print('  %-34s resid %.3e  %-11s' % (name, v, 'FEASIBLE' if v < 1e-8 else 'INFEASIBLE'))
    if v < 1e-8:
        print('        P=%s' % P)
        print('        |C_6 x C_7| = %.6e   (0 <=> C_6 parallel to C_7)' % par)
        print('        |X^(6)| = %s' % X6)
        print('        |X^(7)| = %s' % X7)
    return v


print('=== axis branches (all three R_g nonzero at each anchor) ===')
show('aligned  odd(6) & odd(7)', [(6, i) for i in ODD] + [(7, i) for i in ODD], 101)
show('aligned  even(6) & even(7)', [(6, i) for i in EVEN] + [(7, i) for i in EVEN], 103)
show('MIXED    odd(6) & even(7)', [(6, i) for i in ODD] + [(7, i) for i in EVEN], 107)
show('MIXED    even(6) & odd(7)', [(6, i) for i in EVEN] + [(7, i) for i in ODD], 109)
print()
print('=== single-anchor axis only (no constraint at the other anchor) ===')
show('odd(6) only', [(6, i) for i in ODD], 113)
show('even(6) only', [(6, i) for i in EVEN], 127)
