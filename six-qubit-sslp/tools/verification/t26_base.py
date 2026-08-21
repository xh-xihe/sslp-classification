"""Is the VERIFIED-FACTS model feasible at all once the full moment-polytope
relation (T2) P_0+P_2+P_4 = 3/8 is included?

Strategy: solve the model WITHOUT (T2) (known easy), then continue (T2) in.
Plus a large multi-scale random search.
"""
import sys, time
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import numpy as np
from scipy.optimize import least_squares

import t26_facts_fast as F

M_noT2 = None


def build_with_target(tgt, extra_zero=(), use_R3=False):
    """same as F.build but with the (T2) constant replaced by tgt (None = drop it)."""
    M, c = F.build(extra_zero, use_R3)
    # (T2) rows sit right after (A); locate them by their constant -0.375
    idx = [k for k in range(len(c)) if abs(c[k] + 0.375) < 1e-12]
    assert len(idx) == 2, idx
    if tgt is None:
        keep = [k for k in range(len(c)) if k not in idx]
        return M[keep], c[keep]
    c = c.copy()
    for k in idx:
        c[k] = -tgt
    return M, c


def mk(M, c):
    return (lambda x: np.einsum('kij,i,j->k', M, x, x) + c,
            lambda x: 2.0 * np.einsum('kij,j->ki', M, x))


def run(M, c, starts, seeds=None, nfev=3000):
    r, j = mk(M, c)
    best, bx = np.inf, None
    for x0 in starts:
        s = least_squares(r, x0, jac=j, method='lm', xtol=1e-15, ftol=1e-15,
                          gtol=1e-15, max_nfev=nfev)
        v = np.linalg.norm(s.fun)
        if v < best:
            best, bx = v, s.x.copy()
    return best, bx


rs = np.random.RandomState(2026)
print('--- (a) facts model WITHOUT (T2) ---')
M0, c0 = build_with_target(None)
b0, x0 = run(M0, c0, [rs.randn(64) * s for s in rs.choice([0.2, 0.35, 0.6, 1.0], 200)])
C, D = F.report(x0)
P = np.array([np.vdot(C[i], C[i]).real for i in range(8)])
print('    best %.3e   P = %s   P0+P2+P4 = %.6f' % (b0, np.round(P, 5), P[[0, 2, 4]].sum()))

print('--- (b) continuation of (T2) from that solution up to 3/8 ---')
x = x0.copy()
cur = P[[0, 2, 4]].sum()
ok = True
for t in np.linspace(0, 1, 41)[1:]:
    tgt = (1 - t) * cur + t * 0.375
    Mt, ct = build_with_target(tgt)
    b, x = run(Mt, ct, [x, x + 0.02 * rs.randn(64), x + 0.05 * rs.randn(64)])
    if b > 1e-9:
        print('    continuation stalled at target %.6f, residual %.3e' % (tgt, b))
        ok = False
        break
if ok:
    C, D = F.report(x)
    P = np.array([np.vdot(C[i], C[i]).real for i in range(8)])
    print('    continuation SUCCEEDED, residual %.3e, P = %s' % (b, np.round(P, 5)))

print('--- (c) big multi-scale random search WITH (T2) ---')
M1, c1 = build_with_target(0.375)
starts = []
for k in range(1200):
    starts.append(rs.randn(64) * rs.choice([0.15, 0.25, 0.35, 0.5, 0.8]))
t0 = time.time()
b1, x1 = run(M1, c1, starts, nfev=1500)
print('    1200 starts %.0fs   best %.6e' % (time.time() - t0, b1))
if b1 < 1e-8:
    C, D = F.report(x1)
    P = np.array([np.vdot(C[i], C[i]).real for i in range(8)])
    X6 = np.abs([np.vdot(C[6], D[i]) for i in range(6)])
    X7 = np.abs([np.vdot(C[7], D[i]) for i in range(6)])
    print('    P   = %s' % np.round(P, 6))
    print('    |X^(6)| = %s' % np.round(X6, 6))
    print('    |X^(7)| = %s' % np.round(X7, 6))
    print('    |C6 x C7| = %.6e' % abs(C[6][0] * C[7][1] - C[6][1] * C[7][0]))
    np.save('t26_base_sol.npy', x1)
print()
print('VERDICT: facts model (with T2) is %s' % ('FEASIBLE' if min(b1, b if ok else 9) < 1e-8
                                                else 'apparently INFEASIBLE'))
