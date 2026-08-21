"""Ablation: which of the verified facts makes the model infeasible?

Sanity check on the encoding: if the model were over-constrained by a bug in
(M)/(E)/(A)/(T2), dropping R1 or R2 would not restore feasibility.
"""
import sys, time
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import numpy as np
from scipy.optimize import least_squares
import t26_facts_fast as F

M, c = F.build()
sizes = [('M', 16), ('N', 1), ('E', 8), ('A', 2), ('T2', 2), ('R1', 24), ('R2', 24)]
off = np.cumsum([0] + [s for _, s in sizes])
names = [n for n, _ in sizes]
assert off[-1] == len(c), (off[-1], len(c))


def sub(drop):
    keep = []
    for k, nm in enumerate(names):
        if nm in drop:
            continue
        keep += list(range(off[k], off[k + 1]))
    return M[keep], c[keep]


def solve(Ms, cs, ns=250, seed=9):
    pad = max(0, 65 - Ms.shape[0])
    r = lambda x: np.concatenate([np.einsum('kij,i,j->k', Ms, x, x) + cs, np.zeros(pad)])
    j = lambda x: np.vstack([2.0 * np.einsum('kij,j->ki', Ms, x), np.zeros((pad, 64))])
    rs = np.random.RandomState(seed)
    best, bx = np.inf, None
    for _ in range(ns):
        s = least_squares(r, rs.randn(64) * rs.choice([0.2, 0.35, 0.6]), jac=j,
                          method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=1200)
        v = np.linalg.norm(s.fun)
        if v < best:
            best, bx = v, s.x.copy()
    return best, bx


for drop in [[], ['R1'], ['R2'], ['T2'], ['R1', 'R2'], ['M'], ['A'], ['E']]:
    t = time.time()
    Ms, cs = sub(drop)
    b, bx = solve(Ms, cs)
    tag = 'FACTS minus ' + (','.join(drop) if drop else 'nothing')
    st = 'FEASIBLE  ' if b < 1e-8 else 'infeasible'
    extra = ''
    if b < 1e-8:
        C, D = F.report(bx)
        P = np.round([np.vdot(C[i], C[i]).real for i in range(8)], 4)
        extra = '  P=%s' % P
    print('%-28s %s resid %.3e (%.0fs)%s' % (tag, st, b, time.time() - t, extra))
