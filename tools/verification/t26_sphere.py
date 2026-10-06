"""Task 4, scale-invariant form.

All 244 non-normalisation KL residuals are HOMOGENEOUS quadratics, and the pure-Z
Pauli with e=z=0 already forces ||c||^2 = ||d||^2, so a nonzero solution can always
be rescaled to a normalised code.  Minimising them on the sphere ||x||^2 = 2
therefore removes the trivial solution and any scale trade-off:

    orbit 26 admits a code  <=>  min over the sphere is 0.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import time

import numpy as np
from scipy.optimize import least_squares

src = open('t26_kl_fast.py').read().split('NST = int')[0]
exec(src)

hk = [k for k in range(M.shape[0]) if lab[k] not in ('norm0', 'norm1')]
Mh = M[hk]
S = np.sqrt(2.0)
print('homogeneous KL residuals: %d   unknowns: %d' % (len(hk), N))


def g(x):
    y = S * x / np.linalg.norm(x)
    return np.einsum('kij,i,j->k', Mh, y, y)


def run(nstart, seed, tag, x_seeds=None):
    rs = np.random.RandomState(seed)
    best, bx, hist = np.inf, None, []
    t0 = time.time()
    for k in range(nstart):
        x0 = x_seeds[k % len(x_seeds)] + 0.3 * rs.randn(N) if x_seeds is not None else rs.randn(N)
        s = least_squares(g, x0, method='lm', xtol=1e-14, ftol=1e-14, gtol=1e-14,
                          max_nfev=4000)
        v = np.linalg.norm(s.fun); hist.append(v)
        if v < best:
            best, bx = v, s.x.copy()
    h = np.sort(np.array(hist))
    print('%-26s %4d starts %6.1fs   min %.8e  1%%ile %.8e  median %.8e'
          % (tag, nstart, time.time() - t0, h[0], h[max(0, len(h) // 100)], h[len(h) // 2]))
    return best, bx


best, bx = run(250, 11, 'random starts')

# restart from solutions of the DIAGONAL-only subsystem (which is solvable)
dk = [k for k in range(M.shape[0]) if lab[k] not in ('norm0', 'norm1')
      and lab[k][0].startswith('dia')]
Md = M[dk]
gd = lambda x: np.einsum('kij,i,j->k', Md, S * x / np.linalg.norm(x), S * x / np.linalg.norm(x))
rs = np.random.RandomState(77)
seeds = []
for k in range(40):
    s = least_squares(gd, rs.randn(N), method='lm', xtol=1e-14, ftol=1e-14, gtol=1e-14,
                      max_nfev=4000)
    if np.linalg.norm(s.fun) < 1e-9:
        seeds.append(s.x.copy())
print('exact solutions of the diagonal-only subsystem found: %d' % len(seeds))
if seeds:
    b2, _ = run(150, 23, 'from diagonal solutions', seeds)
    best = min(best, b2)

# restart from solutions of the OFF-diagonal-only subsystem
ok_ = [k for k in range(M.shape[0]) if lab[k] not in ('norm0', 'norm1')
       and lab[k][0].startswith('off')]
Mo = M[ok_]
go = lambda x: np.einsum('kij,i,j->k', Mo, S * x / np.linalg.norm(x), S * x / np.linalg.norm(x))
seeds2 = []
for k in range(40):
    s = least_squares(go, rs.randn(N), method='lm', xtol=1e-14, ftol=1e-14, gtol=1e-14,
                      max_nfev=4000)
    if np.linalg.norm(s.fun) < 1e-9:
        seeds2.append(s.x.copy())
print('exact solutions of the off-diagonal-only subsystem found: %d' % len(seeds2))
if seeds2:
    b3, _ = run(150, 29, 'from off-diagonal solutions', seeds2)
    best = min(best, b3)

print()
print('BEST KL RESIDUAL over the normalised sphere: %.10e' % best)
y = S * bx / np.linalg.norm(bx)
c, d = y[:16] + 1j * y[16:32], y[32:48] + 1j * y[48:64]
print('  ||c||^2 = %.8f   ||d||^2 = %.8f' % (np.sum(abs(c) ** 2), np.sum(abs(d) ** 2)))
print('  largest single Pauli violation: %.10e' % np.max(np.abs(g(bx))))
print()
print('VERDICT: orbit 26 is %s by the full weight-<=2 KL system.'
      % ('NOT EXCLUDED -- ALARM' if best < 1e-6 else 'EXCLUDED'))
