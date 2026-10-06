"""Solve the orbit-46 diagonal moment system from scratch and compare with
the paper's claimed normal form  (u,u,a,a,v,v,b,b,g,g),
u = 1/4 - a,  v = 1/4 - b - g,  p = q under the X_6 matching."""
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
from orbit import fiber

Q, A, D = 6, [1, 2, 2, 2, 3, 3], 3
S0, S1 = fiber(A, Q, 0), fiber(A, Q, D)
n0, n1 = len(S0), len(S1)
print('S_0 =', ' '.join(S0))
print('S_3 =', ' '.join(S1))

flip = lambda x: x[:5] + ('1' if x[5] == '0' else '0')
print('X_6 matching from S_0:', ' '.join(flip(x) for x in S0))
print('matches S_3 as a set:', sorted(flip(x) for x in S0) == sorted(S1))

rows = [[1] * n0 + [0] * n1, [0] * n0 + [1] * n1]
rhs = [1, 1]
for T in [()] + [(i,) for i in range(6)] + list(combinations(range(6), 2)):
    chi = lambda z: (-1) ** sum(int(z[i]) for i in T)
    rows.append([chi(x) for x in S0] + [-chi(y) for y in S1])
    rhs.append(0)
M = sp.Matrix(rows)
print('moment matrix %dx%d, rank %d' % (M.rows, M.cols, M.rank()))

v = sp.Matrix(sp.symbols('p0:%d q0:%d' % (n0, n1)))
sol = sp.solve([sp.Eq(r, b) for r, b in zip(M * v, sp.Matrix(rhs))],
               list(v), dict=True)[0]
free = sorted({s for e in sol.values() for s in e.free_symbols},
              key=lambda s: s.name)
print('free parameters:', free)

pv = [sp.simplify(sol.get(v[k], v[k])) for k in range(n0)]
qv = [sp.simplify(sol.get(v[n0 + k], v[n0 + k])) for k in range(n1)]
print()
print('solved p (lexicographic S_0 order):')
for x, e in zip(S0, pv):
    print('   %s  %s' % (x, e))
print('solved q, reindexed to the X_6 matching (should equal p):')
qd = dict(zip(S1, qv))
mism = []
for x, e in zip(S0, pv):
    f = sp.simplify(qd[flip(x)] - e)
    if f != 0:
        mism.append((x, qd[flip(x)], e))
    print('   %s -> %s  %s' % (x, flip(x), qd[flip(x)]))
print()
print('p_x == q_{x^e6} for every x :', not mism)
print('number of free parameters   :', len(free), '(paper: 3)')
print('paper pattern (m,m,a,a,v,v,b,b,g,g) i.e. equal in consecutive pairs:')
print('   consecutive-pair equality:',
      [sp.simplify(pv[2 * k] - pv[2 * k + 1]) == 0 for k in range(5)])
