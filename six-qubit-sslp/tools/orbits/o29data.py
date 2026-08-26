"""Structural data for the orbit 29 certificate."""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from relgen import setup
from scan import bits, xor, dot
from kl import dressings_full
from cert import build, reduce_mod_linear

AVEC, QQ, DELTA = [1, 1, 1, 1, 2, 2], 4, 1
_, _, _, S0, S1 = setup(29)
n0, n1 = len(S0), len(S1)
Q, R, V, Am, bv, enames = build(S0, S1)
fields = list(enames) + ['nq%d' % k for k in range(n0)] + ['nr%d' % k for k in range(n1)]

# K4 on the four top pairs that carry edges
VERT = [3, 5, 6, 7]
EDGE = {1: (3, 5), 2: (3, 6), 3: (3, 7), 4: (5, 6), 5: (5, 7), 6: (6, 7)}
# which mask carries which orthogonality
EMASK = {(1, 3): '010000', (1, 5): '100000', (2, 3): '001000', (2, 6): '100000',
         (3, 3): '000100', (3, 7): '100000', (4, 5): '001000', (4, 6): '010000',
         (5, 5): '000100', (5, 7): '010000', (6, 6): '000100', (6, 7): '001000'}
# endgame: top pair -> (uncrossed mask, crossed mask, three bottom pairs,
#                       three edge-free top pairs)
FAM = {3: ('100001', '100010'), 5: ('010001', '010010'),
       6: ('001001', '001010'), 7: ('000101', '000110')}
MASKS = sorted({m for m in EMASK.values()} | {m for p in FAM.values() for m in p})
INC = {m: [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
       for m in MASKS}


def solve_row(m, tgt, zs):
    M = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in INC[m]] for z in zs])
    sol = M.T.gauss_jordan_solve(sp.Matrix(tgt))[0]
    mu = sol.subs({p: 0 for p in sol.free_symbols})
    return [(zs[u], sp.Rational(mu[u])) for u in range(len(zs)) if mu[u] != 0]


def edge_combo(m, n):
    """Dressing combination realising  star(c_{2m}) d_{2n} + star(c_{2m+1}) d_{2n+1} = 0."""
    e = EMASK[(m, n)]
    ii = INC[e]
    tgt = [1 if (i, t) in ((2 * m, 2 * n), (2 * m + 1, 2 * n + 1)) else 0 for i, t in ii]
    assert sum(tgt) == 2, (m, n, e, ii)
    return e, solve_row(e, tgt, dressings_full(e))


if __name__ == '__main__':
    print('S0 =', S0)
    print('S1 =', S1)
    ok = True
    for m, (n, np_) in EDGE.items():
        expr = (Q[2 * m] + Q[2 * m + 1]) - (R[2 * n] + R[2 * n + 1]) \
               - (R[2 * np_] + R[2 * np_ + 1]) + sp.Rational(1, 4)
        cof, rem = reduce_mod_linear(expr, V, Am, bv)
        r = sp.simplify(rem)
        ok = ok and r == 0
        print('P_%d = Q_%d + Q_%d - 1/4  reduces to %s' % (m, n, np_, r))
    print('all six edge identities hold:', ok)
    for m, n in sorted(EMASK):
        e, cmb = edge_combo(m, n)
        print('  C%d perp D%d  [%s]  %s' % (m, n, e, [(z, str(c)) for z, c in cmb]))
