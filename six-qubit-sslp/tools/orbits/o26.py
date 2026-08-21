"""Orbit 26: the group matrices and the matrix moment identity.

Blocks pair up by the virtual bit z into four groups indexed by (x,y).  The
claim to check is

    C_g C_g^dagger + D_g D_g^dagger = rho / 2,     rho = sum_g C_g C_g^dagger,

as a consequence of the diagonal Knill-Laflamme conditions for F on the
zero-angle qubit together with F Z_j on the tail bits carrying x, y, x+y.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from blocks import structure
from scan import bits, dot

A, QQ, DELTA, S0, S1, T0, _T1, BOT, _TOP = structure(26)
# the top block matching bottom block i is the one on the COMPLEMENTED tail
comp = lambda u: ''.join('1' if c == '0' else '0' for c in u)
TOP = [(S1.index('0' + comp(u)), S1.index('1' + comp(u))) for u in T0]
# tails as (x,y,z) -> the paper's parametrisation t = (x, y, z, z^(xy), x^y)
TAG = {}
for x in (0, 1):
    for y in (0, 1):
        for z in (0, 1):
            t = '%d%d%d%d%d' % (x, y, z, z ^ (x * y), x ^ y)
            TAG[t] = (x, y, z)
GRP = {}
for i, t in enumerate(T0):
    x, y, z = TAG[t]
    GRP.setdefault((x, y), [None, None])[z] = i
GROUPS = [GRP[k] for k in sorted(GRP)]
Pc = {(a, b, i): sp.Symbol('Pc%d%d_%d' % (a, b, i)) for a in (0, 1) for b in (0, 1)
      for i in range(8)}
Pd = {(a, b, i): sp.Symbol('Pd%d%d_%d' % (a, b, i)) for a in (0, 1) for b in (0, 1)
      for i in range(8)}
E0, EX = '000000', '100000'
# tail bits carrying x, y and x^y sit at six-qubit positions 1, 2 and 5
ZS = [bits(0), bits(1 << 1), bits(1 << 2), bits(1 << 5)]
ZS = ZS + [bits(1 | m) for m in (0, 1 << 1, 1 << 2, 1 << 5)]


def cond(e, z):
    ex = 0
    for i in range(8):
        b0, b1 = BOT[i]
        u, v = ((0, 0), (1, 1)) if e == E0 else ((0, 1), (1, 0))
        ex += (-1) ** dot(z, S0[b0]) * Pc[(u[0], u[1], i)]
        ex += (-1) ** dot(z, S0[b1]) * Pc[(v[0], v[1], i)]
    for i in range(8):
        c0, c1 = TOP[i]
        u, v = ((0, 0), (1, 1)) if e == E0 else ((0, 1), (1, 0))
        ex -= (-1) ** dot(z, S1[c0]) * Pd[(u[0], u[1], i)]
        ex -= (-1) ** dot(z, S1[c1]) * Pd[(v[0], v[1], i)]
    return sp.expand(ex)


CONDS = [(e, z, cond(e, z)) for e in (E0, EX) for z in ZS]


def target(a, b, g):
    rho = sum(Pc[(a, b, i)] for i in range(8))
    return sp.expand(sum(Pc[(a, b, i)] + Pd[(a, b, i)] for i in GROUPS[g])
                     - sp.Rational(1, 2) * rho)


def solve(a, b, g):
    tgt = target(a, b, g)
    lam = sp.symbols('lam0:%d' % len(CONDS))
    expr = sp.expand(sum(l * c[2] for l, c in zip(lam, CONDS)) - tgt)
    mons = sorted(set(Pc.values()) | set(Pd.values()), key=str)
    sol = sp.solve([sp.Eq(expr.coeff(m), 0) for m in mons], lam, dict=True)
    if not sol:
        return None
    s = sol[0]
    out = []
    for n, l in enumerate(lam):
        v = sp.simplify(s.get(l, l))
        v = v.subs({t: 0 for t in v.free_symbols}) if v.free_symbols else v
        if v != 0:
            out.append((CONDS[n][0], CONDS[n][1], sp.nsimplify(v)))
    return out


if __name__ == '__main__':
    print('tails      :', dict(enumerate(T0)))
    print('groups (x,y) ->', {k: GRP[k] for k in sorted(GRP)})
    ok = True
    for g in range(4):
        for a in (0, 1):
            for b in (0, 1):
                r = solve(a, b, g)
                if r is None:
                    ok = False
                    print('  group %d entry (%d,%d): NOT IN SPAN' % (g, a, b))
                elif (a, b, g) == (0, 0, 0) or (a, b, g) == (0, 1, 3):
                    print('  group %d entry (%d,%d): %d terms' % (g, a, b, len(r)))
    print('C_g C_g^dag + D_g D_g^dag = rho/2 holds for every group and entry:', ok)
