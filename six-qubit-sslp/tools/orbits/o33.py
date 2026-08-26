"""Orbit 33: the block reflection, set up exactly.

Blocks: c_i = (p_i, q_i) with p_i = c(S0[i]), q_i = c(S0[i+6]);
        d_i = (s_i, t_i) with s_i = d(S1[5-i]), t_i = d(S1[11-i]).

Monomials  Pc[a][b][i] = (c_i)_a conj((c_i)_b),  Pd[a][b][i] likewise.
Target     Pc[a][b][i] + Pd[a][b][i] - 2 R_i sum_k Pc[a][b][k] = 0.
"""
import sys
sys.path.insert(0, '.')
import sympy as sp

from orbit import fiber
from scan import bits, xor, dot

AVEC, QQ, DELTA = [0, 1, 1, 3, 3, 3], 5, 1
S0, S1 = fiber(AVEC, QQ, 0), fiber(AVEC, QQ, DELTA)
TB = ['00000', '01111', '10111', '11001', '11010', '11100']
TT = [''.join('1' if ch == '0' else '0' for ch in u) for u in TB]
BOT = [(S0.index('0' + u), S0.index('1' + u)) for u in TB]
TOP = [(S1.index('0' + u), S1.index('1' + u)) for u in TT]
RV = [sp.Rational(3, 10)] + [sp.Rational(1, 5)] * 2 + [sp.Rational(1, 10)] * 3
E0, EX = '000000', '100000'
ZS = [bits(0)] + [bits(1 << j) for j in range(1, 6)]
ZS = ZS + [bits(1) ] + [bits(1 | (1 << j)) for j in range(1, 6)]   # with the qubit-0 Z

# symbols
Pc = {(a, b, i): sp.Symbol('Pc%d%d_%d' % (a, b, i)) for a in (0, 1) for b in (0, 1)
      for i in range(6)}
Pd = {(a, b, i): sp.Symbol('Pd%d%d_%d' % (a, b, i)) for a in (0, 1) for b in (0, 1)
      for i in range(6)}


def cond(e, z):
    """The diagonal KL condition as a symbolic expression (bottom minus top)."""
    ex = 0
    for i in range(6):
        b0, b1 = BOT[i]
        if e == E0:
            ex += (-1) ** dot(z, S0[b0]) * Pc[(0, 0, i)]
            ex += (-1) ** dot(z, S0[b1]) * Pc[(1, 1, i)]
        else:                                   # e = X on qubit 0
            ex += (-1) ** dot(z, S0[b0]) * Pc[(0, 1, i)]
            ex += (-1) ** dot(z, S0[b1]) * Pc[(1, 0, i)]
    for i in range(6):
        t0, t1 = TOP[i]
        if e == E0:
            ex -= (-1) ** dot(z, S1[t0]) * Pd[(0, 0, i)]
            ex -= (-1) ** dot(z, S1[t1]) * Pd[(1, 1, i)]
        else:
            ex -= (-1) ** dot(z, S1[t0]) * Pd[(0, 1, i)]
            ex -= (-1) ** dot(z, S1[t1]) * Pd[(1, 0, i)]
    return sp.expand(ex)


CONDS = [(e, z, cond(e, z)) for e in (E0, EX) for z in ZS]


def solve_target(a, b, i):
    tgt = sp.expand(Pc[(a, b, i)] + Pd[(a, b, i)]
                    - 2 * RV[i] * sum(Pc[(a, b, k)] for k in range(6)))
    lam = sp.symbols('lam0:%d' % len(CONDS))
    expr = sp.expand(sum(l * c[2] for l, c in zip(lam, CONDS)) - tgt)
    mons = sorted(set(Pc.values()) | set(Pd.values()), key=str)
    eqs = [sp.Eq(expr.coeff(m), 0) for m in mons]
    sol = sp.solve(eqs, lam, dict=True)
    if not sol:
        return None
    s = sol[0]
    out = []
    for n, l in enumerate(lam):
        v = sp.simplify(s.get(l, l))
        v = v.subs({x: 0 for x in v.free_symbols}) if v.free_symbols else v
        if v != 0:
            out.append((CONDS[n][0], CONDS[n][1], sp.nsimplify(v)))
    return out


if __name__ == '__main__':
    print('S0 =', S0)
    print('S1 =', S1)
    print('bottom blocks', BOT)
    print('top    blocks', TOP)
    allok = True
    for a in (0, 1):
        for b in (0, 1):
            for i in range(6):
                r = solve_target(a, b, i)
                if r is None:
                    allok = False
                    print('  (%d,%d) block %d : NOT IN SPAN' % (a, b, i))
                elif (a, b, i) == (0, 0, 0) or (a, b, i) == (0, 1, 3):
                    print('  (%d,%d) block %d : %d terms  %s'
                          % (a, b, i, len(r), [(e, z, str(v)) for e, z, v in r][:4]))
    print('every reflection identity lies in the span of the 24 conditions:', allok)
