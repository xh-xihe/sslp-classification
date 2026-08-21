"""Orbit 31 in the phase parametrisation.

Every active position admits d_{v-bar} = rho_v * conj(c_v) with |rho_v| = 1, and
rho is constant along the columns of the 4x4 table.  Substituting turns each
cross-KL equation into a bilinear form in the bottom amplitudes whose
coefficients are the four column phases.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from relgen import setup
from scan import bits, xor, dot
from kl import dressings_full

A, QQ, DELTA, S0, S1 = setup(31)
E = ['000', '011', '101', '110']
U = ['011', '101', '110']
c3 = lambda s: ''.join('1' if ch == '0' else '0' for ch in s)
POS = {}                       # my S0 index -> (row, column), row 0 = A
for e in range(4):
    POS[S0.index('000' + E[e])] = (0, e)
for i in range(3):
    for e in range(4):
        POS[S0.index(U[i] + c3(E[e]))] = (i + 1, e)
NAME = {v: ('A%d' % k[1] if k[0] == 0 else 'B%d%d' % (k[0], k[1])) for v, k in POS.items()}
comp = lambda s: ''.join('1' if ch == '0' else '0' for ch in s)
cs = {v: sp.Symbol('c_%s' % NAME[v]) for v in range(16)}
sg = [sp.Symbol('s%d' % e) for e in range(4)]      # conj of the column phase


def bilinear(e, z):
    """The cross-KL equation for mask e and dressing z, after substitution."""
    ex = 0
    for t, y in enumerate(S1):
        w = xor(y, e)
        if w not in S0:
            continue
        v = S0.index(comp(y))                      # y = v-bar
        ex += (-1) ** dot(z, y) * sg[POS[v][1]] * cs[v] * cs[S0.index(w)]
    return sp.expand(ex)


if __name__ == '__main__':
    eqs = []
    for m in range(64):
        e = bits(m)
        if e.count('1') > 2:
            continue
        for z in dressings_full(e):
            b = bilinear(e, z)
            if b != 0:
                eqs.append((e, z, b))
    print('nonzero bilinear equations: %d' % len(eqs))
    seen, uniq = set(), []
    for e, z, b in eqs:
        k = min(str(sp.expand(b)), str(sp.expand(-b)))
        if k in seen:
            continue
        seen.add(k)
        uniq.append((e, z, b))
    print('distinct up to sign: %d' % len(uniq))
    for e, z, b in uniq[:14]:
        print('  [%s|%s]  %s = 0' % (e, z, b))
