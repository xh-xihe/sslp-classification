"""Masks and relation data for the orbit 26 certificate."""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from o26 import S0, S1, T0, BOT, TOP, GROUPS, CONDS, Pc, Pd, target, solve
from scan import bits, xor, dot
from kl import dressings_full
from cert import build, reduce_mod_linear

n0, n1 = len(S0), len(S1)
Q, R, V, Am, bv, enames = build(S0, S1)
fields = list(enames) + ['nq%d' % k for k in range(n0)] + ['nr%d' % k for k in range(n1)]
CYC = [0, 3, 4, 1, 2, 5]
NB = {CYC[k]: (CYC[(k - 1) % 6], CYC[(k + 1) % 6]) for k in range(6)}
EDGES = [(CYC[k], CYC[(k + 1) % 6]) for k in range(6)]
ANCH = [6, 7]
dist = lambda s, t: sum(1 for x, y in zip(s, t) if x != y)
comp = lambda u: ''.join('1' if c == '0' else '0' for c in u)


def mask_for(i, j, flip_r):
    """Six-qubit mask joining bottom block i to top block j, with/without an r flip."""
    return ('1' if flip_r else '0') + xor5(T0[i], comp(T0[j]))


def xor5(s, t):
    return ''.join('1' if a != b else '0' for a, b in zip(s, t))


MAT = {}          # cycle edge -> (weight-1 mask, weight-2 mask)
for (i, j) in EDGES:
    assert dist(T0[i], T0[j]) == 4
    MAT[(i, j)] = (mask_for(i, j, False), mask_for(i, j, True))
SCA = {}          # (cycle vertex, anchor) -> weight-2 mask
for i in range(6):
    for j in ANCH:
        assert dist(T0[i], T0[j]) == 3
        SCA[(i, j)] = mask_for(i, j, False)
E0, EX = '000000', '100000'
ZDIAG = [bits(0), bits(1 << 1), bits(1 << 2), bits(1 << 5)]
ZDIAG = ZDIAG + [bits(1 | m) for m in (0, 1 << 1, 1 << 2, 1 << 5)]
MASKS = sorted({m for p in MAT.values() for m in p} | set(SCA.values()))
INC = {m: [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
       for m in MASKS}

if __name__ == '__main__':
    print('cycle', CYC, ' edges', EDGES)
    for e in EDGES:
        print('  edge %s : masks %s   incidences %d/%d'
              % (e, MAT[e], len(INC[MAT[e][0]]), len(INC[MAT[e][1]])))
    print('scalar masks:', {k: SCA[k] for k in sorted(SCA)})
    print('all off-diagonal masks: %d' % len(MASKS))
    bad = [m for m in MASKS if m.count('1') > 2]
    print('any mask of weight > 2:', bad)
