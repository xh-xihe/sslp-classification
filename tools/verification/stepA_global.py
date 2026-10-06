"""Independent route: one global 256-column system, no mask decomposition."""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp
from o26 import S0, S1, T0
from scan import bits, xor, dot
from kl import conditions

comp = lambda u: ''.join('1' if ch == '0' else '0' for ch in u)
BI = {S0.index(('1' if a else '0') + u): (i, a) for i, u in enumerate(T0) for a in (0, 1)}
TI = {S1.index(('1' if a else '0') + comp(u)): (i, a) for i, u in enumerate(T0) for a in (0, 1)}
BX = {v: k for k, v in BI.items()}
TX = {v: k for k, v in TI.items()}
CO = {(p, q): 16 * p + q for p in range(16) for q in range(16)}

rows = []
for e, z, off, db, dt in conditions(S0, S1):
    if not off:
        continue
    r = [0] * 256
    for p, q in off:
        r[CO[(p, q)]] += (-1) ** dot(z, S1[q])
    rows.append(r)
M = sp.Matrix(rows)
B = sp.Matrix([list(v) for v in M.rowspace()])
print('global off-diagonal system: %d rows, rank %d' % (M.rows, B.rows))


def vec(coeffs):
    v = sp.zeros(1, 256)
    for (bi, a, tj, b), q in coeffs.items():
        v[0, CO[(BX[(bi, a)], TX[(tj, b)])]] += q
    return v


def imp(coeffs):
    v = vec(coeffs)
    return B.rows == B.col_join(v).rank()


PAIRS = [(0, 1), (0, 2), (1, 2)]
print('R1 canonical entries (omega=+1) / omega=-1 / symplectic:')
for (g, h) in PAIRS:
    for a in (0, 1):
        for b in (0, 1):
            plus = {}
            minus = {}
            symp = {}
            for c in (0, 1):
                plus[(2 * g + c, a, 2 * h + 1 - c, b)] = 1
                plus[(2 * h + c, a, 2 * g + 1 - c, b)] = 1
                minus[(2 * g + c, a, 2 * h + 1 - c, b)] = 1
                minus[(2 * h + c, a, 2 * g + 1 - c, b)] = -1
                symp[(2 * g + c, a, 2 * h + 1 - c, b)] = (-1) ** c
                symp[(2 * h + c, a, 2 * g + 1 - c, b)] = (-1) ** c
            print('  (%d,%d)[%d,%d]  %s  %s  %s' % (g, h, a, b, imp(plus), imp(minus), imp(symp)))
print('R2 unflipped (X_i + Y_i) / (X_i - Y_i) / flipped (Xf_i + Yf_i):')
for j in (6, 7):
    for i in range(6):
        p = {(j, b, i, b): 1 for b in (0, 1)}
        p.update({(i, a, j, a): 1 for a in (0, 1)})
        q = {(j, b, i, b): 1 for b in (0, 1)}
        q.update({(i, a, j, a): -1 for a in (0, 1)})
        f = {(j, b, i, 1 - b): 1 for b in (0, 1)}
        f.update({(i, a, j, 1 - a): 1 for a in (0, 1)})
        f2 = {(j, b, i, 1 - b): 1 for b in (0, 1)}
        f2.update({(i, a, j, 1 - a): -1 for a in (0, 1)})
        print('  j=%d i=%d  X+Y %s   X-Y %s   flipped X+Y %s   flipped X-Y %s'
              % (j, i, imp(p), imp(q), imp(f), imp(f2)))
print('control: is any single flipped anchor monomial constrained at all?')
print('  cc(C6_0)D0_1 alone = 0 :', imp({(6, 0, 0, 1): 1}))
print('  column for cc(C6_0)D0_1 identically zero in the system :',
      all(M[r, CO[(BX[(6, 0)], TX[(0, 1)])]] == 0 for r in range(M.rows)))
