"""How much of the KL off-diagonal information do R1 and R2 actually capture?

The 72 off-diagonal KL forms have rank 30.  R1 supplies 12 rows and R2 supplies 12.
If rank(R1 u R2) < 30 there are relations the argument is simply not using.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from o26 import S0, S1, BOT, TOP
from scan import xor, dot
from kl import dressings_full, flips

n0, n1 = len(S0), len(S1)
NV = n0 * n1
IDX = lambda x, y: x * n1 + y


def vec(terms):
    v = [0] * NV
    for (x, y), c in terms:
        v[IDX(x, y)] += c
    return v


rows, tags = [], []
for e in flips():
    inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
    if not inc:
        continue
    for z in dressings_full(e):
        rows.append(vec([((x, t), (-1) ** dot(z, S1[t])) for x, t in inc]))
        tags.append((e, z))
KL = sp.Matrix(rows)
rKL = KL.rank()
print('KL off-diagonal forms: %d rows, rank %d' % (KL.rows, rKL))

R1 = []
for g in range(3):
    for h in range(g + 1, 3):
        for a in (0, 1):
            for bb in (0, 1):
                R1.append(vec([((BOT[2 * g + c][a], TOP[2 * h + 1 - c][bb]), 1) for c in (0, 1)]
                              + [((BOT[2 * h + c][a], TOP[2 * g + 1 - c][bb]), 1) for c in (0, 1)]))
R2 = []
for j in (6, 7):
    for i in range(6):
        R2.append(vec([((BOT[j][a], TOP[i][a]), 1) for a in (0, 1)]
                      + [((BOT[i][a], TOP[j][a]), 1) for a in (0, 1)]))
M1, M2 = sp.Matrix(R1), sp.Matrix(R2)
M12 = M1.col_join(M2)
print('rank R1 = %d,  rank R2 = %d,  rank(R1 u R2) = %d' % (M1.rank(), M2.rank(), M12.rank()))
print('MISSING off-diagonal rank not used by the argument: %d' % (rKL - M12.rank()))

# which masks carry the missing rank?
print()
print('rank contributed by each flip family, and how much of it R1 u R2 already has:')
for e in sorted({t[0] for t in tags}):
    sub = sp.Matrix([rows[k] for k in range(len(rows)) if tags[k][0] == e])
    r_e = sub.rank()
    r_join = M12.col_join(sub).rank()
    print('   e=%s  wt %d  incidences %2d  rank %2d   new rank on top of R1uR2: %d'
          % (e, e.count('1'), sum(1 for t, y in enumerate(S1) if xor(y, e) in S0), r_e,
             r_join - M12.rank()))

# ---- the diagonal side ----------------------------------------------------
print()
print('=== diagonal side ===')
DV = {}
k = 0
for x in range(n0):
    for xx in range(n0):
        DV[('c', x, xx)] = k; k += 1
for y in range(n1):
    for yy in range(n1):
        DV[('d', y, yy)] = k; k += 1
ND = k


def dvec(terms):
    v = [0] * ND
    for key, c in terms:
        v[DV[key]] += c
    return v


drows, dtags = [], []
for e in flips():
    db = [(S0.index(xor(x, e)), i) for i, x in enumerate(S0) if xor(x, e) in S0]
    dt = [(S1.index(xor(y, e)), j) for j, y in enumerate(S1) if xor(y, e) in S1]
    if not db and not dt:
        continue
    for z in dressings_full(e):
        t = [(('c', j, i), (-1) ** dot(z, S0[i])) for j, i in db] \
            + [(('d', j, i), -(-1) ** dot(z, S1[i])) for j, i in dt]
        drows.append(dvec(t)); dtags.append((e, z))
DKL = sp.Matrix(drows)
print('diagonal KL forms: %d rows, rank %d' % (DKL.rows, DKL.rank()))
# the group matrix identity, 4 groups x 4 entries
GM = []
GROUPS = [[0, 1], [2, 3], [4, 5], [6, 7]]
for g in range(4):
    for a in (0, 1):
        for bb in (0, 1):
            t = []
            for i in GROUPS[g]:
                t.append((('c', BOT[i][a], BOT[i][bb]), 1))
                t.append((('d', TOP[i][a], TOP[i][bb]), 1))
            for i in range(8):
                t.append((('c', BOT[i][a], BOT[i][bb]), sp.Rational(-1, 2)))
            GM.append(dvec(t))
MG = sp.Matrix(GM)
print('group matrix identity rows: %d, rank %d' % (MG.rows, MG.rank()))
print('rank(diagonal KL) - rank(group identity) = %d' % (DKL.rank() - MG.rank()))
print('group identity inside the diagonal KL span:',
      DKL.rank() == DKL.col_join(MG).rank())
