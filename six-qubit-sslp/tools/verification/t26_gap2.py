"""Extract the SIX off-diagonal relations that R1 u R2 do not use, and measure the
unused rank on the diagonal side relative to (group identity + moment equations).
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from o26 import S0, S1, BOT, TOP
from orbit import ind
from scan import xor, dot
from kl import dressings_full, flips

n0, n1 = len(S0), len(S1)
BLK = {BOT[i][a]: (i, a) for i in range(8) for a in (0, 1)}
TBL = {TOP[i][a]: (i, a) for i in range(8) for a in (0, 1)}
lbl = lambda x, y: 'M[C%d_%d , D%d_%d]' % (BLK[x][0], BLK[x][1], TBL[y][0], TBL[y][1])

WT1 = [e for e in flips() if e.count('1') == 1
       and any(xor(y, e) in S0 for y in S1)]
print('weight-one masks with incidences:', WT1)

R1rows = []
for g in range(3):
    for h in range(g + 1, 3):
        for a in (0, 1):
            for bb in (0, 1):
                R1rows.append([(BOT[2 * g + c][a], TOP[2 * h + 1 - c][bb]) for c in (0, 1)]
                              + [(BOT[2 * h + c][a], TOP[2 * g + 1 - c][bb]) for c in (0, 1)])
R2rows = []
for j in (6, 7):
    for i in range(6):
        R2rows.append([(BOT[j][a], TOP[i][a]) for a in (0, 1)]
                      + [(BOT[i][a], TOP[j][a]) for a in (0, 1)])

for e in WT1:
    inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
    cols = {p: k for k, p in enumerate(inc)}
    rows = []
    for z in dressings_full(e):
        rows.append([(-1) ** dot(z, S1[t]) for _, t in inc])
    Mm = sp.Matrix(rows)
    rs = Mm.rref()[0][:Mm.rank(), :]
    used = []
    for r in R1rows + R2rows:
        if all(p in cols for p in r):
            v = [0] * len(inc)
            for p in r:
                v[cols[p]] += 1
            used.append(v)
    U = sp.Matrix(used) if used else sp.zeros(0, len(inc))
    print()
    print('--- mask e = %s : %d incidences, rank %d, R1/R2 use rank %d ---'
          % (e, len(inc), Mm.rank(), U.rank() if U.rows else 0))
    print('    incidences:', [lbl(x, y) for x, y in inc])
    print('    a basis of the full row space (each row = one relation = 0):')
    for i in range(rs.rows):
        terms = ' + '.join('%s*%s' % (rs[i, k], lbl(*inc[k])) for k in range(len(inc)) if rs[i, k])
        print('       ', terms)
    # complement of the used part inside the row space
    extra = []
    cur = U
    for i in range(rs.rows):
        cand = cur.col_join(sp.Matrix([list(rs[i, :])]))
        if cand.rank() > cur.rank():
            extra.append(list(rs[i, :])); cur = cand
    print('    NOT implied by R1 u R2 (%d new relations):' % len(extra))
    for v in extra:
        terms = ' + '.join('%s*%s' % (v[k], lbl(*inc[k])) for k in range(len(inc)) if v[k])
        print('       ', terms)

# ---------- diagonal side ---------------------------------------------------
print()
print('=== diagonal side: how much is unused ===')
DV, k = {}, 0
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


drows = []
for e in flips():
    db = [(S0.index(xor(x, e)), i) for i, x in enumerate(S0) if xor(x, e) in S0]
    dt = [(S1.index(xor(y, e)), j) for j, y in enumerate(S1) if xor(y, e) in S1]
    if not db and not dt:
        continue
    for z in dressings_full(e):
        drows.append(dvec([(('c', j, i), (-1) ** dot(z, S0[i])) for j, i in db]
                          + [(('d', j, i), -(-1) ** dot(z, S1[i])) for j, i in dt]))
DKL = sp.Matrix(drows)
GROUPS = [[0, 1], [2, 3], [4, 5], [6, 7]]
GM = []
for g in range(4):
    for a in (0, 1):
        for bb in (0, 1):
            t = [(('c', BOT[i][a], BOT[i][bb]), 1) for i in GROUPS[g]] \
                + [(('d', TOP[i][a], TOP[i][bb]), 1) for i in GROUPS[g]] \
                + [(('c', BOT[i][a], BOT[i][bb]), sp.Rational(-1, 2)) for i in range(8)]
            GM.append(dvec(t))
MOM = []                                   # the pure-Z (e = 0) moment equations
for z in dressings_full('000000'):
    MOM.append(dvec([(('c', i, i), (-1) ** dot(z, S0[i])) for i in range(n0)]
                    + [(('d', j, j), -(-1) ** dot(z, S1[j])) for j in range(n1)]))
FACTS = sp.Matrix(GM + MOM)
print('diagonal KL rank              : %d' % DKL.rank())
print('group identity rank           : %d' % sp.Matrix(GM).rank())
print('moment (pure-Z) rank          : %d' % sp.Matrix(MOM).rank())
print('rank(group identity + moments): %d' % FACTS.rank())
print('facts inside the KL span      : %s' % (DKL.rank() == DKL.col_join(FACTS).rank()))
print('UNUSED diagonal rank          : %d' % (DKL.rank() - FACTS.rank()))
