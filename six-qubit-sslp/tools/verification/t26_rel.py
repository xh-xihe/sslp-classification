"""Independent re-derivation of R1 and R2 from the raw weight-<=2 KL system.

Off-diagonal monomials  M[x][y] = conj(c_{S0[x]}) d_{S1[y]}.
An admissible Pauli X^e Z^z (|supp e u supp z| <= 2) gives the linear form
    sum_{y in S1, y^e in S0} (-1)^{z.y} M[idx(y^e)][y] = 0.
We check that every claimed R1 / R2 entry lies in the ROW SPACE of those forms,
and record which masks are used.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from o26 import S0, S1, BOT, TOP, GROUPS
from scan import bits, xor, dot
from kl import dressings_full, flips

n0, n1 = len(S0), len(S1)
IDX = {(x, y): x * n1 + y for x in range(n0) for y in range(n1)}
NV = n0 * n1


def vec(terms):
    v = [0] * NV
    for (x, y), c in terms:
        v[IDX[(x, y)]] += c
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
print('off-diagonal KL forms: %d rows, rank %d' % (KL.rows, KL.rank()))


def in_span(target):
    T = sp.Matrix([target])
    return KL.rank() == KL.col_join(T).rank()


def support_masks(target):
    """Which flips e are needed?  Test the span of each single-mask family."""
    used = []
    for e in sorted({t[0] for t in tags}):
        sub = sp.Matrix([rows[k] for k in range(len(rows)) if tags[k][0] == e])
        if sub.rows and sub.rank() == sub.col_join(sp.Matrix([target])).rank():
            used.append(e)
    return used


print()
print('=== R2 : C_j^dag D_i + C_i^dag D_j = 0,  i<=5, j in {6,7} ===')
allR2 = True
for j in (6, 7):
    for i in range(6):
        t = vec([((BOT[j][a], TOP[i][a]), 1) for a in (0, 1)]
                + [((BOT[i][a], TOP[j][a]), 1) for a in (0, 1)])
        ok = in_span(t)
        allR2 &= ok
        if i == 0:
            print('  (i=%d,j=%d) in span: %s   single-mask families that already contain it: %s'
                  % (i, j, ok, support_masks(t)))
print('  ALL twelve R2 relations lie in the KL span:', allR2)

print()
print('=== R1 : conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0,  0<=g<h<=2 ===')
allR1 = True
for g in range(3):
    for h in range(g + 1, 3):
        for a in (0, 1):
            for bidx in (0, 1):
                t = vec([((BOT[2 * g + c][a], TOP[2 * h + 1 - c][bidx]), 1) for c in (0, 1)]
                        + [((BOT[2 * h + c][a], TOP[2 * g + 1 - c][bidx]), 1) for c in (0, 1)])
                ok = in_span(t)
                allR1 &= ok
                if (g, h) == (0, 1):
                    print('  pair (%d,%d) entry (%d,%d) in span: %s  masks: %s'
                          % (g, h, a, bidx, ok, support_masks(t)))
print('  ALL twelve R1 entries lie in the KL span:', allR1)

print()
print('=== NOT available: per-edge two-term relations D_i C_k^dag + D_k C_i^dag ===')
bad = 0
for g in range(3):
    for h in range(g + 1, 3):
        for c in (0, 1):
            t = vec([((BOT[2 * g + c][a], TOP[2 * h + 1 - c][bidx]), 1) for a in (0, 1) for bidx in (0, 1) if a == bidx])
            # two-term version of one R1 half only
            t = vec([((BOT[2 * g + c][0], TOP[2 * h + 1 - c][0]), 1),
                     ((BOT[2 * h + 1 - c][0], TOP[2 * g + c][0]), 1)])
            if in_span(t):
                bad += 1
print('  two-term halves that ARE in the span (expect 0):', bad)

print()
print('=== the CROSS-ANCHOR contraction the repair wants ===')
print('  it is a contraction of the SAME R1 rows, so it is available whenever R1 is:',
      allR1 and allR2)
