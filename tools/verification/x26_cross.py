"""TASK 1 -- the CROSS-ANCHOR contraction of R1, verified by bilinearity only.

Nothing is guessed about indices: conj((C_i)_a) and (D_i)_b are INDEPENDENT
free symbols, R1's entry E_ab(g,h) is written exactly as in the fact list, the
contraction is performed as a literal double sum over a,b, and the result is
compared to the claimed expression in
      X^j_i = C_j^dag D_i = sum_b conj((C_j)_b) (D_i)_b
      Y^j_i = C_i^dag D_j = sum_a conj((C_i)_a) (D_j)_a
by exact polynomial equality.
"""
import sympy as sp

NB = 8
cc = [[sp.Symbol('cc%d_%d' % (i, a)) for a in (0, 1)] for i in range(NB)]  # conj (C_i)_a
dd = [[sp.Symbol('d%d_%d' % (i, a)) for a in (0, 1)] for i in range(NB)]   # (D_i)_a
PAIRS = [(0, 1), (0, 2), (1, 2)]


def E(g, h, a, b):
    """R1 matrix entry (a,b) for the cycle-group pair (g,h)."""
    t = 0
    for c in (0, 1):
        t += cc[2 * g + c][a] * dd[2 * h + 1 - c][b]
        t += cc[2 * h + c][a] * dd[2 * g + 1 - c][b]
    return t


def X(j, i):
    return sum(cc[j][b] * dd[i][b] for b in (0, 1))


def Y(j, i):
    return sum(cc[i][a] * dd[j][a] for a in (0, 1))


def contract(g, h, jA, jB):
    """sum_{a,b} (D_jA)_a conj((C_jB)_b) E_ab(g,h):  a-slot jA, b-slot jB."""
    return sp.expand(sum(dd[jA][a] * cc[jB][b] * E(g, h, a, b)
                         for a in (0, 1) for b in (0, 1)))


def claim(g, h, jA, jB):
    return sp.expand(sum(Y(jA, 2 * g + c) * X(jB, 2 * h + 1 - c) for c in (0, 1))
                     + sum(Y(jA, 2 * h + c) * X(jB, 2 * g + 1 - c) for c in (0, 1)))


print('=' * 74)
print('STEP 1.  literal contraction  ==  sum_c Y^jA_{2g+c} X^jB_{2h+1-c}')
print('                                + sum_c Y^jA_{2h+c} X^jB_{2g+1-c}')
print('=' * 74)
allok = True
for (jA, jB) in [(7, 6), (6, 7), (6, 6), (7, 7)]:
    for (g, h) in PAIRS:
        diff = sp.expand(contract(g, h, jA, jB) - claim(g, h, jA, jB))
        ok = diff == 0
        allok = allok and ok
        print('  a-slot D_%d , b-slot conj(C_%d) , pair (%d,%d):  identity holds = %s'
              % (jA, jB, g, h, ok))
print('  ALL 12 exact:', allok)

print()
print('=' * 74)
print('STEP 2.  apply R2  (Y^j_i = -X^j_i)  in abstract scalars')
print('=' * 74)
Xs = {(j, i): sp.Symbol('X%d_%d' % (j, i)) for j in (6, 7) for i in range(6)}
Ys = {(j, i): sp.Symbol('Y%d_%d' % (j, i)) for j in (6, 7) for i in range(6)}


def abstract(g, h, jA, jB):
    return (sum(Ys[(jA, 2 * g + c)] * Xs[(jB, 2 * h + 1 - c)] for c in (0, 1))
            + sum(Ys[(jA, 2 * h + c)] * Xs[(jB, 2 * g + 1 - c)] for c in (0, 1)))


def RJR(g, h, j1, j2):
    """R_g^{(j1)} J R_h^{(j2)T}  with  R_g^{(j)} = (X^j_{2g}, X^j_{2g+1}),  J = [[0,1],[1,0]]."""
    return Xs[(j1, 2 * g)] * Xs[(j2, 2 * h + 1)] + Xs[(j1, 2 * g + 1)] * Xs[(j2, 2 * h)]


sub = {Ys[(j, i)]: -Xs[(j, i)] for j in (6, 7) for i in range(6)}
for (jA, jB) in [(7, 6), (6, 7), (6, 6), (7, 7)]:
    for (g, h) in PAIRS:
        got = sp.expand(abstract(g, h, jA, jB).subs(sub))
        tgt = sp.expand(-(RJR(g, h, jA, jB) + RJR(h, g, jA, jB)))
        print('  (a-slot %d, b-slot %d) pair (%d,%d):  contraction = -[ R_%d^(%d) J R_%d^(%d)T'
              ' + R_%d^(%d) J R_%d^(%d)T ]   %s'
              % (jA, jB, g, h, g, jA, h, jB, h, jA, g, jB, sp.expand(got - tgt) == 0))

print()
print('  ==> CROSS-ANCHOR RELATION (a-slot D_7, b-slot conj(C_6)), one per pair g<h:')
for (g, h) in PAIRS:
    print('        R_%d^(7) J R_%d^(6)T  +  R_%d^(7) J R_%d^(6)T  =  0' % (g, h, h, g))
print('  ==> the other order (a-slot D_6, b-slot conj(C_7)) gives the transpose,')
for (g, h) in PAIRS:
    lhs = sp.expand(RJR(g, h, 6, 7) + RJR(h, g, 6, 7))
    rhs = sp.expand(RJR(h, g, 7, 6) + RJR(g, h, 7, 6))
    print('        pair (%d,%d): identical as a polynomial: %s' % (g, h, sp.expand(lhs - rhs) == 0))
print('  ==> same anchor in both slots reproduces the KNOWN per-anchor relation:')
for j in (6, 7):
    for (g, h) in PAIRS:
        v = sp.expand(RJR(g, h, j, j) + RJR(h, g, j, j) - 2 * RJR(g, h, j, j))
        print('        j=%d pair (%d,%d):  = 2 R_%d^(%d) J R_%d^(%d)T   %s'
              % (j, g, h, g, j, h, j, v == 0))
