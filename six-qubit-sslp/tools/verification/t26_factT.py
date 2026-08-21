"""Task 1: fact (T)  P_{2g}+P_{2g+1} = 1/4 for EVERY group, anchor included.

Everything is reduced modulo the LINEAR moment system (cert.build) with
cert.reduce_mod_linear; remainder 0 means the moment system implies it.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from o26 import S0, S1, BOT, TOP, GROUPS, T0
from cert import build, reduce_mod_linear

Q, R, V, A, b, names = build(S0, S1)
print('moment system: %d equations, %d unknowns, rank %d' % (A.rows, A.cols, A.rank()))
print('names:', names)

P = [Q[BOT[i][0]] + Q[BOT[i][1]] for i in range(8)]      # ||C_i||^2
QQ = [R[TOP[i][0]] + R[TOP[i][1]] for i in range(8)]     # ||D_i||^2

def chk(label, expr):
    cof, rem = reduce_mod_linear(sp.expand(expr), V, A, b)
    ok = (rem == 0)
    print('%-42s remainder = %s   %s' % (label, rem, 'IMPLIED' if ok else '*** NOT implied ***'))
    return ok, cof

allok = True
print()
print('--- (a) P_i = Q_i ---')
for i in range(8):
    ok, _ = chk('P_%d - Q_%d' % (i, i), P[i] - QQ[i])
    allok &= ok

print()
print('--- (b) anchor block masses ---')
for i in (6, 7):
    ok, _ = chk('P_%d - 1/8' % i, P[i] - sp.Rational(1, 8))
    allok &= ok
    ok, _ = chk('Q_%d - 1/8' % i, QQ[i] - sp.Rational(1, 8))
    allok &= ok

print()
print('--- (c) FACT (T): group sums ---')
Tcof = {}
for g in range(4):
    i, j = GROUPS[g]
    tag = 'ANCHOR' if g == 3 else 'cycle '
    ok, cof = chk('%s group %d : P_%d + P_%d - 1/4' % (tag, g, i, j),
                  P[i] + P[j] - sp.Rational(1, 4))
    Tcof[('P', g)] = cof
    allok &= ok
    ok, cof = chk('%s group %d : Q_%d + Q_%d - 1/4' % (tag, g, i, j),
                  QQ[i] + QQ[j] - sp.Rational(1, 4))
    allok &= ok

print()
print('--- (d) the weaker facts (T) is supposed to strengthen ---')
chk('sum_{i<6} P_i - 3/4', sum(P[i] for i in range(6)) - sp.Rational(3, 4))
chk('P_1+P_3+P_5 - 3/8', P[1] + P[3] + P[5] - sp.Rational(3, 8))
chk('P_0+P_2+P_4 - 3/8', P[0] + P[2] + P[4] - sp.Rational(3, 8))
chk('Q_1+Q_3+Q_5 - 3/8', QQ[1] + QQ[3] + QQ[5] - sp.Rational(3, 8))

print()
print('--- (e) individual blocks pinned? ---')
for i in range(8):
    cof, rem = reduce_mod_linear(sp.expand(P[i]), V, A, b)
    print('P_%d reduces to : %s' % (i, rem))

print()
print('ALL CHECKS PASS:', allok)

print()
print('--- (f) certificate for FACT (T), cycle groups, in the original equations ---')
for g in range(4):
    cof = Tcof[('P', g)]
    terms = [(names[k], cof[k]) for k in range(len(names)) if cof[k] != 0]
    print('group %d : %s' % (g, terms))
