"""Exact Farkas certificates for every infeasible zero-set, and the exact shape
of the block-mass polytope."""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from itertools import combinations, product

import sympy as sp

from o26 import S0, S1, BOT, TOP
from cert import build, reduce_mod_linear

Q, R, V, A, b, names = build(S0, S1)
Pexpr = [Q[BOT[i][0]] + Q[BOT[i][1]] for i in range(8)]
red = []
for i in range(8):
    _, rem = reduce_mod_linear(sp.expand(Pexpr[i]), V, A, b)
    red.append(sp.expand(rem))
u, v = sp.symbols('u v')
sub = {sp.Symbol('r7'): u / 2, sp.Symbol('r15'): u / 2,
       sp.Symbol('r5'): v / 2, sp.Symbol('r13'): v / 2}
aff = [sp.expand(r.subs(sub)) for r in red]
print('block masses as affine functions of u=P_0, v=P_2 (mod the moment system):')
for i in range(8):
    print('   P_%d = %s' % (i, aff[i]))

print()
print('the block-mass polytope  { P_i >= 0 }  in (u,v):')
ineqs = [sp.simplify(a) for a in aff]
print('   ', [sp.simplify(a) >= 0 for a in aff[:6]])
verts = [(sp.Rational(0, 1), sp.Rational(1, 8)), (sp.Rational(0), sp.Rational(1, 4)),
         (sp.Rational(1, 8), sp.Rational(1, 4)), (sp.Rational(1, 4), sp.Rational(1, 8)),
         (sp.Rational(1, 4), sp.Rational(0)), (sp.Rational(1, 8), sp.Rational(0))]
print('   hexagon vertices (u,v) and the block masses there:')
for w in verts:
    Pv = [sp.nsimplify(a.subs({u: w[0], v: w[1]})) for a in aff]
    print('      (u,v)=%s  ->  P=%s   zero blocks %s'
          % (w, Pv, [i for i in range(8) if Pv[i] == 0]))


def certify(Z):
    """find integer lam_i>=0 (i not in Z), mu_i free (i in Z) with
       sum lam_i P_i + sum mu_i P_i  ==  negative constant   (mod moment system)."""
    out = set(range(8)) - set(Z)
    for k in range(1, 4):
        for pick in combinations(sorted(out), k):
            for lam in product([1, 2, 3], repeat=k):
                base = sum(l * aff[i] for l, i in zip(lam, pick))
                for mu in product([-3, -2, -1, 0, 1, 2, 3], repeat=len(Z)):
                    e = sp.expand(base + sum(m * aff[i] for m, i in zip(mu, sorted(Z))))
                    if e.free_symbols:
                        continue
                    if e < 0:
                        terms = ' + '.join('%d*P_%d' % (l, i) for l, i in zip(lam, pick))
                        ext = ' '.join('%+d*P_%d' % (m, i) for m, i in zip(mu, sorted(Z)) if m)
                        return '%s %s  ==  %s' % (terms, ext, e)
    return None


print()
print('=== exact certificates for the infeasible zero-sets ===')
import numpy as np
from scipy.optimize import linprog
An = np.array(A.tolist(), float); bn = np.array(b.tolist(), float).ravel()
Prow = [[float(sp.expand(Pexpr[i]).coeff(x)) for x in V] for i in range(8)]
n = A.cols


def lpfeas(Z):
    rows = [list(An[k]) for k in range(An.shape[0])] + [Prow[i] for i in Z]
    rhs = list(bn) + [0.0] * len(Z)
    r = linprog(np.zeros(n), A_eq=np.array(rows), b_eq=np.array(rhs),
                bounds=[(0, None)] * n, method='highs')
    return r.status == 0


for k in (1, 2, 3):
    for Z in combinations(range(8), k):
        if lpfeas(set(Z)):
            continue
        c = certify(set(Z))
        if k == 3 and c is None:
            continue          # triples: covered by a contained infeasible pair
        print('  %-12s infeasible.  %s' % (str(list(Z)), c if c else '(no small cert found)'))
    if k == 3:
        break
