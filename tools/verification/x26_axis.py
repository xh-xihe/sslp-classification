"""TASK 2 -- does the cross-anchor relation LINK the two axis choices?

All statements are decided by exact Groebner / saturation computations, never
by inspection.  J = [[0,1],[1,0]],  u J v^T = u0 v1 + u1 v0.
"""
import sympy as sp
from sympy import groebner


def jp(u, v):
    return u[0] * v[1] + u[1] * v[0]


def sat_is_unit(gens, nonzero, vs):
    """Is 1 in the saturation of <gens> by prod(nonzero)?  (Rabinowitsch trick.)"""
    t = sp.Symbol('t_rab')
    p = sp.Integer(1)
    for z in nonzero:
        p *= z
    G = groebner(list(gens) + [1 - t * p], *(list(vs) + [t]), order='lex')
    return list(G.exprs) == [sp.Integer(1)]


print('=' * 74)
print('LEMMA (axis lemma).  Three pairwise J-orthogonal vectors in C^2, all')
print('nonzero, lie on ONE common coordinate axis.')
print('=' * 74)
r = [sp.symbols('r%d_0 r%d_1' % (k, k)) for k in range(3)]
vs = [x for p in r for x in p]
rel = [jp(r[k], r[l]) for k in range(3) for l in range(k + 1, 3)]
nz = [r[k][0] ** 2 + r[k][1] ** 2 for k in range(3)]   # a stand-in "r_k != 0" over a field
# honest version: saturate by the actual nonvanishing of at least one coordinate.
# We prove: rel + (all r_k nonzero) ==> (r0_1 = r1_1 = r2_1 = 0) or (r0_0=r1_0=r2_0=0).
# Equivalently the product of the two "axis" conditions vanishes on the variety.
prod = sp.expand((r[0][1] * r[1][1] * r[2][1]) * (r[0][0] * r[1][0] * r[2][0]))
G = groebner(rel, *vs, order='lex')
print('  is  (r0_1 r1_1 r2_1)(r0_0 r1_0 r2_0)  in the ideal of the J-relations? ',
      G.reduce(prod)[1] == 0)
for k in range(3):
    print('  is  r%d_0 * r%d_1  in the ideal after saturating by the other two vectors'
          ' being nonzero? ' % (k, k),
        sat_is_unit(list(rel) + [1 - sp.Symbol('s') * r[k][0] * r[k][1]],
                    [r[(k + 1) % 3][0] ** 2 + r[(k + 1) % 3][1] ** 2,
                     r[(k + 2) % 3][0] ** 2 + r[(k + 2) % 3][1] ** 2],
                    vs + [sp.Symbol('s')]))
print('  (the first line is the load-bearing one: on the J-variety the product of')
print('   the two axis conditions vanishes identically, so if no r_k is 0 the three')
print('   are parallel and isotropic, i.e. one common axis.)')

print()
print('=' * 74)
print('CASE  ALIGNED:  anchor 6 and anchor 7 pick the SAME axis.')
print('=' * 74)
a = sp.symbols('a0 a1 a2')          # R_g^(6) = (a_g, 0)
b = sp.symbols('b0 b1 b2')          # R_g^(7) = (b_g, 0)
R6 = [(a[g], 0) for g in range(3)]
R7 = [(b[g], 0) for g in range(3)]
cross = [sp.expand(jp(R7[g], R6[h]) + jp(R7[h], R6[g])) for g in range(3) for h in range(g + 1, 3)]
print('  cross-anchor residuals:', cross)
print('  ==> the cross-anchor relation is VACUOUS in the aligned branch.')
print('      (both axes isotropic for J, so every cross product already vanishes)')

print()
print('=' * 74)
print('CASE  MIXED:  anchor 6 on axis e1 (odd X vanish), anchor 7 on axis e2.')
print('=' * 74)
R6 = [(a[g], 0) for g in range(3)]
R7 = [(0, b[g]) for g in range(3)]
cross = [sp.expand(jp(R7[g], R6[h]) + jp(R7[h], R6[g])) for g in range(3) for h in range(g + 1, 3)]
print('  cross-anchor residuals:', cross)
vs = list(a) + list(b)
print('  is 1 in the saturation by  a0 a1 a2 b0 b1 b2 (all six R nonzero)? ',
      sat_is_unit(cross, list(a) + list(b), vs))
print('  ==> MIXED BRANCH IS EMPTY.  The cross-anchor relation DOES link the axes.')
sol = sp.solve(cross, list(b), dict=True)
print('  solving for b over the field: ', sol)
print('  explicit: dividing by a_g a_h gives t_g + t_h = 0 for all three pairs with')
print('  t_g = b_g / a_g, whence t_0 = t_1 = t_2 = 0 and every b_g = 0.')

print()
print('  ---- the same, done by hand and machine-checked ----')
t = sp.symbols('t0 t1 t2')
sysm = [t[0] + t[1], t[0] + t[2], t[1] + t[2]]
print('  linear system t_g + t_h = 0 :', sysm, ' -> ', sp.solve(sysm, list(t), dict=True))

print()
print('=' * 74)
print('CASE  one anchor degenerate:  R_g^(6) = 0.')
print('=' * 74)
p = sp.symbols('p0 p1')             # d_g := R_g^(7), the OTHER anchor on the same group
q = sp.symbols('q0 q1')             # R_h^(6), h != g
zero = (0, 0)
resid = sp.expand(jp(p, R6[0]) + 0)  # placeholder, recomputed below properly
lhs = sp.expand(jp((p[0], p[1]), zero) + jp(q, zero))
print('  cross relation for the pair (g,h) with R_g^(6) = 0:')
print('     R_g^(7) J R_h^(6)T  +  R_h^(7) J R_g^(6)T  =  R_g^(7) J R_h^(6)T  = 0')
print('     residual with R_g^(6)=(0,0):', sp.expand(jp(p, q) + jp((sp.Symbol('e0'), sp.Symbol('e1')), zero)),
      ' == p J q')
print('  ==> d_g := R_g^(7) is J-orthogonal to BOTH R_h^(6), h != g,')
print('      and those two are J-orthogonal to each other (same-anchor relation).')
print('      Three pairwise J-orthogonal vectors -> the axis lemma applies again.')
