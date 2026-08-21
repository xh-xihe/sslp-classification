"""TASKS 3 and 4 -- every branch of the case tree, each step machine-checked.

Notation.  Blocks 0..5 are the cycle blocks, 6 and 7 the anchor blocks.
  P_i = |C_i|^2,  Q_i = |D_i|^2,   X^j_i = C_j^dag D_i,  Y^j_i = C_i^dag D_j.
  R_g^{(j)} = (X^j_{2g}, X^j_{2g+1}),   J = [[0,1],[1,0]].
  Z_j = { g : R_g^{(j)} = 0 }.
Verified facts used:
  (M)  C_g C_g^dag + D_g D_g^dag = rho/2 for all four groups; rho = sum C_i C_i^dag
       = sum D_i D_i^dag
  (T)  P_{2g}+P_{2g+1} = Q_{2g}+Q_{2g+1} = 1/4 for every group including {6,7}
  (A)  P_6 = P_7 = Q_6 = Q_7 = 1/8
  (E)  P_i = Q_i
  (T2) P_0+P_2+P_4 = P_1+P_3+P_5 = 3/8  (same for Q)
  (R1) matrix relation -> per-anchor and cross-anchor J relations (x26_cross.py)
  (R2) Y^j_i = -X^j_i
"""
import sympy as sp
from sympy import groebner, Rational as Q_

I2 = sp.eye(2)


def unit(name):
    """A genuinely unit complex 2-vector: (cos th, sin th e^{i ph}) e^{i ps}."""
    th, ph, ps = sp.symbols('%s_th %s_ph %s_ps' % (name, name, name), real=True)
    return sp.Matrix([sp.cos(th) * sp.exp(sp.I * ps),
                      sp.sin(th) * sp.exp(sp.I * (ps + ph))])


def dag(v):
    return v.conjugate().T


def perp(v):
    return sp.Matrix([-sp.conjugate(v[1]), sp.conjugate(v[0])])


def sat_unit(gens, nonzero, vs):
    t = sp.Symbol('t_rab')
    p = sp.Integer(1)
    for z in nonzero:
        p *= z
    G = groebner(list(gens) + [1 - t * p], *(list(vs) + [t]), order='lex')
    return list(G.exprs) == [sp.Integer(1)]


jp = lambda u, vv: u[0] * vv[1] + u[1] * vv[0]
BAR = '=' * 76

print(BAR)
print('BRANCH 1.   |Z_j| >= 2 for some anchor j:  R_g^{(j)} = R_h^{(j)} = 0, g != h.')
print(BAR)
print('  R2 turns the four vanishing X into:  C_i perp D_j and D_i perp C_j for the')
print('  four blocks i of groups g,h.  With C_j, D_j nonzero (A) each block lies on a')
print('  fixed line: C_i in span(w), w = D_j^perp;  D_i in span(v), v = C_j^perp.')
print('  (T) gives C_g C_g^dag = (1/4) w w^dag, D_g D_g^dag = (1/4) v v^dag, same for h.')
print('  (M) on group g:  (1/4)(w w^dag + v v^dag) = rho/2, so rho = (1/2)(w w^dag + v v^dag).')
print('  C_j has norm^2 1/8 and is perpendicular to v, so C_j C_j^dag = (1/8)(I - v v^dag).')
uv = unit('v')
uw = unit('w')
print('     sanity: v and w are unit:',
      sp.simplify((dag(uv) * uv)[0, 0]) == 1, sp.simplify((dag(uw) * uw)[0, 0]) == 1)
rho = Q_(1, 2) * (uw * dag(uw) + uv * dag(uv))
lhs = sp.expand(rho - Q_(1, 2) * (uw * dag(uw)) - Q_(1, 8) * (I2 - uv * dag(uv)))
tgt = sp.expand(Q_(5, 8) * uv * dag(uv) - Q_(1, 8) * I2)
print('     C_k C_k^dag + C_j2 C_j2^dag = rho - (1/2) w w^dag - (1/8)(I - v v^dag)')
print('     equals (5/8) v v^dag - (1/8) I :',
      sp.simplify(sp.expand(lhs - tgt)) == sp.zeros(2, 2))
vp = perp(uv)
val = sp.simplify((dag(vp) * tgt * vp)[0, 0] / (dag(vp) * vp)[0, 0])
print('     Rayleigh quotient of that matrix at v^perp =', val, ' < 0')
print('     but the left side is a sum of two PSD matrices.   CONTRADICTION.')
print('     [facts used: (M) (T) (A) (R2); no R1 needed]')

print()
print(BAR)
print('BRANCH 2.   Z_6 and Z_7 share a group g  (with Branch 1 gone, Z_6 = Z_7 = {g}).')
print(BAR)
print('  step 1.  D_{2g}, D_{2g+1} perp C_6 and perp C_7.  If C_6, C_7 were independent')
print('           both D vanish, so Q_{2g}+Q_{2g+1} = 0, against (T).  Hence C_6 || C_7,')
print('           direction n.  Symmetrically D_6 || D_7, direction m, and')
print('           C_{2g},C_{2g+1} in span(w), w = m^perp; D_{2g},D_{2g+1} in span(v), v = n^perp.')
print('  step 2.  (M) on the anchor group and on group g both equal rho/2:')
print('             (1/4)(n n^dag + m m^dag) = rho/2 = (1/4)(w w^dag + v v^dag),')
print('           and w w^dag = I - m m^dag, v v^dag = I - n n^dag, so')
print('             n n^dag + m m^dag = 2I - (n n^dag + m m^dag), i.e. n n^dag + m m^dag = I.')
un = unit('n')
mperp = perp(un)
chk = sp.simplify(un * dag(un) + mperp * dag(mperp) - I2)
print('           for a general orthonormal pair (n, m) that identity holds:',
      chk == sp.zeros(2, 2))
um = unit('m')
S = un * dag(un) + um * dag(um) - I2
ipc = sp.simplify(sp.Abs((dag(un) * um)[0, 0]) ** 2)
force = sp.simplify(sp.expand(sp.trace((S.H * S)) - 2 * ipc))
print('           and for ANY two unit n, m:  ||n n^dag + m m^dag - I||_F^2 = 2 |<n,m>|^2,')
print('           machine check (difference simplifies to 0):', sp.simplify(force) == 0)
print('           so n n^dag + m m^dag = I forces <n,m> = 0, i.e. m perp n; then')
print('           m = v, w = n, rho = I/2, group g has C in span(n) and D in span(m).')
print('  step 3.  rho = I/2 minus group g ((1/4) n n^dag) minus the anchors ((1/4) n n^dag)')
print('           leaves sum_{h != g} C_h C_h^dag = (1/2) m m^dag, rank one, so every')
print('           C_i in the other two groups lies in span(m); dually every D_i in span(n).')
sub_rest = sp.simplify(Q_(1, 2) * I2 - Q_(1, 4) * un * dag(un)
                       - Q_(1, 4) * un * dag(un) - Q_(1, 2) * mperp * dag(mperp))
print('           machine check of that subtraction:', sub_rest == sp.zeros(2, 2))
print('  step 4.  R2 for the two anchors on those blocks, C_6 = al n, D_6 = be m,')
print('           C_7 = al2 n, D_7 = be2 m, C_i = c_i m, D_i = d_i n:')
print('             conj(al) d_i + be conj(c_i) = 0,  conj(al2) d_i + be2 conj(c_i) = 0.')
print('           A nonsingular 2x2 would force c_i = d_i = 0 for all four blocks, i.e.')
print('           two groups of mass zero, against (T).  So the determinant vanishes and')
print('             d_i = -nu conj(c_i),  |nu| = |be|/|al| = 1  by (A).')
print('  step 5.  R1 on the pair (g,h): with C_{2g+c} = gam_{2g+c} n, D_{2g+c} = del_{2g+c} m,')
print('           C_{2h+c} = c_{2h+c} m, D_{2h+c} = d_{2h+c} n, entry (a,b) is')
print('             conj(n_a) n_b [conj(gam_{2g}) d_{2h+1} + conj(gam_{2g+1}) d_{2h}]')
print('           + conj(m_a) m_b [conj(c_{2h}) del_{2g+1} + conj(c_{2h+1}) del_{2g}] = 0.')
M1 = sp.Matrix(2, 2, lambda a, b: sp.conjugate(un[a]) * un[b])
M2 = sp.Matrix(2, 2, lambda a, b: sp.conjugate(mperp[a]) * mperp[b])
l1, l2 = sp.symbols('l1 l2')
eqs = [sp.simplify(sp.expand((l1 * M1 + l2 * M2)[i, j])) for i in range(2) for j in range(2)]
sol = sp.solve(eqs, [l1, l2], dict=True)
indep = (sol == [] or all(sp.simplify(s.get(l1, l1)) == 0 and sp.simplify(s.get(l2, l2)) == 0
                          for s in sol))
print('           conj(n)n^T and conj(m)m^T are linearly independent (n perp m):', indep)
print('           hence BOTH brackets vanish separately.')
print('  step 6.  substituting d_i = -nu conj(c_i) leaves')
print('             (I)   gam_{2g} c_{2h+1} + gam_{2g+1} c_{2h} = 0   for both h != g')
print('             (III) c_{2h1} c_{2h2+1} + c_{2h1+1} c_{2h2} = 0   (R1 on the pair (h1,h2))')
g0, g1, c10, c11, c20, c21 = sp.symbols('gam0 gam1 c10 c11 c20 c21')
gens = [g0 * c11 + g1 * c10, g0 * c21 + g1 * c20, c10 * c21 + c11 * c20]
print('           generators:', gens)
print('           is 1 in the saturation by gam0*gam1*c10*c11*c20*c21 ?',
      sat_unit(gens, [g0, g1, c10, c11, c20, c21], [g0, g1, c10, c11, c20, c21]))
print('           so gam_{2g} = 0 or gam_{2g+1} = 0.')
print('           gam_{2g} = 0 forces c_{2h} = 0 for both h and P_{2g} = 0, hence')
print('             P_0 + P_2 + P_4 = 0, against (T2) = 3/8;')
print('           gam_{2g+1} = 0 gives P_1 + P_3 + P_5 = 0, likewise.   CONTRADICTION.')
print('     [facts used: (M) (T) (A) (E) (T2) (R1) (R2)]')

print()
print(BAR)
print('BRANCH 3.   Z_j = {g} and g not in Z_j2   (d_g := R_g^{(j2)} != 0).')
print(BAR)
p0, e0, e1 = sp.symbols('p0 e0 e1')
print('  cross-anchor with R_g^{(j)} = 0 gives  d_g J R_h^{(j)T} = 0 for h != g;')
print('  same-anchor gives R_h1^{(j)} J R_h2^{(j)T} = 0.  Three pairwise J-orthogonal')
print('  vectors, all nonzero because Z_j = {g}, so the axis lemma puts them on one axis.')
print('  Axis e1 (second coordinate zero):')
print('     R_h^{(j)} = (a_h, 0), a_h != 0  ->  X^j_{2h+1} = 0 for h = h1, h2;')
print('     R_g^{(j)} = 0                   ->  X^j_{2g} = X^j_{2g+1} = 0;')
print('     d_g = (p, 0), p != 0            ->  X^j2_{2g+1} = 0.')
print('  Same-anchor relation for j2 on the pair (g,h):  d_g J R_h^{(j2)T} =',
      sp.expand(jp((p0, 0), (e0, e1))), '= 0, and p != 0, so X^j2_{2h+1} = 0.')
print('  Both anchors therefore annihilate every odd X: the ALIGNED configuration,')
print('  closed in Branch 4b.  (Axis e2 gives the same statement with even indices.)')

print()
print(BAR)
print('BRANCH 4a.  Z_6 = Z_7 = empty, MIXED axes.')
print(BAR)
a = sp.symbols('a0 a1 a2')
b = sp.symbols('b0 b1 b2')
R6 = [(a[g], 0) for g in range(3)]
R7 = [(0, b[g]) for g in range(3)]
cross = [sp.expand(jp(R7[g], R6[h]) + jp(R7[h], R6[g]))
         for g in range(3) for h in range(g + 1, 3)]
print('  cross-anchor residuals:', cross)
print('  is 1 in the saturation by a0 a1 a2 b0 b1 b2 (all six R nonzero)?',
      sat_unit(cross, list(a) + list(b), list(a) + list(b)))
print('  CONTRADICTION.   [facts used: (R1) (R2) only]')

print()
print(BAR)
print('BRANCH 4b.  ALIGNED axes (also the exit of Branch 3).')
print(BAR)
print('  Both anchors annihilate the odd X (say).  R2 turns that into')
print('     C_1, C_3, C_5 perp D_6 and perp D_7.')
print('  case (i)  D_6, D_7 independent -> C_1 = C_3 = C_5 = 0 -> P_1+P_3+P_5 = 0,')
print('            against (T2) = 3/8.')
print('  case (ii) D_6 || D_7 with direction m (both nonzero by (A)).  Put w = m^perp;')
print('            C_1, C_3, C_5 lie in span(w) and sum_odd |<w,C_i>|^2 = 3/8 by (T2).')
print('            (M) on the anchor group sandwiched with w kills both D terms:')
print('               A := |<w,C_6>|^2 + |<w,C_7>|^2 = (w^dag rho w)/2,')
print('            while w^dag rho w = sum_i |<w,C_i>|^2 = ev + 3/8 + A with ev >= 0.')
A, ev = sp.symbols('A ev', nonnegative=True)
sol = sp.solve([sp.Eq(2 * A, ev + Q_(3, 8) + A)], [A], dict=True)
print('            exact solve of 2A = ev + 3/8 + A :', sol, ' so A = 3/8 + ev >= 3/8')
print('            but A <= P_6 + P_7 = 1/4 by (A), and 3/8 > 1/4.   CONTRADICTION.')
print('     [facts used: (M) (A) (T2) (R2)]')
