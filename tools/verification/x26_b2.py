"""Branch 2, steps 5 and 6, done symbolically instead of in prose.

Configuration reached at the end of step 3:
    n perp m, both unit;  rho = I/2
    group g   :  C_{2g+c} = gam_{2g+c} n ,  D_{2g+c} = del_{2g+c} m
    groups h  :  C_{2h+c} = c_{2h+c} m   ,  D_{2h+c} = d_{2h+c} n     (h = h1, h2)
    step 4    :  d_i = -nu conj(c_i)  for i in h1 u h2, nu != 0.
R1 is taken verbatim from the fact list:
    E_ab(g,h) = sum_c conj((C_{2g+c})_a)(D_{2h+1-c})_b
              + sum_c conj((C_{2h+c})_a)(D_{2g+1-c})_b = 0.
Conjugates are carried as independent symbols; R1 is bilinear so that is sound.
"""
import sympy as sp
from sympy import groebner

# independent symbols for the two orthonormal directions and their conjugates
n = sp.symbols('n0 n1')
m = sp.symbols('m0 m1')
cn = sp.symbols('cn0 cn1')     # conj(n)
cm = sp.symbols('cm0 cm1')     # conj(m)

gam = sp.symbols('gam0 gam1')          # C of group g,  index 2g, 2g+1
cgam = sp.symbols('cgam0 cgam1')       # conj
dele = sp.symbols('del0 del1')         # D of group g
c1 = sp.symbols('c10 c11')             # C of group h1
c2 = sp.symbols('c20 c21')             # C of group h2
cc1 = sp.symbols('cc10 cc11')
cc2 = sp.symbols('cc20 cc21')
d1 = sp.symbols('d10 d11')             # D of group h1
d2 = sp.symbols('d20 d21')             # D of group h2

# C_i as (scalar, direction, conj-direction), D_i as (scalar, direction)
CG = {0: (cgam[0], cn), 1: (cgam[1], cn)}          # conj(C) of group g
DG = {0: (dele[0], m), 1: (dele[1], m)}
CH = {('h1', 0): (cc1[0], cm), ('h1', 1): (cc1[1], cm),
      ('h2', 0): (cc2[0], cm), ('h2', 1): (cc2[1], cm)}
DH = {('h1', 0): (d1[0], n), ('h1', 1): (d1[1], n),
      ('h2', 0): (d2[0], n), ('h2', 1): (d2[1], n)}


def E_gh(h, a, b):
    """R1 entry for the pair (g, h), h in {h1, h2}."""
    t = 0
    for c in (0, 1):
        s, dirn = CG[c]
        t += s * dirn[a] * DH[(h, 1 - c)][0] * DH[(h, 1 - c)][1][b]
        s2, dir2 = CH[(h, c)]
        t += s2 * dir2[a] * DG[1 - c][0] * DG[1 - c][1][b]
    return sp.expand(t)


def E_hh(a, b):
    """R1 entry for the pair (h1, h2)."""
    t = 0
    for c in (0, 1):
        s, dirn = CH[('h1', c)]
        t += s * dirn[a] * DH[('h2', 1 - c)][0] * DH[('h2', 1 - c)][1][b]
        s2, dir2 = CH[('h2', c)]
        t += s2 * dir2[a] * DH[('h1', 1 - c)][0] * DH[('h1', 1 - c)][1][b]
    return sp.expand(t)


print('=' * 76)
print('STEP 5.  R1(g,h) separates into a conj(n)n^T part and a conj(m)m^T part')
print('=' * 76)
for h, dh in [('h1', d1), ('h2', d2)]:
    br_n = sp.expand(cgam[0] * dh[1] + cgam[1] * dh[0])
    ch = cc1 if h == 'h1' else cc2
    br_m = sp.expand(ch[0] * dele[1] + ch[1] * dele[0])
    ok = True
    for a in (0, 1):
        for b in (0, 1):
            got = E_gh(h, a, b)
            tgt = sp.expand(cn[a] * n[b] * br_n + cm[a] * m[b] * br_m)
            ok = ok and sp.expand(got - tgt) == 0
    print('  pair (g,%s):  E_ab = conj(n_a) n_b [%s] + conj(m_a) m_b [%s]   exact: %s'
          % (h, br_n, br_m, ok))
print('  conj(n)n^T and conj(m)m^T are independent (n perp m, both nonzero), so each')
print('  bracket vanishes on its own:')
print('    (I)  conj(gam_{2g}) d_{2h+1} + conj(gam_{2g+1}) d_{2h} = 0')
print('    (II) conj(c_{2h}) del_{2g+1} + conj(c_{2h+1}) del_{2g} = 0')

print()
print('=' * 76)
print('STEP 5b.  R1(h1,h2) is a single bracket times conj(m) n^T')
print('=' * 76)
brk = sp.expand(cc1[0] * d2[1] + cc1[1] * d2[0] + cc2[0] * d1[1] + cc2[1] * d1[0])
ok = all(sp.expand(E_hh(a, b) - cm[a] * n[b] * brk) == 0 for a in (0, 1) for b in (0, 1))
print('  E_ab = conj(m_a) n_b [%s]   exact: %s' % (brk, ok))
print('  conj(m) n^T is a nonzero matrix, so   (III)  that bracket = 0.')

print()
print('=' * 76)
print('STEP 6.  substitute  d_i = -nu conj(c_i)  (step 4) and conjugate')
print('=' * 76)
nu = sp.Symbol('nu')
sub = {d1[0]: -nu * cc1[0], d1[1]: -nu * cc1[1], d2[0]: -nu * cc2[0], d2[1]: -nu * cc2[1]}
I_h1 = sp.expand((cgam[0] * d1[1] + cgam[1] * d1[0]).subs(sub))
I_h2 = sp.expand((cgam[0] * d2[1] + cgam[1] * d2[0]).subs(sub))
III = sp.expand(brk.subs(sub))
print('  (I)  h1 becomes ', I_h1, '  -> divide by -nu and conjugate:  gam0*c11 + gam1*c10 = 0')
print('  (I)  h2 becomes ', I_h2, '  -> conjugate:                    gam0*c21 + gam1*c20 = 0')
print('  (III)     becomes ', III, '  -> conjugate:  c10*c21 + c11*c20 = 0')
print('  (the factor 2 in (III) confirms the two middle terms coincide, i.e. the')
print('   bracket is genuinely the J-form of the two c vectors, not a cancellation)')

g0, g1 = sp.symbols('G0 G1')
u10, u11, u20, u21 = sp.symbols('u10 u11 u20 u21')
gens = [g0 * u11 + g1 * u10, g0 * u21 + g1 * u20, u10 * u21 + u11 * u20]
vs = [g0, g1, u10, u11, u20, u21]
t = sp.Symbol('t_rab')
G = groebner(gens + [1 - t * g0 * g1 * u10 * u11 * u20 * u21], *(vs + [t]), order='lex')
print()
print('  final system:', gens)
print('  Groebner basis of the Rabinowitsch ideal (saturate by all six nonzero):',
      list(G.exprs))
print('  unit ideal:', list(G.exprs) == [sp.Integer(1)])
print()
print('  by hand, machine-confirmed:  (I) forces (c_{2h}, c_{2h+1}) = sigma_h (gam0, -gam1),')
sg1, sg2 = sp.symbols('sig1 sig2')
lhs = sp.expand((sg1 * g0) * (-sg2 * g1) + (-sg1 * g1) * (sg2 * g0))
print('   and then (III) reads  sigma_1 sigma_2 * (%s) = %s'
      % (sp.expand(lhs / (sg1 * sg2)), lhs))
print('   so gam0*gam1 = 0, contradicting "both nonzero".')
print('   The remaining cases gam0 = 0 and gam1 = 0 kill P_0+P_2+P_4 resp. P_1+P_3+P_5,')
print('   both of which (T2) pins at 3/8.')
