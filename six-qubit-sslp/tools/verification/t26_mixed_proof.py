"""Symbolic check of the MIXED-branch reduction.

Mixed branch, anchor 6 kills the odd X's and anchor 7 the even ones:
    C_6^dag D_1 = C_6^dag D_3 = C_6^dag D_5 = 0,
    C_7^dag D_0 = C_7^dag D_2 = C_7^dag D_4 = 0.
With R2 this makes
    C_1, C_3, C_5  perp D_6      ->  all parallel, C_{2k+1} = c_{2k+1} w6
    C_0, C_2, C_4  perp D_7      ->  all parallel, C_{2k}   = c_{2k}   w7
    D_1, D_3, D_5  perp C_6      ->  all parallel, D_{2k+1} = d_{2k+1} v6
    D_0, D_2, D_4  perp C_7      ->  all parallel, D_{2k}   = d_{2k}   v7
(C_6, C_7, D_6, D_7 are nonzero because P_6 = P_7 = Q_6 = Q_7 = 1/8.)

Claim: each R1 matrix identity then collapses to
    [conj(c_even) d_odd + conj(c_even') d_odd'] * conj(w7) v6^T
  + [conj(c_odd)  d_even + conj(c_odd')  d_even'] * conj(w6) v7^T = 0.
Conjugates are treated as independent symbols -- the identity is bilinear, so
that is sound.
"""
import sympy as sp

w6 = sp.symbols('w6_0 w6_1'); w7 = sp.symbols('w7_0 w7_1')
v6 = sp.symbols('v6_0 v6_1'); v7 = sp.symbols('v7_0 v7_1')
cw6 = sp.symbols('cw6_0 cw6_1'); cw7 = sp.symbols('cw7_0 cw7_1')   # conjugates
c = sp.symbols('c0:6'); d = sp.symbols('d0:6')
cc = sp.symbols('cc0:6')                                            # conj(c_i)

C = {0: (c[0], cw7), 2: (c[2], cw7), 4: (c[4], cw7),
     1: (c[1], cw6), 3: (c[3], cw6), 5: (c[5], cw6)}
CONJ = {0: cc[0], 1: cc[1], 2: cc[2], 3: cc[3], 4: cc[4], 5: cc[5]}
D = {0: (d[0], v7), 2: (d[2], v7), 4: (d[4], v7),
     1: (d[1], v6), 3: (d[3], v6), 5: (d[5], v6)}


def conjC(i, a):
    return CONJ[i] * C[i][1][a]


def Dv(i, b):
    return D[i][0] * D[i][1][b]


BASIS = {}
for a in (0, 1):
    for b in (0, 1):
        BASIS[(a, b)] = {'w7v6': cw7[a] * v6[b], 'w6v7': cw6[a] * v7[b]}

print('R1 residual, entry by entry, for each cycle-group pair:')
scalars = {}
for (g, h) in [(0, 1), (0, 2), (1, 2)]:
    coefs = set()
    for a in (0, 1):
        for b in (0, 1):
            expr = 0
            for cidx in (0, 1):
                expr += conjC(2 * g + cidx, a) * Dv(2 * h + 1 - cidx, b)
                expr += conjC(2 * h + cidx, a) * Dv(2 * g + 1 - cidx, b)
            expr = sp.expand(expr)
            A = sp.expand(expr.coeff(cw7[a]).coeff(v6[b]))
            B = sp.expand(expr.coeff(cw6[a]).coeff(v7[b]))
            rest = sp.expand(expr - A * cw7[a] * v6[b] - B * cw6[a] * v7[b])
            assert rest == 0, (g, h, a, b, rest)
            coefs.add((A, B))
    assert len(coefs) == 1, coefs
    A, B = coefs.pop()
    scalars[(g, h)] = (A, B)
    print('  pair (%d,%d):  [%s] * conj(w7)v6^T  +  [%s] * conj(w6)v7^T = 0' % (g, h, A, B))

print()
print('So, whenever conj(w7)v6^T and conj(w6)v7^T are linearly independent')
print('(equivalently NOT(w6 || w7 and v6 || v7)), R1 gives the six scalars:')
for k in scalars:
    print('   %s = 0' % scalars[k][0])
for k in scalars:
    print('   %s = 0' % scalars[k][1])

print()
print('Family 1 in J-orthogonal form, r_k = (conj(c_{2k}), d_{2k+1}):')
r = [(cc[0], d[1]), (cc[2], d[3]), (cc[4], d[5])]
for (k, l) in [(0, 1), (0, 2), (1, 2)]:
    jv = sp.expand(r[k][0] * r[l][1] + r[k][1] * r[l][0])
    tgt = scalars[[(0, 1), (0, 2), (1, 2)][[(0, 1), (0, 2), (1, 2)].index((k, l))]][0]
    print('   r_%d J r_%d^T = %s   equals the R1 scalar: %s' % (k, l, jv, sp.expand(jv - tgt) == 0))

print()
print('Family 2 in J-orthogonal form, s_k = (conj(c_{2k+1}), d_{2k}):')
s = [(cc[1], d[0]), (cc[3], d[2]), (cc[5], d[4])]
for (k, l) in [(0, 1), (0, 2), (1, 2)]:
    jv = sp.expand(s[k][0] * s[l][1] + s[k][1] * s[l][0])
    tgt = scalars[[(0, 1), (0, 2), (1, 2)][[(0, 1), (0, 2), (1, 2)].index((k, l))]][1]
    print('   s_%d J s_%d^T = %s   equals the R1 scalar: %s' % (k, l, jv, sp.expand(jv - tgt) == 0))

print()
print('CONSEQUENCE (same J-orthogonality lemma, one dimension down):')
print('  either some r_k = 0  ->  P_{2k} = P_{2k+1} = 0, killed by (T);')
print('  or all r_k lie on one axis -> c_0=c_2=c_4=0 (P_0+P_2+P_4=0) or')
print('     d_1=d_3=d_5=0 (P_1+P_3+P_5=0), both killed by (T2) = 3/8.')
print('  Same for s.  The MIXED branch therefore CLOSES on the verified facts.')

print()
print('--- degenerate sub-branch: w6 || w7 AND v6 || v7 ---')
print('  then C_0..C_5 all parallel to one w and D_0..D_5 all parallel to one v.')
print('  rho = sum_i C_i C_i^dag = (3/4) w w^dag + (1/4) u u^dag,  u = C_6/|C_6| = C_7/|C_7|')
print('  group identity for any cycle group g: (1/4)(w w^dag + v v^dag) = rho/2')
w, v = sp.symbols('W V', positive=True)
print('  => rho = (1/2)(w w^dag + v v^dag) = (1/4) I + (3/4) w w^dag - (1/4) v v^dag')
print('  => 3 v v^dag - w w^dag = I; applying to v gives 2 v = <w,v> w, so v || w,')
print('     and then 2 w w^dag = I, impossible in dimension two.  CLOSED.')
