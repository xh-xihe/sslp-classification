"""Symbolic verification of every algebraic step used by orbits 49 and 51.

Each check prints the residual of a claimed polynomial identity; every residual
must be exactly 0.  Nothing here divides by anything.

Run:  python tools/run.py generators/ver4951.py
"""
from sympy import symbols, expand, simplify, Rational, solve, Matrix

u = symbols('u0:10')
v = symbols('v0:10')

R = Rational
ok = True


def chk(name, expr):
    global ok
    e = expand(expr)
    print('%-46s residual = %s' % (name, e))
    if e != 0:
        ok = False


print('=== ENDGAME identity (Triangle.pair_prod_eq_zero) ===')
A, B, C, D, E, F = symbols('A B C D E F')
h1 = A * F + B * E
h2 = C * F + D * E
h3 = A * D + B * C
chk('E*B*C = (C/2)h1 - (A/2)h2 + (E/2)h3',
    E * B * C - ((C / 2) * h1 - (A / 2) * h2 + (E / 2) * h3))

print()
print('=== ORBIT 49 ===')
# reciprocal relations rec_i : u8*v_i + u_i*v8 = 0   (i = 0..7)
rec = [u[8] * v[i] + u[i] * v[8] for i in range(8)]

# rank-one masks
mk1 = u[3] * v[0] + u[2] * v[1] + u[1] * v[2] + u[0] * v[3]   # e = 110000
mk2 = u[5] * v[0] + u[4] * v[1] + u[1] * v[4] + u[0] * v[5]   # e = 101000
mk3 = u[5] * v[2] + u[4] * v[3] + u[3] * v[4] + u[2] * v[5]   # e = 100001
mk4 = u[7] * v[0] + u[6] * v[1] + u[1] * v[6] + u[0] * v[7]   # e = 011000

chk('(u0u3+u1u2)*v8 from mk1',
    (u[0] * u[3] + u[1] * u[2]) * v[8]
    - (-u[8] / 2 * mk1 + u[3] / 2 * rec[0] + u[2] / 2 * rec[1]
       + u[1] / 2 * rec[2] + u[0] / 2 * rec[3]))
chk('(u0u5+u1u4)*v8 from mk2',
    (u[0] * u[5] + u[1] * u[4]) * v[8]
    - (-u[8] / 2 * mk2 + u[5] / 2 * rec[0] + u[4] / 2 * rec[1]
       + u[1] / 2 * rec[4] + u[0] / 2 * rec[5]))
chk('(u2u5+u3u4)*v8 from mk3',
    (u[2] * u[5] + u[3] * u[4]) * v[8]
    - (-u[8] / 2 * mk3 + u[5] / 2 * rec[2] + u[4] / 2 * rec[3]
       + u[3] / 2 * rec[4] + u[2] / 2 * rec[5]))
chk('(u0u7+u1u6)*v8 from mk4',
    (u[0] * u[7] + u[1] * u[6]) * v[8]
    - (-u[8] / 2 * mk4 + u[7] / 2 * rec[0] + u[6] / 2 * rec[1]
       + u[1] / 2 * rec[6] + u[0] / 2 * rec[7]))

print()
print('--- orbit 49 moment pinning ---')
q = symbols('q0:10')
# linear facts available from the moment system
# q0+q1 = q2+q3 = q4+q5 = q6+q7 = 1/6 ,  q0+q2+q4+q6 = 1/3
sub = {q[1]: R(1, 6) - q[0], q[3]: R(1, 6) - q[2],
       q[5]: R(1, 6) - q[4], q[7]: R(1, 6) - q[6]}
e1 = (q[0] * q[3] - q[1] * q[2]).subs(sub)
e2 = (q[0] * q[5] - q[1] * q[4]).subs(sub)
e3 = (q[0] * q[7] - q[1] * q[6]).subs(sub)
chk('q0 - q2 = 6*e1', (q[0] - q[2]) - 6 * e1)
chk('q0 - q4 = 6*e2', (q[0] - q[4]) - 6 * e2)
chk('q0 - q6 = 6*e3', (q[0] - q[6]) - 6 * e3)
solq = solve([q[0] - q[2], q[0] - q[4], q[0] - q[6],
              q[0] + q[2] + q[4] + q[6] - R(1, 3)], list(q[:8]), dict=True)
print('  pinned point:', solq)

print()
print('=== ORBIT 51 ===')
A1 = u[9] * v[0] - u[0] * v[9]
A2 = u[8] * v[1] + u[0] * v[9]
A3 = u[1] * v[8] + u[0] * v[9]
B1 = u[9] * v[2] - u[2] * v[9]
B2 = u[8] * v[3] + u[2] * v[9]
B3 = u[3] * v[8] + u[2] * v[9]
M = u[3] * v[0] + u[2] * v[1] + u[1] * v[2] + u[0] * v[3]
C1 = u[8] * v[6] + u[6] * v[8]
C2 = u[9] * v[7] + u[7] * v[9]
D1 = u[9] * v[6] + u[6] * v[9]
D2 = u[8] * v[7] + u[7] * v[8]
W = u[8] * v[9] - u[9] * v[8]

chk('v6*W = v9*C1 - v8*D1', v[6] * W - (v[9] * C1 - v[8] * D1))
chk('v7*W = v9*D2 - v8*C2', v[7] * W - (v[9] * D2 - v[8] * C2))

# with W = 0 : G1 = u0u9 + u1u8 , G2 = u2u9 + u3u8
chk('(u0u9+u1u8)*v8 = u8*A3 - u0*W',
    (u[0] * u[9] + u[1] * u[8]) * v[8] - (u[8] * A3 - u[0] * W))
chk('(u2u9+u3u8)*v8 = u8*B3 - u2*W',
    (u[2] * u[9] + u[3] * u[8]) * v[8] - (u[8] * B3 - u[2] * W))

# the mask identity  u8*u9*M = (u0u3+u1u2)*(u8v9 + u9v8)  modulo A1,A2-A3,B1,B2-B3
IDEAL = (u[8]*u[3]*A1 + u[9]*u[2]*(A2 - A3) + u[8]*u[1]*B1 + u[9]*u[0]*(B2 - B3))
chk('u8u9*M - (u0u3+u1u2)(u8v9+u9v8) = ideal',
    u[8]*u[9]*M - (u[0]*u[3] + u[1]*u[2])*(u[8]*v[9] + u[9]*v[8]) - IDEAL)
# and with W = 0 the right factor is 2*u8*v9
chk('2*(u0u3+u1u2)*u8*v9 from M and W',
    2*(u[0]*u[3] + u[1]*u[2])*u[8]*v[9]
    - (u[8]*u[9]*M - IDEAL + (u[0]*u[3] + u[1]*u[2])*W))

print()
print('--- orbit 51 moment pinning ---')
q = symbols('q0:10')
r = symbols('r0:10')
a, b = q[0], q[2]
subs51 = {q[1]: R(1, 6) - a, q[3]: R(1, 6) - b,
          r[8]: R(1, 3) - a - b, r[9]: a + b}
f1 = (q[1] * r[8] - q[0] * r[9]).subs(subs51)
f2 = (q[3] * r[8] - q[2] * r[9]).subs(subs51)
chk('9q0+3q2-1 = -18*f1', (9 * a + 3 * b - 1) - (-18) * f1)
chk('3q0+9q2-1 = -18*f2', (3 * a + 9 * b - 1) - (-18) * f2)
print('  solve:', solve([9 * a + 3 * b - 1, 3 * a + 9 * b - 1], [a, b]))

print()
print('ALL RESIDUALS ZERO' if ok else 'FAILURE')
