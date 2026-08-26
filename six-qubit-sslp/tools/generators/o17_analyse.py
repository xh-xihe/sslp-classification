"""Orbit 17 analysis: fibers, moment normal form, KL rows, hafnian ideal.

(q, m, a) = (4, 2, (1,1,1,1,1,1)), delta = 2.
"""
from fractions import Fraction as F
from itertools import combinations

from sympy import Matrix, Rational, zeros

from orbit import fiber
from kl import dressings_full, flips
from scan import bits, xor, dot

N = 6
A = [1] * 6
Q = 4

S0 = fiber(A, Q, 0)
S1 = fiber(A, Q, 2)
print('S0 (%d):' % len(S0), S0)
print('S1 (%d):' % len(S1), S1)

EDGES = list(combinations(range(6), 2))
print('edges', len(EDGES))


def estr(e):
    return ''.join('1' if i in e else '0' for i in range(6))


def cstr(e):
    return ''.join('0' if i in e else '1' for i in range(6))


# index maps
i0 = {s: k for k, s in enumerate(S0)}
i1 = {s: k for k, s in enumerate(S1)}

print('anchor bottom (empty) index', i0['000000'])
print('anchor top (V) index', i1['111111'])
for e in EDGES:
    assert cstr(e) in i0, e
    assert estr(e) in i1, e

# ---------------------------------------------------------------- moments
def ind(s, i):
    return 1 if s[i] == '1' else 0

rows, rhs, lab = [], [], []
rows.append([1] * 16 + [0] * 16); rhs.append(1); lab.append('n0')
rows.append([0] * 16 + [1] * 16); rhs.append(1); lab.append('n1')
for i in range(6):
    rows.append([ind(x, i) for x in S0] + [-ind(y, i) for y in S1])
    rhs.append(0); lab.append('m%d' % (i + 1))
for (i, j) in combinations(range(6), 2):
    rows.append([ind(x, i) * ind(x, j) for x in S0] + [-ind(y, i) * ind(y, j) for y in S1])
    rhs.append(0); lab.append('m%d%d' % (i + 1, j + 1))

M = Matrix(rows)
b = Matrix(rhs)
print('moment matrix', M.shape, 'rank', M.rank())

# Solve: is a given linear functional implied?  Solve  w^T M = target^T
def implied(target_vec, target_rhs, name):
    """Is  target . p = target_rhs  a consequence of M p = b ?"""
    sol = M.T.solve_least_squares(Matrix(target_vec))
    resid = (M.T * sol - Matrix(target_vec))
    if any(r != 0 for r in resid):
        print('  NOT implied:', name)
        return None
    val = (sol.T * b)[0, 0]
    ok = (val == target_rhs)
    print('  %-28s implied, value %s  %s' % (name, val, 'OK' if ok else 'MISMATCH %s' % target_rhs))
    return sol

print('linear consequences of the moment system:')
# |a|^2 = q_[000000] = 1/4
t = [0] * 32; t[i0['000000']] = 1
implied(t, Rational(1, 4), 'q(empty) = 1/4')
# |b|^2 = r_[111111] = 1/4
t = [0] * 32; t[16 + i1['111111']] = 1
implied(t, Rational(1, 4), 'r(V) = 1/4')
# degree sums
for v in range(6):
    t = [0] * 32
    for e in EDGES:
        if v in e:
            t[i0[cstr(e)]] = 1
    implied(t, Rational(1, 4), 'bottom degree at %d = 1/4' % v)
for v in range(6):
    t = [0] * 32
    for e in EDGES:
        if v in e:
            t[16 + i1[estr(e)]] = 1
    implied(t, Rational(1, 4), 'top degree at %d = 1/4' % v)
# x_e = y_e
for e in EDGES[:3]:
    t = [0] * 32
    t[i0[cstr(e)]] = 1
    t[16 + i1[estr(e)]] = -1
    implied(t, Rational(0, 1), 'x_%s - y_%s = 0' % (e, e))

# ---------------------------------------------------------------- KL rows
print()
print('KL incidence structure (off-diagonal), by flip mask:')
seen = {}
for e in flips():
    off = [(xor(y, e), y) for y in S1 if xor(y, e) in S0]
    if not off:
        continue
    seen[e] = off
    print('  e=%s  |inc|=%d  dressings=%d' % (e, len(off), len(dressings_full(e))))
print('masks with off-diagonal incidences:', len(seen))
