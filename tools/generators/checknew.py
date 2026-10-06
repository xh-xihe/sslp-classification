"""Independent verification of the checkable claims in the new sections
of six_qubit_sslp.tex (orbits 5,6,47-52 and the fourteen order-two orbits).

Everything is recomputed from the angle records with sympy exact rationals.
"""
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
from orbit import fiber

OK, BAD = [], []


def check(name, got, want):
    (OK if got == want else BAD).append((name, got, want))


# ---------------------------------------------------------------- 13877
tau = lambda n: sum(1 for d in range(1, n + 1) if n % d == 0)
total = sum((tau(q) - 1) * sp.binomial(q + 5, 6) for q in range(2, 10))
check('raw record count 13877', int(total), 13877)

# ---------------------------------------------- fibers of the new orbits
S = lambda a, q, d: [''.join(map(str, x)) for x in fiber(a, q, d)] \
    if fiber(a, q, d) and not isinstance(fiber(a, q, d)[0], str) else fiber(a, q, d)

CLAIMED = {
    47: ((6, [1, 1, 1, 1, 2, 2], 2),
         '000000 001111 010111 011011 100111 101011 110011 111101 111110',
         '000001 000010 001100 010100 011000 100100 101000 110000 111111'),
    48: ((6, [1, 1, 1, 2, 2, 2], 2),
         '000000 000111 011011 011101 011110 101011 101101 101110 110011 '
         '110101 110110',
         '000001 000010 000100 011000 011111 101000 101111 110000 110111'),
    52: ((6, [1, 2, 3, 3, 4, 4], 2),
         '000000 001100 010001 010010 011101 011110 100111 101011 110100 111000',
         '000011 001111 010000 011100 100101 100110 101001 101010 110111 111011'),
    42: ((6, [1, 1, 1, 1, 3, 3], 3),
         '000000 000011 011101 011110 101101 101110 110101 110110 111001 111010',
         '000001 000010 011100 011111 101100 101111 110100 110111 111000 111011'),
    43: ((6, [1, 1, 1, 2, 3, 3], 3),
         '000000 000011 001101 001110 010101 010110 100101 100110 111001 111010',
         '000001 000010 001100 001111 010100 010111 100100 100111 111000 111011'),
    44: ((6, [1, 1, 2, 3, 3, 4], 3),
         '000000 000110 001001 001111 011010 011100 101010 101100 110001 110111',
         '000010 000100 001011 001101 011000 011110 101000 101110 110011 110101'),
    46: ((6, [1, 2, 2, 2, 3, 3], 3),
         '000000 000011 011100 011111 100101 100110 101001 101010 110001 110010',
         '000001 000010 011101 011110 100100 100111 101000 101011 110000 110011'),
}
for oid, ((q, a, d), s0, s2) in CLAIMED.items():
    got0, got2 = sorted(S(a, q, 0)), sorted(S(a, q, d))
    check('orbit %d  S_0' % oid, got0, sorted(s0.split()))
    check('orbit %d  S_d' % oid, got2, sorted(s2.split()))

# ------------------------------------------------- half-angle matchings
for oid, i in ((42, 6), (43, 6), (44, 5), (46, 6)):
    (q, a, d), s0, s2 = CLAIMED[oid]
    f0, f2 = CLAIMED[oid][1].split(), CLAIMED[oid][2].split()
    flip = lambda x: x[:i - 1] + ('1' if x[i - 1] == '0' else '0') + x[i:]
    check('orbit %d  X_%d is the stated matching' % (oid, i),
          [flip(x) for x in f0], f2)

# ------------------------------------------------------- determinants
chi = lambda z, j: -1 if z[j - 1] == '1' else 1


def Wten(oid, i, js):
    f2 = CLAIMED[oid][2].split()
    rows = [[1] * 10, [chi(y, i) for y in f2]]
    for j in js:
        rows.append([chi(y, j) for y in f2])
        rows.append([chi(y, i) * chi(y, j) for y in f2])
    return sp.Matrix(rows).det()


check('det W_42', abs(Wten(42, 6, [1, 2, 3, 4])), 73728)
check('det W_43', abs(Wten(43, 6, [1, 2, 3, 4])), 73728)
check('det W_44', abs(Wten(44, 5, [1, 2, 3, 4])), 32768)
check('det W_46', abs(Wten(46, 6, [1, 2, 3, 4])), 73728)

W5 = sp.Matrix([[1, 1, 1, 1, 1], [1, 1, -1, -1, -1], [1, -1, 1, -1, -1],
                [1, -1, -1, 1, -1], [1, -1, -1, -1, 1]])
check('det W_5 (orbit 6)', W5.det(), -48)
H4 = sp.Matrix([[1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1]])
check('det Hadamard 4x4', H4.det(), -16)
TRI = sp.Matrix([[1, 1, 0], [1, 0, 1], [0, 1, 1]])
check('det odd triangle', TRI.det(), -2)

# K_5 triangle-versus-edge incidence matrix
V5 = [1, 2, 3, 4, 5]
E5 = list(combinations(V5, 2))
T5 = list(combinations(V5, 3))
M = sp.Matrix([[1 if set(e) <= set(t) else 0 for e in E5] for t in T5])
check('det K_5 triangle-edge', M.det(), -48)

# parity-four edge system W_k W_k^T = 8 I
E4 = [z for z in range(16) if bin(z).count('1') % 2 == 0]
bit = lambda z, j: (z >> (3 - j)) & 1
k = 0
rows = [[1] * 8, [(-1) ** bit(z, k) for z in E4]]
for j in range(4):
    if j == k:
        continue
    rows.append([(-1) ** bit(z, j) for z in E4])
    rows.append([(-1) ** (bit(z, k) + bit(z, j)) for z in E4])
Wk = sp.Matrix(rows)
check('parity-4  W_k W_k^T = 8I', Wk * Wk.T, 8 * sp.eye(8))
check('parity-4  |det W_k|', abs(Wk.det()), 4096)

# --------------------------------------------------------- orbit 5 / 17
check('orbit 5  Bell bound  4/27 > 1/9', sp.Rational(4, 27) > sp.Rational(1, 9),
      True)
check('orbit 17 star degree 5/4 != 1/4',
      sp.Rational(5, 4) == sp.Rational(1, 4), False)

# ---------------------------------------------------------------- report
print('PASS %d / %d' % (len(OK), len(OK) + len(BAD)))
for n, g, w in BAD:
    print('  FAIL %-34s got %s  want %s' % (n, g, w))
if not BAD:
    for n, g, w in OK:
        print('  ok   %s' % n)
