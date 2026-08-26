"""Data for `SixQubit/Orbit5.lean`: fibers, the rows that are used, and the
rational combinations that isolate each target.

Layout of the two fibers (qubits 0,1 are the zero-angle pair `A`,
qubits 2..5 are the four active coordinates):

    Y[4*t + alpha]   t = 0..4  ->  u, a1, a2, a3, a4     alpha = 00,01,10,11
    Z[4*t + alpha]   t = 0..4  ->  b1, b2, b3, b4, v
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from orbit import fiber          # noqa: E402
from scan import xor, dot, bits  # noqa: E402

A = [0, 0, 1, 1, 1, 1]
Q = 3
T0 = ['0000', '0111', '1011', '1101', '1110']
T1 = ['1000', '0100', '0010', '0001', '1111']
AB = ['00', '01', '10', '11']

Y = [a + t for t in T0 for a in AB]
Z = [a + t for t in T1 for a in AB]

assert sorted(fiber(A, Q, 0)) == sorted(Y)
assert sorted(fiber(A, Q, 1)) == sorted(Z)

# active flip masks, as 6-bit strings
EFLIP = ['001000', '000100', '000010', '000001']          # e_1 .. e_4
AFLIP = {'A1': '100000', 'A2': '010000', 'A3': '110000'}  # flips inside A


def two_flip(i, j):
    """mask X_k X_l with {k,l} the complement of {i,j} in {0,1,2,3}"""
    rest = [t for t in range(4) if t not in (i, j)]
    m = ['0'] * 6
    for t in rest:
        m[2 + t] = '1'
    return ''.join(m)


def sgn(z, s):
    return -1 if dot(z, s) else 1


def off_row(e, z):
    """[(sign, bottom index, top index)] for offSum c d e z"""
    out = []
    for t, y in enumerate(Z):
        x = xor(y, e)
        if x in Y:
            out.append((sgn(z, y), Y.index(x), t))
    return out


def diag_row(e, z, top):
    """[(sign, partner index, index)] for diagTop / diagBot"""
    S = Z if top else Y
    out = []
    for i, s in enumerate(S):
        p = xor(s, e)
        if p in S:
            out.append((sgn(z, s), S.index(p), i))
    return out


def dressings_A():
    """the four Z-dressings supported inside A"""
    return ['000000', '100000', '010000', '110000']


if __name__ == '__main__':
    print('|Y| =', len(Y), ' |Z| =', len(Z))
    for i, e in enumerate(EFLIP):
        r = off_row(e, '000000')
        print('e_%d = %s : %d incidences' % (i + 1, e, len(r)))
        print('   ', [(s, Y[b], Z[t]) for (s, b, t) in r])
    print('two-flip (0,1):', two_flip(0, 1), off_row(two_flip(0, 1), '000000'))
    for nm, e in AFLIP.items():
        print(nm, e, 'diag bottom', len(diag_row(e, '000000', False)),
              'top', len(diag_row(e, '000000', True)))


def moment_rows():
    """(label, bottom coeff list, top coeff list) for the 2+6+15 moment equations"""
    rows = [('n0', [1] * 20, [0] * 20, 1), ('n1', [0] * 20, [1] * 20, 1)]
    for i in range(6):
        rows.append(('m%d' % (i + 1),
                     [1 if x[i] == '1' else 0 for x in Y],
                     [1 if y[i] == '1' else 0 for y in Z], 0))
    for i in range(6):
        for j in range(i + 1, 6):
            rows.append(('m%d%d' % (i + 1, j + 1),
                         [1 if x[i] == '1' and x[j] == '1' else 0 for x in Y],
                         [1 if y[i] == '1' and y[j] == '1' else 0 for y in Z], 0))
    return rows


def check_norms():
    from sympy import Matrix, Rational
    rows = moment_rows()
    Amat = Matrix([r[1] + [-c for c in r[2]] for r in rows])
    rhs = Matrix([[r[3]] for r in rows])
    targets = []
    for t in range(5):
        v = [0] * 40
        for al in range(4):
            v[4 * t + al] = 1
        targets.append(('bottom tail %d' % t, v, Rational(1, 3) if t == 0 else Rational(1, 6)))
    for t in range(5):
        v = [0] * 40
        for al in range(4):
            v[20 + 4 * t + al] = 1
        targets.append(('top tail %d' % t, v, Rational(1, 3) if t == 4 else Rational(1, 6)))
    for al in range(4):
        v = [0] * 40
        for t in range(5):
            v[4 * t + al] = 1
            v[20 + 4 * t + al] = -1
        targets.append(('marginal diag %d' % al, v, Rational(0)))
    ok = True
    for (nm, v, val) in targets:
        sol = Amat.T.solve_least_squares(Matrix([[x] for x in v]))
        resid = (Amat.T * sol - Matrix([[x] for x in v])).norm()
        got = (rhs.T * sol)[0, 0]
        good = (resid == 0 and got == val)
        ok = ok and good
        print('%-20s in row space: %s   value %s (want %s)' % (nm, resid == 0, got, val))
    return ok
