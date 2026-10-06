"""Analysis of moment orbits 49 and 51 (phase propagation).

Computes the two fibers, matches the paper's ordering, solves the full
21-equation moment system exactly, and row-reduces every admissible
weight-<=2 Knill-Laflamme flip mask to expose the isolated relations.

Run:  python tools/run.py generators/an4951.py
"""
from itertools import combinations

from sympy import Matrix, Rational, symbols, linsolve

from orbit import fiber, ind
from kl import conditions, dressings_full, flips
from scan import xor, dot

N = 6

ORB = {
    49: ([1, 1, 1, 3, 3, 5], 6, 2),
    51: ([1, 1, 2, 3, 3, 4], 6, 2),
}

PAPER = {
    49: ['000000', '000110', '001001', '001111', '010001',
         '010111', '100001', '100111', '111010', '111100'],
    51: ['000000', '000110', '001001', '001111', '011010',
         '011100', '101010', '101100', '110001', '110111'],
}


def comp(s):
    return ''.join('0' if ch == '1' else '1' for ch in s)


def moment_matrix(S0, S1):
    """2 normalisations + 6 one-bit + 15 two-bit equations."""
    n0, n1 = len(S0), len(S1)
    rows, rhs, lab = [], [], []
    rows.append([1] * n0 + [0] * n1); rhs.append(1); lab.append('n0')
    rows.append([0] * n0 + [1] * n1); rhs.append(1); lab.append('n1')
    for i in range(N):
        rows.append([ind(x, i) for x in S0] + [-ind(y, i) for y in S1])
        rhs.append(0); lab.append('m%d' % (i + 1))
    for (i, j) in combinations(range(N), 2):
        rows.append([ind(x, i) * ind(x, j) for x in S0]
                    + [-ind(y, i) * ind(y, j) for y in S1])
        rhs.append(0); lab.append('m%d%d' % (i + 1, j + 1))
    return Matrix(rows), Matrix(rhs), lab


def analyse(name):
    a, q, delta = ORB[name]
    S0 = fiber(a, q, 0)
    S1 = fiber(a, q, delta)
    print('=' * 70)
    print('ORBIT %d   a=%s  q=%d  delta=%d' % (name, a, q, delta))
    print('  |S0| = %d   |S1| = %d' % (len(S0), len(S1)))
    print('  complementary:', sorted(comp(x) for x in S0) == sorted(S1))
    print('  paper S0 == computed S0 (as sets):',
          sorted(PAPER[name]) == sorted(S0))

    B = PAPER[name]                 # bottom, paper order
    T = [comp(x) for x in B]        # top, indexed by complement
    print('  top order (complement):', T)

    A, rhs, lab = moment_matrix(B, T)
    print('  moment matrix shape', A.shape, ' rank', A.rank())

    ps = symbols('p0:10')
    rs = symbols('r0:10')
    unk = list(ps) + list(rs)
    sol = linsolve((A, rhs), unk)
    sol = list(sol)[0]
    print('  general solution:')
    for k in range(10):
        print('    p%-2d = %s' % (k, sol[k]))
    for k in range(10):
        print('    r%-2d = %s' % (k, sol[10 + k]))
    free = sorted({s for e in sol for s in e.free_symbols}, key=str)
    print('  free parameters:', free)
    return B, T, sol, free


def relations(name, B, T):
    """For every flip mask e, row reduce the off-diagonal system."""
    print('-' * 70)
    print('OFF-DIAGONAL RELATIONS, orbit %d' % name)
    out = {}
    for e in flips():
        inc = [(B.index(xor(y, e)), t) for t, y in enumerate(T) if xor(y, e) in B]
        if not inc:
            continue
        zs = dressings_full(e)
        rows = [[(-1) ** dot(z, T[t]) for (_s, t) in inc] for z in zs]
        M = Matrix(rows)
        R, piv = M.rref()
        R = R[:len(piv), :]
        out[e] = (inc, R, piv)
        print('  e=%s  inc=%s' % (e, [(s, t) for (s, t) in inc]))
        print('       rank %d / %d unknowns' % (len(piv), len(inc)))
        for r in range(R.rows):
            terms = []
            for cidx in range(R.cols):
                if R[r, cidx] != 0:
                    terms.append('%+s*z[%d,%d]' % (R[r, cidx], inc[cidx][0], inc[cidx][1]))
            print('       0 = ' + ' '.join(terms))
    return out


def diagonals(name, B, T):
    print('-' * 70)
    print('DIAGONAL RELATIONS, orbit %d' % name)
    for e in flips():
        db = [(B.index(xor(x, e)), i) for i, x in enumerate(B) if xor(x, e) in B]
        dt = [(T.index(xor(y, e)), j) for j, y in enumerate(T) if xor(y, e) in T]
        if not db and not dt:
            continue
        if e == '0' * 6:
            continue
        print('  e=%s  bot=%s  top=%s' % (e, db, dt))


if __name__ == '__main__':
    for nm in (49, 51):
        B, T, sol, free = analyse(nm)
        relations(nm, B, T)
        diagonals(nm, B, T)
