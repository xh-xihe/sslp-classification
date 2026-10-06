"""Orbit 5 (q=3, a=(0,0,1,1,1,1), delta=1): fibers and the admissible KL system.

Qubits 0,1 are the zero-angle pair A; qubits 2..5 are the four active
coordinates V = {1,2,3,4}.  The active tails are

    T0 = {0000, 0111, 1011, 1101, 1110}      (u, a_1, a_2, a_3, a_4)
    T1 = {1000, 0100, 0010, 0001, 1111}      (b_1, b_2, b_3, b_4, v)

and every tail carries a vector in C^4 indexed by the two A bits.
"""
from itertools import combinations

from orbit import fiber
from kl import dressings_full, flips
from scan import xor

A = [0, 0, 1, 1, 1, 1]
Q = 3

S0 = fiber(A, Q, 0)
S1 = fiber(A, Q, 1)

T0 = ['0000', '0111', '1011', '1101', '1110']
T1 = ['1000', '0100', '0010', '0001', '1111']
AB = ['00', '01', '10', '11']

Y = [a + t for t in T0 for a in AB]
Z = [a + t for t in T1 for a in AB]

# names: u/a_i for bottom, b_i/v for top
YNAME = ['u', 'a1', 'a2', 'a3', 'a4']
ZNAME = ['b1', 'b2', 'b3', 'b4', 'v']


def check():
    assert sorted(S0) == sorted(Y), (sorted(S0), sorted(Y))
    assert sorted(S1) == sorted(Z)
    assert len(S0) == 20 and len(S1) == 20
    print('fibers OK: |S0| = %d, |S1| = %d' % (len(S0), len(S1)))


def conds():
    """(e, z, offlist, botlist, toplist) for every admissible Pauli."""
    out = []
    for e in flips():
        for z in dressings_full(e):
            off = [(Y.index(xor(y, e)), t) for t, y in enumerate(Z) if xor(y, e) in Y]
            db = [(Y.index(xor(x, e)), i) for i, x in enumerate(Y) if xor(x, e) in Y]
            dt = [(Z.index(xor(y, e)), j) for j, y in enumerate(Z) if xor(y, e) in Z]
            out.append((e, z, off, db, dt))
    return out


def label(idx, top):
    names = ZNAME if top else YNAME
    return '%s[%s]' % (names[idx // 4], AB[idx % 4])


if __name__ == '__main__':
    check()
    cs = conds()
    print('admissible Paulis: %d (expect 154)' % len(cs))
    nz_off = [(e, z, off) for (e, z, off, _, _) in cs if off]
    print('with nonempty off-diagonal incidence: %d' % len(nz_off))
    seen = {}
    for e, z, off in nz_off:
        seen.setdefault(e, []).append(z)
    for e in sorted(seen):
        print('  e=%s  dressings=%d  incidences=%d' %
              (e, len(seen[e]), len([1 for (ee, zz, o) in nz_off if ee == e][0:1]
                                    and [x for (ee, zz, o) in nz_off if ee == e][0])))
