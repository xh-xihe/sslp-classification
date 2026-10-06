"""Structural probe for the parity-four triad (orbits 14, 15, 24).

Checks, straight from `fiber`:
  * the claimed frozen / tied coordinates on both fibers,
  * that the effective four bits land in the even / odd parity classes,
  * that the tail map fiber -> (free bit, effective four bits) is a bijection.
"""
import sys

sys.path.insert(0, 'tools/core')
from orbit import fiber

ORB = {
    15: (4, [0, 1, 2, 2, 2, 2], 2),
    24: (4, [1, 2, 2, 2, 2, 3], 2),
    14: (4, [0, 1, 1, 2, 2, 2], 2),
}


def show(oid):
    q, a, d = ORB[oid]
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    print('--- orbit %d  a=%s q=%d delta=%d   |S0|=%d |S1|=%d'
          % (oid, a, q, d, len(S0), len(S1)))
    for i in range(6):
        v0 = {x[i] for x in S0}
        v1 = {y[i] for y in S1}
        print('   coord %d : S0 %s   S1 %s' % (i + 1, sorted(v0), sorted(v1)))
    for i in range(6):
        for j in range(i + 1, 6):
            if all(x[i] == x[j] for x in S0) and all(y[i] == y[j] for y in S1):
                print('   TIED  x_%d = x_%d on both fibers' % (i + 1, j + 1))
    return S0, S1


def parity(oid, free, eff):
    """free: index of the free/zero-angle qubit or None; eff: 4 effective coords."""
    q, a, d = ORB[oid]
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    e0 = [''.join(x[i] for i in eff) for x in S0]
    e1 = [''.join(y[i] for i in eff) for y in S1]
    print('   effective bits %s : S0 parities %s ; S1 parities %s'
          % ([i + 1 for i in eff],
             sorted({sum(map(int, s)) % 2 for s in e0}),
             sorted({sum(map(int, s)) % 2 for s in e1})))
    if free is None:
        print('   S0 eff strings distinct: %s (%d)' % (len(set(e0)) == len(e0), len(set(e0))))
        print('   S1 eff strings distinct: %s (%d)' % (len(set(e1)) == len(e1), len(set(e1))))
    else:
        k0 = [(x[free], t) for x, t in zip(S0, e0)]
        k1 = [(y[free], t) for y, t in zip(S1, e1)]
        print('   (free,eff) keys distinct: S0 %s  S1 %s'
              % (len(set(k0)) == len(k0), len(set(k1)) == len(k1)))


show(15); parity(15, 0, [2, 3, 4, 5])
show(24); parity(24, None, [1, 2, 3, 4])
show(14); parity(14, 0, [1, 3, 4, 5])
