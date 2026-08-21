"""The complete weight-<=2 Knill-Laflamme system.

`scan.dressings` under-generates: for a weight-one flip it returns only
{0} u {e_j}, seven strings, but a Pauli acting as X or Y on the flipped site and
as I or Z on one other site is equally admissible, giving twelve.  It also
returns nothing for e = 0, dropping the pure-Z conditions -- the moment
equations -- entirely.  Every orbit certified so far used a subset of the true
conditions, so those proofs stand; this module supplies the full set.
"""
from itertools import combinations

from scan import bits, xor, dot


def dressings_full(e):
    """All z with |supp(e) u supp(z)| <= 2 -- enumerated and filtered, no cleverness."""
    sup = {i for i in range(6) if e[i] == '1'}
    if len(sup) > 2:
        return []
    out = []
    for m in range(64):
        z = bits(m)
        if len(sup | {i for i in range(6) if z[i] == '1'}) <= 2:
            out.append(z)
    return out


def flips():
    """All e with |supp(e)| <= 2, including 0."""
    return [bits(m) for m in range(64) if bits(m).count('1') <= 2]


def conditions(S0, S1):
    """(z, off_incidences, bot_pairs, top_pairs) for every admissible Pauli."""
    out = []
    for e in flips():
        for z in dressings_full(e):
            off = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
            db = [(S0.index(xor(x, e)), i) for i, x in enumerate(S0) if xor(x, e) in S0]
            dt = [(S1.index(xor(y, e)), j) for j, y in enumerate(S1) if xor(y, e) in S1]
            out.append((e, z, off, db, dt))
    return out


if __name__ == '__main__':
    for m in [0, 1, 3]:
        e = bits(m)
        print('e=%s  old %d  new %d' % (e, len(__import__('scan').dressings(e)),
                                        len(dressings_full(e))))
