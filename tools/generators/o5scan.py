"""Inventory of the orbit-5 admissible Knill-Laflamme rows, grouped by flip mask."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from o5data import Y, Z, conds, label, AB, YNAME, ZNAME
from scan import dot


def sgn(z, s):
    return -1 if dot(z, s) else 1


def offexpr(z, off):
    """symbolic off-diagonal row: sum of  sgn * conj(bottom) * top"""
    terms = []
    for (bi, ti) in off:
        terms.append((sgn(z, Z[ti]), label(bi, False), label(ti, True)))
    return terms


def group(terms):
    """collect into vector-level inner products  conj(X[A]) * Y[A] summed over A"""
    from collections import defaultdict
    acc = defaultdict(dict)
    for s, b, t in terms:
        bn, ba = b.split('[')
        tn, ta = t.split('[')
        assert ba == ta, (b, t)
        acc[(bn, tn)][ba.rstrip(']')] = s
    return acc


if __name__ == '__main__':
    cs = conds()
    byflip = {}
    for (e, z, off, db, dt) in cs:
        byflip.setdefault(e, []).append((z, off, db, dt))
    for e in sorted(byflip, key=lambda s: (s.count('1'), s)):
        rows = byflip[e]
        noff = len(rows[0][1])
        ndb = len(rows[0][2])
        print('flip e=%s  dressings=%d  offinc=%d  diaginc=%d' % (e, len(rows), noff, ndb))
