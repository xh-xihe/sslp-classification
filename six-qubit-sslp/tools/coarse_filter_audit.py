#!/usr/bin/env python3
"""Audit the coarse affine-Smith filter and measure what its S_delta clause
carries.

`main.tex` states the filter as

    min(affdim S_0, affdim S_delta) >= r_min(q),          six:eq:coarserank

justified by `q <= beta_r` at `r := affdim T_0 = affdim T_1` (six:eq:ractual,
six:eq:qbetar).  The Lean development proves the *linear*-rank version of that
bound -- `SupportedBitBasis` takes raw bit rows, not differences -- and the two
ranks differ by one whenever the origin is outside the support's affine hull.

The S_0 clause survives that difference: the zero-residue fibre contains the
all-zero word, so its affine and linear ranks agree (proved in Lean as
`MaskRankBridge.residueZeroMask_affineRank_eq_span`, and reconfirmed here on
all 11,422 pairs).  The S_delta clause does not.

This script measures the exposure exactly: how many pairs the S_delta clause
alone discards, and whether any of them could have carried a code anyway.

Run:  python tools/coarse_filter_audit.py
"""
import io
import os
import re
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exact_lp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BETA = {0: 0, 1: 1, 2: 1, 3: 2, 4: 3, 5: 5, 6: 9}


def rmin(q):
    return min(r for r in range(7) if BETA[r] >= q)


def rank(rows):
    rows = [list(map(F, r)) for r in rows]
    if not rows:
        return 0
    n = len(rows[0])
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pr = rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / pr[c]
                rows[i] = [a - f * b for a, b in zip(rows[i], pr)]
        r += 1
    return r


def words(mask):
    return [x for x in range(64) if (mask >> x) & 1]


def bits(x):
    return [(x >> j) & 1 for j in range(6)]


def affdim(mask):
    P = [bits(x) for x in words(mask)]
    if not P:
        return -1
    if len(P) == 1:
        return 0
    b = P[0]
    return rank([[a - c for a, c in zip(p, b)] for p in P[1:]])


def lindim(mask):
    return rank([bits(x) for x in words(mask)])


def phi(x):
    b = bits(x)
    return ([F(b[i]) for i in range(6)] +
            [F(b[i] * b[j]) for i in range(6) for j in range(i + 1, 6)])


def moment_feasible(mask0, mask1):
    """`six:eq:mean` and `six:eq:cov`: do the two moment images have a common
    point?  Equivalently, is the convex hull intersection nonempty -- the exact
    condition `six:eq:separator` certifies the failure of."""
    P0, P1 = words(mask0), words(mask1)
    if not P0 or not P1:
        return False
    c0 = [phi(x) for x in P0]
    c1 = [phi(y) for y in P1]
    n0, n1 = len(P0), len(P1)
    A, rhs = [], []
    A.append([F(1)] * n0 + [F(0)] * n1)
    rhs.append(F(1))
    A.append([F(0)] * n0 + [F(1)] * n1)
    rhs.append(F(1))
    for r in range(21):
        A.append([c0[k][r] for k in range(n0)] + [-c1[k][r] for k in range(n1)])
        rhs.append(F(0))
    status, x, y = exact_lp.solve(A, rhs)
    exact_lp.check(A, rhs, status, x, y)   # every verdict carries a checked
    return status == 'feasible'            # primal point or Farkas dual


def load_pairs():
    src = io.open(os.path.join(ROOT, 'MainTheory', 'Generated',
                               'FinitePairData.lean'), encoding='utf-8').read()
    block = src[src.index('def pairTable'):src.index('theorem pairTable_size')]
    return [tuple(int(x) for x in m)
            for m in re.findall(r'⟨(\d+), (\d+), (\d+), (\d+)⟩', block)]


def main():
    pairs = load_pairs()
    print('pairs                                  : %d' % len(pairs))

    mismatched = sum(1 for (_, _, m0, _) in pairs if affdim(m0) != lindim(m0))
    print('pairs with affdim(S_0) != lindim(S_0)  : %d  (expect 0: 0^6 in S_0)'
          % mismatched)

    kept = only_s0 = only_s1 = 0
    exposed = []
    for (q, m, m0, m1) in pairs:
        rm = rmin(q)
        p0, p1 = rm <= affdim(m0), rm <= affdim(m1)
        if p0 and p1:
            kept += 1
        elif p0:
            only_s0 += 1
            exposed.append((q, m, m0, m1))
        elif p1:
            only_s1 += 1
    print('kept by the filter                     : %d  (six:eq:508)' % kept)
    print('discarded by the S_delta clause alone  : %d' % only_s0)
    print('discarded by the S_0 clause alone      : %d' % only_s1)

    survivors = [p for p in exposed if moment_feasible(p[2], p[3])]
    print('of the S_delta-only discards, moment-feasible: %d' % len(survivors))
    for s in survivors[:20]:
        print('    q=%d m=%d masks=(%d, %d)' % s)

    mf = sum(1 for (q, m, m0, m1) in pairs
             if rmin(q) <= min(affdim(m0), affdim(m1))
             and moment_feasible(m0, m1))
    print('moment-feasible among the survivors    : %d  (six:eq:291)' % mf)

    # The route whose soundness is fully proved: drop the unjustified clause.
    s0_only = [p for p in pairs if rmin(p[0]) <= affdim(p[2])]
    mf2 = sum(1 for p in s0_only if moment_feasible(p[2], p[3]))
    print()
    print('--- the route that needs no unproved step ---')
    print('pairs passing the S_0 clause alone     : %d' % len(s0_only))
    print('moment-feasible among those            : %d' % mf2)
    print('same 291?                              : %s' % (mf2 == mf))
    return 0


if __name__ == '__main__':
    sys.exit(main())
