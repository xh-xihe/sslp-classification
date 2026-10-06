"""Check the two outer-record totals `main.tex` quotes, and the per-q counts.

`main.tex` states `(P_6(2), ..., P_6(9)) = (6, 27, 77, 209, 428, 923, 1632, 2975)`
(six:eq:primitivevalues), and says the raw `13,877` sorted outer angle records
reduce to `13,449` primitive ones (six:eq:primitiveTotal).

The per-q counts are checked in the Lean kernel by
`MainTheory/OuterIndex.lean`, for the `q` where `decide` can carry them.  What
this script adds is the two totals, which are sums of those counts weighted by
the number of admissible logical orders `m > 1` dividing `q` -- a weighting the
Lean file does not perform.

The raw total uses `C(q+5,6)`, the number of sorted vectors before the
primitivity filter; the primitive total uses `P_6(q)`.  Both are recomputed here
from the definitions rather than transcribed, and the script fails if either
total or any individual count disagrees with the paper.

    python tools/run.py verification/outercount.py
"""
import sys
from math import comb, gcd
from itertools import combinations_with_replacement as cwr

PAPER_P6 = (6, 27, 77, 209, 428, 923, 1632, 2975)
PAPER_RAW = 13877
PAPER_PRIM = 13449


def p6(q):
    """Sorted a in {0..q-1}^6 with gcd(q, a_1, ..., a_6) = 1."""
    n = 0
    for a in cwr(range(q), 6):
        g = q
        for v in a:
            g = gcd(g, v)
        if g == 1:
            n += 1
    return n


def main(argv):
    ok = True
    raw = prim = 0
    print('  q  m-choices      C(q+5,6)      P_6(q)   paper P_6(q)')
    for q in range(2, 10):
        ms = [m for m in range(2, q + 1) if q % m == 0]
        c = comb(q + 5, 6)
        p = p6(q)
        want = PAPER_P6[q - 2]
        if p != want:
            ok = False
        raw += len(ms) * c
        prim += len(ms) * p
        print('  %d  %d              %6d      %6d   %6d%s'
              % (q, len(ms), c, p, want, '' if p == want else '   MISMATCH'))
    print()
    print('  raw total       %6d   paper %6d   %s'
          % (raw, PAPER_RAW, 'ok' if raw == PAPER_RAW else 'MISMATCH'))
    print('  primitive total %6d   paper %6d   %s'
          % (prim, PAPER_PRIM, 'ok' if prim == PAPER_PRIM else 'MISMATCH'))
    ok = ok and raw == PAPER_RAW and prim == PAPER_PRIM
    print()
    print('all counts agree with main.tex: %s' % ok)
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
