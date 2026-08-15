"""Check the r=0 detail asserted in the proof of the exact-distance lemma.

The proof claims a single support string carries the whole matrix element at
rung 0.  This prints every contributing pair so the wording can be made to match
what actually happens.
"""

import numpy as np

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _check import expect, finish                                    # noqa: E402


r2, r3 = np.sqrt(2.0), np.sqrt(3.0)

ZERO = {
    '0000000': 1 / 4,
    '0111100': r3 / 4,
    '1001110': r3 / 4,
    '1010101': r2 / 4,
    '1011001': r2 / 4,
    '1110010': 1 / 4,
    '0100011': 1j / 2,
}
ONE = {''.join('1' if c == '0' else '0' for c in x): v for x, v in ZERO.items()}

# E = X on qubit 0, X on qubit 1, Z on qubit 2, identity elsewhere
FLIP = '1100000'


def act(x):
    """E|x> = sign * |y>."""
    y = ''.join(str(int(a) ^ int(b)) for a, b in zip(x, FLIP))
    return ((-1) ** int(x[2])), y


total = 0j
pairs = []
for x, c1 in ONE.items():
    sgn, y = act(x)
    if y in ZERO:
        total += np.conj(ZERO[y]) * sgn * c1
        pairs.append((x, sgn, y))

print('contributions to <0_L| XXZ |1_L> at rung 0:')
for x, sgn, y in pairs:
    print('   |%s> --E--> %s|%s>' % (x, '+' if sgn > 0 else '-', y))
print()

expect('exactly two support strings contribute', len(pairs), 2)
expect('the pair asserted in the proof', sorted(x for x, _, _ in pairs),
       ['1000011', '1011100'])
expect('|<0|XXZ|1>| at rung 0', abs(total), r3 / 4, 1e-12)

finish('rung-0 witness detail')
