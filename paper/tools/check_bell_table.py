"""Verify the Bell-pair Pauli table of Lemma (lem:bell-pauli) exhaustively.

The whole induction rests on this table, so it is worth checking all sixteen
two-qubit Paulis rather than the five listed cases.
"""

import itertools

import numpy as np

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _check import expect, finish                                    # noqa: E402


I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
P = {'I': I, 'X': X, 'Y': Y, 'Z': Z}

phi0 = np.array([1, 0, 0, 1], dtype=complex) / np.sqrt(2)   # (|00>+|11>)/sqrt2
phi1 = np.array([0, 1, 1, 0], dtype=complex) / np.sqrt(2)   # (|01>+|10>)/sqrt2

claimed = {
    ('I', 'I'): (1, 1, 0),
    ('X', 'X'): (1, 1, 0),
    ('Y', 'Y'): (-1, 1, 0),
    ('Z', 'Z'): (1, -1, 0),
    ('I', 'X'): (0, 0, 1),
    ('X', 'I'): (0, 0, 1),
    ('Y', 'Z'): (0, 0, -1j),
    ('Z', 'Y'): (0, 0, -1j),
}

bad = []
for a, b in itertools.product('IXYZ', repeat=2):
    B = np.kron(P[a], P[b])
    d0 = np.vdot(phi0, B @ phi0)
    d1 = np.vdot(phi1, B @ phi1)
    o = np.vdot(phi0, B @ phi1)
    o2 = np.vdot(phi1, B @ phi0)
    want = claimed.get((a, b), (0, 0, 0))
    got = (d0, d1, o)
    if max(abs(np.array(got) - np.array(want))) > 1e-12:
        bad.append((a + b, got, want))
    # the lemma also asserts the fourth overlap vanishes off the listed cases
    if (a, b) not in claimed and abs(o2) > 1e-12:
        bad.append((a + b, 'o2=%s' % o2, 'o2=0'))

expect('sixteen two-qubit Paulis, table matches including "otherwise zero"',
       len(bad), 0)
for row in bad:
    print('   mismatch:', row)

# the two facts the induction actually consumes
print()
expect('ZZ acts as +1 on Phi_0', np.vdot(phi0, np.kron(Z, Z) @ phi0).real, 1.0, 1e-12)
expect('ZZ acts as -1 on Phi_1', np.vdot(phi1, np.kron(Z, Z) @ phi1).real, -1.0, 1e-12)
expect('XX acts as +1 on Phi_0', np.vdot(phi0, np.kron(X, X) @ phi0).real, 1.0, 1e-12)
expect('XX acts as +1 on Phi_1', np.vdot(phi1, np.kron(X, X) @ phi1).real, 1.0, 1e-12)

finish('Bell-pair Pauli table')
