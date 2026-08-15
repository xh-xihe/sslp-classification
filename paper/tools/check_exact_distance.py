"""Test the referee's claim that the ladder has distance exactly 3, not just >= 3.

The theorem proves the Knill-Laflamme conditions for every Pauli of weight <= 2,
which gives d >= 3.  Writing ((7+2r,2,3)) asserts d = 3 exactly, which needs a
weight-3 Pauli that violates the conditions.  The referee proposes XXZ on the
first three qubits of the seed block, claiming |<0_L|XXZ|1_L>| = sqrt(3)/4 at
every rung.  This builds the ladder and checks.
"""

import itertools

import numpy as np

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _check import expect, finish                                    # noqa: E402


r2, r3 = np.sqrt(2.0), np.sqrt(3.0)

SEED = {
    '0000000': 1 / 4,
    '0111100': r3 / 4,
    '1001110': r3 / 4,
    '1010101': r2 / 4,
    '1011001': r2 / 4,
    '1110010': 1 / 4,
    '0100011': 1j / 2,
}
A0 = [1, 2, 2, 2, 2, 3, 3]
M0 = 8

PHI = {0: {'00': 1 / np.sqrt(2), '11': 1 / np.sqrt(2)},
       1: {'01': 1 / np.sqrt(2), '10': 1 / np.sqrt(2)}}


def ssum(a, x):
    return sum(ai for ai, xi in zip(a, x) if xi == '1')


def lift(psi, a, m, k):
    """One dyadic Bell lift of the logical-k codeword."""
    bk = 0 if k == 0 else m - 1
    out = {}
    for x, c in psi.items():
        h = ((ssum(a, x) - bk) // m) % 2
        for y, t in PHI[h ^ k].items():
            out[x + y] = out.get(x + y, 0) + c * t
    return out


I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
P1 = {'I': I2, 'X': X, 'Y': Y, 'Z': Z}


def vec(d, n):
    v = np.zeros(2 ** n, dtype=complex)
    for x, c in d.items():
        v[int(x, 2)] = c
    return v


def apply_pauli(v, letters, n):
    t = v.reshape([2] * n)
    for q, L in enumerate(letters):
        if L == 'I':
            continue
        t = np.tensordot(P1[L], t, axes=([1], [q]))
        t = np.moveaxis(t, 0, q)
    return t.reshape(-1)


print('the weight-three witness XXZ, rung by rung:')
print()

p0, a, m = SEED, list(A0), M0
p1 = {''.join('1' if ch == '0' else '0' for ch in x): c for x, c in SEED.items()}

for r in range(5):
    n = 7 + 2 * r
    v0, v1 = vec(p0, n), vec(p1, n)
    w = ['I'] * n
    w[0], w[1], w[2] = 'X', 'X', 'Z'
    witness = abs(np.vdot(v0, apply_pauli(v1, w, n)))
    expect('rung %d (n=%2d): |<0|XXZ|1>| = sqrt(3)/4' % (r, n),
           witness, r3 / 4, 1e-12)
    if r < 4:
        p0n, p1n = lift(p0, a, m, 0), lift(p1, a, m, 1)
        a, m, p0, p1 = a + [m, m], 2 * m, p0n, p1n

finish('exact distance')
