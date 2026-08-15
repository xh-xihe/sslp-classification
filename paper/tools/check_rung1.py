"""Verify the rung-1 code of the explicit seed, independently of Lean.

Builds the nine-qubit codewords exactly as printed in the manuscript, then
checks normalization, orthogonality, membership in the subset-sum sectors of
the rung-1 modulus m_1 = 16, the action of the transversal diagonal, and the
Knill-Laflamme conditions for every Pauli of weight at most two.

Every claim is asserted; the script exits nonzero if any fails.
"""

import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _check import expect, finish                                    # noqa: E402

r2, r3 = np.sqrt(2.0), np.sqrt(3.0)

# --- the explicit ((7,2,3)) seed of arXiv:2504.20847 Sec. 6.3.1 -----------
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
    bk = 0 if k == 0 else m - 1
    out = {}
    for x, c in psi.items():
        h = ((ssum(a, x) - bk) // m) % 2
        for y, t in PHI[h ^ k].items():
            out[x + y] = out.get(x + y, 0) + c * t
    return out


psi0 = SEED
psi1 = {''.join('1' if c == '0' else '0' for c in x): v for x, v in SEED.items()}

p0 = lift(psi0, A0, M0, 0)
p1 = lift(psi1, A0, M0, 1)

A1 = A0 + [M0, M0]          # a^(1) = (1,2,2,2,2,3,3,8,8)
M1 = 2 * M0                 # m_1 = 16
N1 = 9

print('rung-1 code of the explicit seed:')
print()


def vec(d):
    v = np.zeros(2 ** N1, dtype=complex)
    for x, c in d.items():
        v[int(x, 2)] = c
    return v


v0, v1 = vec(p0), vec(p1)

expect('|0_L> normalized', np.linalg.norm(v0), 1.0, 1e-12)
expect('|1_L> normalized', np.linalg.norm(v1), 1.0, 1e-12)
expect('codewords orthogonal', abs(np.vdot(v0, v1)), 0.0, 1e-12)
expect('block length', N1, 9)
expect('modulus m_1', M1, 16)

# --- subset-sum sectors, modulo m_1 (not modulo 2 m_1) -------------------
s0 = sorted({ssum(A1, x) % M1 for x in p0})
s1 = sorted({ssum(A1, x) % M1 for x in p1})
expect('residues of |0_L> mod m_1', s0, [0])
expect('residues of |1_L> mod m_1', s1, [M1 - 1])

# --- the transversal diagonal induces D_16 -------------------------------
w = np.exp(2j * np.pi / M1)
diag = np.array([w ** (ssum(A1, format(i, '0%db' % N1)) % M1)
                 for i in range(2 ** N1)])
expect('U|0_L> = |0_L>', float(np.max(np.abs(diag * v0 - v0))), 0.0, 1e-12)
expect('U|1_L> = w^-1 |1_L>',
       float(np.max(np.abs(diag * v1 - np.exp(-2j * np.pi / M1) * v1))), 0.0, 1e-12)

# --- Knill-Laflamme, weight <= 2 -----------------------------------------
I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
P1 = {'I': I, 'X': X, 'Y': Y, 'Z': Z}


def apply_pauli(v, letters):
    t = v.reshape([2] * N1)
    for q, L in enumerate(letters):
        if L == 'I':
            continue
        t = np.tensordot(P1[L], t, axes=([1], [q]))
        t = np.moveaxis(t, 0, q)
    return t.reshape(-1)


worst, count = 0.0, 0
for support in itertools.chain([()],
                               ((i,) for i in range(N1)),
                               itertools.combinations(range(N1), 2)):
    for letters in itertools.product('XYZ', repeat=len(support)):
        s = ['I'] * N1
        for q, L in zip(support, letters):
            s[q] = L
        Ev0, Ev1 = apply_pauli(v0, s), apply_pauli(v1, s)
        worst = max(worst,
                    abs(np.vdot(v0, Ev1)), abs(np.vdot(v1, Ev0)),
                    abs(np.vdot(v0, Ev0) - np.vdot(v1, Ev1)))
        count += 1

expect('Paulis of weight <= 2 enumerated', count, 352)
expect('worst KL violation', worst, 0.0, 1e-12)

finish('rung-1 code')
