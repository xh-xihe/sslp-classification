"""Verify the orbit-21 Farkas certificate exactly, as a linear identity.

The manuscript boxes (eq:o21-farkas)

    A_2 - 1 = 2 sum_{B_21} b_E + 2 sum_{T_21} s_E
              + 2 sum_{R_21,2} a + 3 sum_{R_21,3} a + 4 sum_{R_21,4} a,

every term on the right nonnegative, hence A_2 >= 1.  It says the identity is
obtained "by expanding the complete transforms and reducing all 4096 Pauli
labels under the two forced symmetries".

That is not enough.  Reducing under those symmetries alone -- a_E = 0 when E
anticommutes with G, a_{GE} = a_E, a_{D E D^dagger} = a_E -- leaves 640 unsigned
classes, and the identity is then NOT in the span of the stated constraints:
128 rows come out inconsistent.

A fourth vanishing is needed, and it is not one of the symmetries.  For a code
supported in the two subset-sum fibers, Tr(E Pi) pairs each basis string s with
s xor E.x, and both must lie in the same fiber, so

    a_E = 0   unless   A_a(E.x) = 0 mod q.

For orbit 21 that kills exactly the 320 classes with A_a(E.x) = 2 mod 4 -- the
Paulis carrying S_0 to S_2 -- leaving 320.  With it the identity holds exactly,
and this script reports the rational multipliers that witness it:

    3 (a_I - 1) - 1/2 (A_6 + 4A_1 + A_2 + A_3 - 4)
      + 6 (b_I - a_I) - 2 sum_{i in {1,2,3,6}} (b_{Z_i} - a_{Z_i}).

So the certificate is correct; the list of hypotheses the text says it rests on
is incomplete.  Everything here is exact rational arithmetic -- no floating
point anywhere -- which is what lets the difference be stated as fact rather
than as rounding.

Conventions.  A six-letter Pauli string is qubits 1..6 left to right, so string
index j is qubit j in the development's zero-based numbering.  G = Z1Z2Z3Z6 is
the Z-mask on qubits {0,1,2,5}.  D = S1S2S3 Z4Z5 S6^dagger acts on unsigned
labels as z_i -> z_i xor x_i on those same qubits, since S and S^dagger both
exchange X and Y up to sign while Z acts trivially.

    python tools/run.py verification/o21farkas.py
"""
import io
import os
import re
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
DOC = os.path.join(REPO, 'documents', '20260822', 'supplementary.tex')

NQ, Q = 6, 4
AVEC = [1, 1, 1, 2, 2, 3]
GMASK = sum(1 << j for j in (0, 1, 2, 5))
BS = chr(92)
PAULI = {'I': (0, 0), 'X': (1, 0), 'Y': (1, 1), 'Z': (0, 1)}


def pc(v):
    return bin(v).count('1')


def wtA(u):
    return sum(AVEC[j] for j in range(NQ) if (u >> j) & 1) % Q


def label(sn):
    x = z = 0
    for j, ch in enumerate(sn):
        a, b = PAULI[ch]
        if a:
            x |= 1 << j
        if b:
            z |= 1 << j
    return (x, z)


def load_sets():
    if not os.path.exists(DOC):
        raise SystemExit('source not found: %s' % DOC)
    s = io.open(DOC, encoding='utf-8').read()

    def grab(lab):
        i = s.find(BS + 'label{eq:' + lab + '}')
        if i < 0:
            raise SystemExit('label %s not found' % lab)
        j = s.rfind(BS + 'begin{', 0, i)
        return [label(m) for m in re.findall(r'mathrm\{([IXYZ]{6})\}', s[j:i])]
    out = [grab(k) for k in
           ('o21-Bset', 'o21-Tset', 'o21-R2', 'o21-R3', 'o21-R4')]
    want = [3, 22, 11, 6, 12]
    for L, n, nm in zip(out, want, ('B', 'T', 'R2', 'R3', 'R4')):
        if len(L) != n:
            raise SystemExit('set %s has %d labels, expected %d' % (nm, len(L), n))
    return out


def build(use_fiber):
    """Classes of unsigned labels; `use_fiber` adds the fourth vanishing."""
    labels = [(x, z) for x in range(64) for z in range(64)]
    zeroed = set(l for l in labels
                 if pc(GMASK & l[0]) % 2 or (use_fiber and wtA(l[0]) != 0))
    cls_of, classes = {}, []
    for l in labels:
        if l in zeroed or l in cls_of:
            continue
        orb, stack = set(), [l]
        while stack:
            c = stack.pop()
            if c in orb:
                continue
            orb.add(c)
            for nxt in ((c[0], c[1] ^ GMASK), (c[0], c[1] ^ (c[0] & GMASK))):
                if nxt not in orb:
                    stack.append(nxt)
        i = len(classes)
        for m in orb:
            cls_of[m] = i
        classes.append(orb)
    return labels, zeroed, cls_of, classes


def check(use_fiber, sets):
    B, T, R2, R3, R4 = sets
    labels, zeroed, cls_of, classes = build(use_fiber)
    NV = len(classes)
    live = [l for l in labels if l not in zeroed]

    def zero():
        return [Fraction(0)] * (NV + 1)

    def add(u, v, k=1):
        return [p + Fraction(k) * q for p, q in zip(u, v)]

    def pair(E, F):
        return (pc(E[0] & F[1]) + pc(E[1] & F[0])) % 2

    def wt(F):
        return pc(F[0] | F[1])

    def vec_a(E):
        v = zero()
        if E not in zeroed:
            v[cls_of[E]] += 1
        return v

    def vec_b(E):
        v = zero()
        for F in live:
            v[cls_of[F]] += Fraction((-1) ** pair(E, F), 32)
        return v

    def vec_s(E):
        v = zero()
        for F in live:
            v[cls_of[F]] += Fraction(((-1) ** wt(F)) * ((-1) ** pair(E, F)), 32)
        return v

    def vec_A(j):
        v = zero()
        for F in live:
            if wt(F) == j:
                v[cls_of[F]] += 1
        return v

    I0 = (0, 0)
    tgt = add(vec_A(2), [Fraction(0)] * NV + [Fraction(-1)])
    rhs = zero()
    for E in B:
        rhs = add(rhs, vec_b(E), 2)
    for E in T:
        rhs = add(rhs, vec_s(E), 2)
    for F, k in ((R2, 2), (R3, 3), (R4, 4)):
        for lbl in F:
            rhs = add(rhs, vec_a(lbl), k)
    diff = [p - q for p, q in zip(tgt, rhs)]

    cons = [add(vec_a(I0), [Fraction(0)] * NV + [Fraction(-1)])]
    c1 = add(add(add(vec_A(6), vec_A(1), 4), vec_A(2)), vec_A(3))
    cons.append(add(c1, [Fraction(0)] * NV + [Fraction(-4)]))
    cons.append([p - q for p, q in zip(vec_b(I0), vec_a(I0))])
    for i in (0, 1, 2, 5):
        Z = (0, 1 << i)
        cons.append([p - q for p, q in zip(vec_b(Z), vec_a(Z))])

    rows = [list(c) for c in cons]
    M = [[rows[k][j] for k in range(len(rows))] + [diff[j]]
         for j in range(NV + 1)]
    piv, r = [], 0
    for c in range(len(rows)):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = Fraction(1) / M[r][c]
        M[r] = [e * inv for e in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [e - f * g for e, g in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    bad = [i for i in range(len(M))
           if all(M[i][c] == 0 for c in range(len(rows))) and M[i][-1] != 0]
    lam = [Fraction(0)] * len(rows)
    for i, c in enumerate(piv):
        lam[c] = M[i][-1]
    return NV, len(bad), lam


def main(argv):
    sets = load_sets()
    print('label sets parsed: %s' % ' '.join(str(len(s)) for s in sets))
    names = ['a_I = 1', 'A6+4A1+A2+A3 = 4', 'b_I = a_I',
             'b_Z1 = a_Z1', 'b_Z2 = a_Z2', 'b_Z3 = a_Z3', 'b_Z6 = a_Z6']
    ok = True
    for use_fiber, tag in ((False, 'stated symmetries only'),
                           (True, 'plus the fiber vanishing')):
        NV, bad, lam = check(use_fiber, sets)
        print()
        print('%-28s %3d classes, %d inconsistent rows -> %s'
              % (tag, NV, bad, 'FAILS' if bad else 'identity holds'))
        if not bad:
            for nm, x in zip(names, lam):
                if x:
                    print('      %-20s multiplier %s' % (nm, x))
        if use_fiber and bad:
            ok = False
        if not use_fiber and not bad:
            print('      UNEXPECTED: the stated hypotheses now suffice;')
            print('      the note in this file needs revising.')
            ok = False
    print()
    print('certificate verified exactly:', ok)
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
