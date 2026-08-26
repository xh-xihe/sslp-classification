"""Check the orbit-21 Farkas certificate as a linear identity -- and a retraction.

WHAT THIS FILE ONCE CLAIMED, AND WHY IT WAS WRONG.

The manuscript boxes (eq:o21-farkas) and says the identity comes from expanding
the complete transforms and "reducing all 4096 Pauli labels under the two forced
symmetries".  Reducing under those alone leaves 640 classes, and the identity is
not in the span of the stated constraints: 128 rows come out inconsistent.  From
that I concluded a fourth vanishing was missing, proposed

    a_E = 0   unless   A_a(E.x) = 0 mod q,

reported the identity as verified with it, and recorded the source's hypothesis
list as incomplete.

That conclusion does not hold, for two independent reasons.

First, the proposed vanishing is false.  Checked against the certified orbit-21
code, ninety-six labels with A_a(E.x) != 0 have a nonzero individual diagonal
<k|E|k>.  The reason is that orbit 21's exhibited support is a proper subset of
its fiber -- eight words of sixteen -- so A_a is not an invariant of the support:
the mask 011000 has A_a = 2 yet maps four of the eight word-0 strings back into
word 0.  The genuine vanishing is support-level, and only two masks preserve both
supports, which is a property of that one code rather than of the orbit.

Second, and more basic: the inconsistency does not identify a missing
hypothesis.  Restricting instead to labels with zero X-part also makes the
identity hold, on 32 classes.  Several different strengthenings close those 128
rows, so "the identity holds once I assume P" is no evidence that the source
omitted P.

So the certificate may well follow from exactly the hypotheses the manuscript
states, by a route this script does not reconstruct.  Nothing here shows a gap
in the source, and the earlier claim that it did should not be relied on.

What the script still does honestly is report, for a given set of forced
vanishings, how many classes survive and whether the identity lies in the span
of the stated constraints.  That is a diagnostic, not a verification of the
manuscript's derivation.

Conventions.  A six-letter Pauli string is qubits 1..6 left to right, so string
index j is qubit j in the development's zero-based numbering.  G = Z1Z2Z3Z6 is
the Z-mask on qubits {0,1,2,5}.  D = S1S2S3 Z4Z5 S6^dagger acts on unsigned
labels as z_i -> z_i xor x_i on those same qubits.

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


def per_class(sets):
    """The shape the Lean transcription needs.

    Write Delta for (A_2 - 1) - RHS - (the constraint combination above).  As a
    linear form in the individual `a_F` it does NOT vanish -- 476 labels outside
    the forced set carry a nonzero coefficient -- because the two symmetries
    relate different labels rather than killing them.  What does vanish is the
    coefficient sum on each class.  So the certificate is a per-class identity,
    and in Lean it becomes: reindex the Pauli sum by class, use that `a` is
    constant on each, and check the class sums are zero, which is finite.
    """
    B, T, R2, R3, R4 = sets
    labels = [(x, z) for x in range(64) for z in range(64)]

    def pair(E, F):
        return (pc(E[0] & F[1]) + pc(E[1] & F[0])) % 2

    def wt(F):
        return pc(F[0] | F[1])

    forced = set(l for l in labels if pc(GMASK & l[0]) % 2 or wtA(l[0]) != 0)
    c = {F: Fraction(0) for F in labels}

    def bump(F, k):
        c[F] += Fraction(k)
    for F in labels:
        if wt(F) == 2:
            bump(F, 1)
    for E in B:
        for F in labels:
            bump(F, Fraction(-2 * (-1) ** pair(E, F), 32))
    for E in T:
        for F in labels:
            bump(F, Fraction(-2 * ((-1) ** wt(F)) * ((-1) ** pair(E, F)), 32))
    for Fs, k in ((R2, 2), (R3, 3), (R4, 4)):
        for F in Fs:
            bump(F, -k)
    I0 = (0, 0)
    bump(I0, -3)
    for F in labels:
        w = wt(F)
        if w == 6:
            bump(F, Fraction(1, 2))
        if w == 1:
            bump(F, Fraction(2))
        if w in (2, 3):
            bump(F, Fraction(1, 2))
    for F in labels:
        bump(F, Fraction(-6 * (-1) ** pair(I0, F), 32))
    bump(I0, 6)
    for i in (0, 1, 2, 5):
        Z = (0, 1 << i)
        for F in labels:
            bump(F, Fraction(2 * (-1) ** pair(Z, F), 32))
        bump(Z, -2)

    cls_of, classes = {}, []
    for l in labels:
        if l in forced or l in cls_of:
            continue
        orb, stack = set(), [l]
        while stack:
            cur = stack.pop()
            if cur in orb:
                continue
            orb.add(cur)
            for nxt in ((cur[0], cur[1] ^ GMASK),
                        (cur[0], cur[1] ^ (cur[0] & GMASK))):
                if nxt not in orb:
                    stack.append(nxt)
        i = len(classes)
        for m in orb:
            cls_of[m] = i
        classes.append(sorted(orb))
    free_nz = sum(1 for F in labels if c[F] != 0 and F not in forced)
    bad = [i for i, o in enumerate(classes) if sum(c[F] for F in o) != 0]

    # Averaging over the symmetry group turns the per-class identity into a
    # per-label one, which is what makes it reachable by `decide`.  The group is
    # generated by z -> z xor g (multiplication by G) and z -> z xor (x and g)
    # (conjugation by D); both are involutions and they commute, so it has
    # order four.  Since a is constant on orbits, reindexing gives
    # sum_F c_F a_F = sum_F c_{sigma F} a_F for each sigma, and averaging the
    # four replaces c by its orbit mean -- which is the orbit sum over the
    # orbit size, hence zero off the forced set.
    def s1(F):
        return (F[0], F[1] ^ GMASK)

    def s2(F):
        return (F[0], F[1] ^ (F[0] & GMASK))
    grp = [lambda F: F, s1, s2, lambda F: s1(s2(F))]
    avg = {F: sum(c[g(F)] for g in grp) / 4 for F in labels}
    avg_free_nz = sum(1 for F in labels if avg[F] != 0 and F not in forced)
    return len(classes), free_nz, len(bad), avg_free_nz


def main(argv):
    sets = load_sets()
    print('label sets parsed: %s' % ' '.join(str(len(x)) for x in sets))
    names = ['a_I = 1', 'A6+4A1+A2+A3 = 4', 'b_I = a_I',
             'b_Z1 = a_Z1', 'b_Z2 = a_Z2', 'b_Z3 = a_Z3', 'b_Z6 = a_Z6']
    for use_fiber, tag in ((False, 'G-anticommuting only'),
                           (True, 'plus the (FALSE) fibre vanishing')):
        NV, bad, lam = check(use_fiber, sets)
        print()
        print('%-34s %3d classes, %d inconsistent rows'
              % (tag, NV, bad))
        if not bad:
            for nm, x in zip(names, lam):
                if x:
                    print('      %-20s multiplier %s' % (nm, x))
    print()
    print('Read the docstring before drawing a conclusion from the second block.')
    print('The fibre vanishing is false for orbit 21, whose support is a proper')
    print('subset of its fibre; and several different strengthenings close the')
    print('128 rows, so closure identifies no missing hypothesis.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
