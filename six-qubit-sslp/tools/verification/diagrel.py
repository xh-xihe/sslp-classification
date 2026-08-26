"""The diagonal Knill-Laflamme conditions as a linear system on coherences.

For a mask e and dressing z the condition

    sum_{x in S0, x+e in S0} (-1)^{z.x} conj(c_{x+e}) c_x
  = sum_{y in S1, y+e in S1} (-1)^{z.y} conj(d_{y+e}) d_y

is a +-1 combination of the coherences conj(c_a) c_b with a+b = e.  Each such
pair contributes its two orderings with signs (-1)^{z.x_a} and (-1)^{z.x_b}; when
those agree the pair enters through 2*Re, when they differ through 2i*Im.  So the
condition splits into one real equation in the real parts and one in the
imaginary parts, both with integer coefficients.
"""
import sys
sys.path.insert(0, '.')
from itertools import combinations

import sympy as sp

from orbit import fiber
from scan import bits, xor, dot
from kl import dressings_full, flips


def coherence_system(S0, S1):
    """Rows (label, dict on ('Re'|'Im', side, a, b) -> int) for every diagonal condition."""
    rows = []
    for e in flips():
        if e.count('1') == 0:
            continue
        for z in dressings_full(e):
            re_row, im_row = {}, {}
            for side, S in (('b', S0), ('t', S1)):
                sgn = 1 if side == 'b' else -1
                seen = set()
                for i, x in enumerate(S):
                    if xor(x, e) not in S:
                        continue
                    j = S.index(xor(x, e))
                    key = (side,) + tuple(sorted((i, j)))
                    if key in seen:
                        continue
                    seen.add(key)
                    a, b = sorted((i, j))
                    sa = (-1) ** dot(z, S[a])
                    sb = (-1) ** dot(z, S[b])
                    # term is s_b * conj(c_a) c_b + s_a * conj(c_b) c_a
                    if sa == sb:
                        re_row[('Re', side, a, b)] = re_row.get(('Re', side, a, b), 0) + sgn * 2 * sa
                    else:
                        im_row[('Im', side, a, b)] = im_row.get(('Im', side, a, b), 0) + sgn * 2 * sb
            if re_row:
                rows.append((('Re', e, z), re_row))
            if im_row:
                rows.append((('Im', e, z), im_row))
    return rows


def analyse_diag(S0, S1, verbose=True):
    rows = coherence_system(S0, S1)
    varset = sorted({v for _, r in rows for v in r})
    idx = {v: n for n, v in enumerate(varset)}
    M = sp.zeros(len(rows), len(varset))
    for n, (_, r) in enumerate(rows):
        for v, co in r.items():
            M[n, idx[v]] = co
    rref, piv = M.rref()
    ns = M.nullspace()
    if verbose:
        print('diagonal conditions: %d rows, %d coherence unknowns, rank %d, nullity %d'
              % (len(rows), len(varset), len(piv), len(ns)))
    forced = [varset[c] for c in range(len(varset))
              if all(M[n, c] == 0 or sum(1 for cc in range(len(varset)) if M[n, cc] != 0) > 1
                     for n in range(len(rows)))]
    # coordinates forced to zero: those not in the support of any nullspace vector
    free_sup = set()
    for v in ns:
        for c in range(len(varset)):
            if v[c] != 0:
                free_sup.add(c)
    zeros = [varset[c] for c in range(len(varset)) if c not in free_sup]
    return rows, varset, M, rref, piv, ns, zeros


if __name__ == '__main__':
    from scan import ORBITS
    from propagate import pdim, DLP
    for oid in [int(a) for a in sys.argv[1:]] or [33]:
        a, q, sz = ORBITS[oid]
        S0 = fiber(a, q, 0)
        ds = [x for x in range(1, q) if fiber(a, q, x)
              and (sz is None or (len(S0), len(fiber(a, q, x))) == sz)
              and pdim(S0, fiber(a, q, x)) == DLP[oid]]
        S1 = fiber(a, q, ds[0])
        print('=== orbit %d  delta=%d ===' % (oid, ds[0]))
        rows, varset, M, rref, piv, ns, zeros = analyse_diag(S0, S1)
        print('coherences forced to vanish by the diagonal system alone: %d' % len(zeros))
        for v in zeros:
            print('    %s  %s[%d,%d]' % (v[0], v[1], v[2], v[3]))
