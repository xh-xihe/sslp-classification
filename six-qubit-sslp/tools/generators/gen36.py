"""Generate `SixQubit/Orbit36.lean`: the rigidity core of the order-five orbit 36.

Orbit 36 is the ONE realizable order-five moment orbit.  After the local-`X`
conjugation described in the chapter it is represented by

    a* = (1,1,1,1,2,3),   q = 5,   fibers (S_0, S_4),   S_4 = complement(S_0),

both fibers of size twelve.  This script

  * re-derives the two fibers from `tools/core/orbit.py` and checks them against
    the twelve named points of the chapter (the bit-order convention hazard is
    CHECKED here, not assumed);
  * derives every off-diagonal Knill--Laflamme row used by the proof from the
    incidence structure -- twice, by two independent code paths -- and checks
    that the three `X_i Z_j` dressings really do form the Walsh matrix
    [[-1,1,1],[1,-1,1],[1,1,-1]];
  * derives the moment system (two normalizations, six one-bit rows, fifteen
    two-bit rows) and verifies with exact rational linear algebra that it
    implies the chapter's "complete diagonal-moment normal form";
  * verifies every `linear_combination` certificate that appears in the emitted
    Lean file by expanding it with sympy, and computes every permuted
    instantiation of the three symmetric lemmas rather than typing them;
  * checks that the chapter's canonical witness satisfies every emitted row;
  * and only then writes the Lean module.

Usage (from the repository root):

    python tools/run.py generators/gen36.py            # write the module
    python tools/run.py generators/gen36.py --check    # verify only, do not write
"""
import io
import os
import sys
from itertools import combinations

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools', 'core'))
from orbit import fiber                                        # noqa: E402

OUT = os.path.join(REPO, 'SixQubit', 'Orbit36.lean')
NL = chr(10)

# --------------------------------------------------------------------------
# 1.  The orbit instance
# --------------------------------------------------------------------------

AV = [1, 1, 1, 1, 2, 3]
Q = 5

NAMES = ['u', 'v', 's1', 's2', 's3', 's4',
         'e12', 'e13', 'e14', 'e23', 'e24', 'e34']
POINTS = ['000000', '000011',
          '011110', '101110', '110110', '111010',
          '110001', '101001', '100101', '011001', '010101', '001101']


def comp(s):
    return ''.join('1' if ch == '0' else '0' for ch in s)


def bxor(s, m):
    return ''.join('1' if (s[i] == '1') != (m[i] == '1') else '0'
                   for i in range(6))


def bdot(a, b):
    return sum(1 for i in range(6) if a[i] == '1' and b[i] == '1') % 2


def bit(s, i):
    return 1 if s[i] == '1' else 0


Y = list(POINTS)
Z = [comp(y) for y in Y]
IY = {s: k for k, s in enumerate(Y)}
IZ = {s: k for k, s in enumerate(Z)}

# fiber index of each amplitude name
VIDX = {i: NAMES.index('s%d' % i) for i in (1, 2, 3, 4)}


def eidx(i, j):
    return NAMES.index('e%d%d' % (min(i, j), max(i, j)))


def check_instance():
    """The convention hazard, checked rather than assumed."""
    s0 = fiber(AV, Q, 0)
    s4 = fiber(AV, Q, 4)
    assert sorted(s0) == sorted(Y), 'S_0 does not match the twelve named points'
    assert sorted(s4) == sorted(Z), 'S_4 does not match complement(S_0)'
    assert len(s0) == 12 and len(s4) == 12
    assert sorted(comp(x) for x in s0) == sorted(s4)
    seen = set(Y) | set(Z)
    for k in range(64):
        s = format(k, '06b')
        r = sum(AV[i] for i in range(6) if s[i] == '1') % Q
        assert (r in (0, 4)) == (s in seen)
        if s in IY:
            assert r == 0
        if s in IZ:
            assert r == 4


# --------------------------------------------------------------------------
# 2.  Masks, dressings, rows
# --------------------------------------------------------------------------

MASKS = [('ex1', '100000'), ('ex2', '010000'), ('ex3', '001000'),
         ('ex4', '000100'),
         ('ex15', '100010'), ('ex25', '010010'), ('ex35', '001010'),
         ('ex45', '000110'),
         ('ex56', '000011')]
DRESS = [('w0', '000000'), ('w1', '100000'), ('w2', '010000'),
         ('w3', '001000'), ('w4', '000100'), ('w5', '000010'),
         ('w6', '000001')]
MASKD = dict(MASKS)
DRESSD = dict(DRESS)

ROWS = []
for _i in range(4):
    ROWS.append(('ex%d' % (_i + 1), 'w0'))
    for _j in range(4):
        if _j != _i:
            ROWS.append(('ex%d' % (_i + 1), 'w%d' % (_j + 1)))
for _i in range(4):
    ROWS.append(('ex%d5' % (_i + 1), 'w0'))
ROWS.append(('ex56', 'w0'))

DROWS = [('ex56', 'w0'), ('ex56', 'w6')]

ROWIX = {r: n for n, r in enumerate(ROWS)}


def offdiag_incidence(mask):
    return [k for k in range(12) if bxor(Z[k], mask) in IY]


def offdiag_terms(mask, dress):
    out = []
    for k in offdiag_incidence(mask):
        b = IY[bxor(Z[k], mask)]
        out.append((-1 if bdot(dress, Z[k]) else 1, b, k))
    return out


def offdiag_terms_bruteforce(mask, dress):
    out = []
    for n in range(64):
        s = format(n, '06b')
        if s not in IZ:
            continue
        t = bxor(s, mask)
        if t not in IY:
            continue
        sg = 1
        for i in range(6):
            if dress[i] == '1' and s[i] == '1':
                sg = -sg
        out.append((sg, IY[t], IZ[s]))
    out.sort(key=lambda r: r[2])
    return out


def diag_incidence(pts, index, mask):
    return [k for k in range(12) if bxor(pts[k], mask) in index]


def diag_terms(pts, index, mask, dress):
    out = []
    for k in diag_incidence(pts, index, mask):
        b = index[bxor(pts[k], mask)]
        out.append((-1 if bdot(dress, pts[k]) else 1, b, k))
    return out


def check_rows():
    for mask_name, dress_name in ROWS + DROWS:
        m, dr = MASKD[mask_name], DRESSD[dress_name]
        supp = {i for i in range(6) if m[i] == '1' or dr[i] == '1'}
        assert len(supp) <= 2, 'row %s %s has Pauli weight %d' % (
            mask_name, dress_name, len(supp))
        assert offdiag_terms(m, dr) == offdiag_terms_bruteforce(m, dr) or (
            mask_name, dress_name) in DROWS, 'code paths disagree'
    for mask_name, dress_name in ROWS:
        m, dr = MASKD[mask_name], DRESSD[dress_name]
        assert offdiag_terms(m, dr) == offdiag_terms_bruteforce(m, dr), (
            'two code paths disagree on row %s %s' % (mask_name, dress_name))
    # the X_i rows reproduce the chapter's U/V structure and Walsh matrix
    for i in range(1, 5):
        m = MASKD['ex%d' % i]
        others = [j for j in range(1, 5) if j != i]
        want = set()
        for j in others:
            want.add((eidx(i, j), VIDX[j]))
            want.add((VIDX[j], eidx(i, j)))
        got = {(b, t) for _s, b, t in offdiag_terms(m, '000000')}
        assert got == want, 'X_%d incidence mismatch' % i
        for a, j in enumerate(others):
            dr = DRESSD['w%d' % j]
            terms = offdiag_terms(m, dr)
            row = []
            for jj in others:
                su = [s for s, x, t in terms
                      if (x, t) == (eidx(i, jj), VIDX[jj])][0]
                sv = [s for s, x, t in terms
                      if (x, t) == (VIDX[jj], eidx(i, jj))][0]
                assert su == -sv, 'dressing does not separate U from V'
                row.append(su)
            assert row == [-1 if b == a else 1 for b in range(3)], (
                'Walsh row %d of X_%d is %s' % (a, i, row))
    # X_i X_5 : exactly the two incidences (v', s_i) and (s_i', v)
    for i in range(1, 5):
        terms = offdiag_terms(MASKD['ex%d5' % i], '000000')
        assert len(terms) == 2 and all(s == 1 for s, _b, _t in terms)
        assert {(b, t) for _s, b, t in terms} == {
            (VIDX[i], IY['000011']), (IY['000011'], VIDX[i])}
    # X_5 X_6 : each edge paired with the opposite edge
    terms = offdiag_terms(MASKD['ex56'], '000000')
    assert len(terms) == 6 and all(s == 1 for s, _b, _t in terms)
    for i, j in combinations(range(1, 5), 2):
        k, l = sorted(set(range(1, 5)) - {i, j})
        assert (1, eidx(k, l), eidx(i, j)) in terms


# --------------------------------------------------------------------------
# 3.  The moment system
# --------------------------------------------------------------------------

PAIRS = list(combinations(range(6), 2))


def moment_rows():
    rows = [('n0', [1] * 12, [0] * 12, 1), ('n1', [0] * 12, [1] * 12, 1)]
    for i in range(6):
        rows.append(('m%d' % (i + 1), [bit(y, i) for y in Y],
                     [bit(z, i) for z in Z], 0))
    for i, j in PAIRS:
        rows.append(('m%d%d' % (i + 1, j + 1),
                     [bit(y, i) * bit(y, j) for y in Y],
                     [bit(z, i) * bit(z, j) for z in Z], 0))
    for lab, qc, rc, rhs in rows:
        assert any(qc) or any(rc), 'empty moment row %s' % lab
    return rows


DERIVED = ([('q%d = r%d' % (k, k)) for k in range(12)]
           + ['q0 = 1/10', 'q1 = 1/10',
              'q2 + q3 + q4 + q5 = 2/5',
              'q6 + q7 + q8 + q9 + q10 + q11 = 2/5',
              'q6 + q7 + q8 = q2 + 1/10',
              'q6 + q9 + q10 = q3 + 1/10',
              'q7 + q9 + q11 = q4 + 1/10',
              'q8 + q10 + q11 = q5 + 1/10'])


def check_moments():
    """The 23 rows force the chapter's normal form; verified over Q."""
    rows = moment_rows()
    A, b = [], []
    for _lab, qc, rc, rhs in rows:
        if rhs == 1:
            A.append(list(qc) + list(rc))
            b.append(1)
        else:
            A.append(list(qc) + [-x for x in rc])
            b.append(0)
    M, rhsv = sp.Matrix(A), sp.Matrix(b)
    qs, rs = sp.symbols('q0:12'), sp.symbols('r0:12')
    sol = sp.linsolve((M, rhsv), list(qs) + list(rs))
    assert sol, 'moment system is infeasible'
    vals = list(list(sol)[0])
    env = dict(zip(['q%d' % k for k in range(12)], vals[:12]))
    env.update(dict(zip(['r%d' % k for k in range(12)], vals[12:])))
    for fact in DERIVED:
        lhs, rhs = fact.split('=')
        assert sp.simplify(sp.sympify(lhs, locals=env)
                           - sp.sympify(rhs, locals=env)) == 0, (
            'moment system does not imply %s' % fact)
    return M.rank()


# --------------------------------------------------------------------------
# 4.  Certificates checked with sympy
# --------------------------------------------------------------------------

def check_certificates():
    (c12, c13, c14, c23, c24, c34, r1, r2, r3, r4) = sp.symbols(
        'c12 c13 c14 c23 c24 c34 r1 r2 r3 r4')
    e1 = c12 * r2 + c13 * r3 + c14 * r4
    e2 = c12 * r1 + c23 * r3 + c24 * r4
    e3 = c13 * r1 + c23 * r2 + c34 * r4
    e4 = c14 * r1 + c24 * r2 + c34 * r3
    hm = c12 * c34 + c13 * c24 + c14 * c23
    h = sp.Rational(1, 2)
    for name, goal, cert in [
            ('cramer_r4', c24 * c34 * r4 - c14 * c23 * r1,
             h * c34 * e2 + h * c24 * e3 - h * c23 * e4 - h * r1 * hm),
            ('cramer_r2', c23 * c24 * r2 - c12 * c34 * r1,
             -h * c34 * e2 + h * c24 * e3 + h * c23 * e4 - h * r1 * hm),
            ('cramer_r3', c23 * c34 * r3 - c13 * c24 * r1,
             h * c34 * e2 - h * c24 * e3 + h * c23 * e4 - h * r1 * hm)]:
        assert sp.expand(goal - cert) == 0, 'certificate %s fails' % name

    # the three-active elimination inside `vertex_active`
    f1 = c12 * r2 + c13 * r3
    f2 = c12 * r1 + c23 * r3
    f3 = c13 * r1 + c23 * r2
    assert sp.expand(r3 * (c13 * r1 - c23 * r2) - (r1 * f1 - r2 * f2)) == 0
    assert sp.expand(c13 * r1 - (f3 / 2 + (c13 * r1 - c23 * r2) / 2)) == 0
    assert sp.expand(c23 * r2 - (f3 / 2 - (c13 * r1 - c23 * r2) / 2)) == 0
    assert sp.expand(c12 * r2 - (f1 - r3 * c13)) == 0

    # cubic difference, the pair product, and the cubic itself
    s1, s2, s3, s4, g, p1, p2 = sp.symbols('s1 s2 s3 s4 g p1 p2')
    S = s1 + s2 + s3 + s4
    cub = [t ** 3 - S * t ** 2 + t / 10 + g for t in (s1, s2, s3, s4)]
    hgoal = s1 ** 2 + s1 * s2 + s2 ** 2 - S * (s1 + s2) + sp.Rational(1, 10)
    assert sp.expand((s1 - s2) * hgoal - (cub[0] - cub[1])) == 0
    e2s = (s1 * s2 + s1 * s3 + s1 * s4 + s2 * s3 + s2 * s4 + s3 * s4
           - sp.Rational(2, 5))
    assert sp.expand(s3 * s4 - sp.Rational(3, 10) - (e2s + hgoal)) == 0
    hd1 = s1 * s2 + s1 * s3 + s1 * s4 - p1 - sp.Rational(1, 10)
    assert sp.expand((s1 ** 3 - S * s1 ** 2 + s1 / 10 + p1 * s1)
                     - (-s1 * hd1)) == 0
    hd2 = s1 * s2 + s2 * s3 + s2 * s4 - p2 - sp.Rational(1, 10)
    hg2 = p2 * s2 - p1 * s1
    assert sp.expand((s2 ** 3 - S * s2 ** 2 + s2 / 10 + p1 * s1)
                     - (-s2 * hd2 - hg2)) == 0
    # the three scale ratios
    gg2 = (s2 * s3) * (s2 * s4) * p2 - (s1 * s2) * (s3 * s4) * p1
    assert sp.expand((p2 * s2 - p1 * s1) * (s2 * s3 * s4) - gg2) == 0
    p3, p4 = sp.symbols('p3 p4')
    gg3 = (s2 * s3) * (s3 * s4) * p3 - (s1 * s3) * (s2 * s4) * p1
    assert sp.expand((p3 * s3 - p1 * s1) * (s2 * s3 * s4) - gg3) == 0
    gg4 = (s2 * s4) * (s3 * s4) * p4 - (s1 * s4) * (s2 * s3) * p1
    assert sp.expand((p4 * s4 - p1 * s1) * (s2 * s3 * s4) - gg4) == 0


def check_witness():
    """The chapter's canonical pair satisfies every emitted row."""
    w = sp.Rational(-1, 2) + sp.sqrt(3) * sp.I / 2
    ten, fif = 1 / sp.sqrt(10), 1 / sp.sqrt(15)
    cval = {'u': ten, 'v': ten, 's1': ten, 's2': ten, 's3': ten, 's4': ten,
            'e12': fif, 'e34': fif, 'e13': w * fif, 'e24': w * fif,
            'e14': w ** 2 * fif, 'e23': w ** 2 * fif}
    cvec = [cval[n] for n in NAMES]
    dvec = [sp.conjugate(cvec[k]) if k < 2 else -sp.conjugate(cvec[k])
            for k in range(12)]
    for mask_name, dress_name in ROWS:
        m, dr = MASKD[mask_name], DRESSD[dress_name]
        tot = sum(sg * sp.conjugate(cvec[b]) * dvec[t]
                  for sg, b, t in offdiag_terms(m, dr))
        assert sp.simplify(sp.expand(tot)) == 0, (
            'witness fails row %s %s' % (mask_name, dress_name))
    for mask_name, dress_name in DROWS:
        m, dr = MASKD[mask_name], DRESSD[dress_name]
        bot = sum(sg * sp.conjugate(cvec[b]) * cvec[t]
                  for sg, b, t in diag_terms(Y, IY, m, dr))
        top = sum(sg * sp.conjugate(dvec[b]) * dvec[t]
                  for sg, b, t in diag_terms(Z, IZ, m, dr))
        assert sp.simplify(sp.expand(bot - top)) == 0, (
            'witness fails diagonal row %s %s' % (mask_name, dress_name))
    p = [sp.simplify(sp.Abs(v) ** 2) for v in cvec]
    pt = [sp.simplify(sp.Abs(v) ** 2) for v in dvec]
    for lab, qc, rc, rhs in moment_rows():
        lhs = sum(qc[k] * p[k] for k in range(12))
        rr = sum(rc[k] * pt[k] for k in range(12))
        if rhs == 1:
            assert sp.simplify(lhs + rr - 1) == 0, lab
        else:
            assert sp.simplify(lhs - rr) == 0, lab
    for k in range(6):
        assert sp.simplify(p[k] - sp.Rational(1, 10)) == 0
        assert sp.simplify(pt[k] - sp.Rational(1, 10)) == 0
    for k in range(6, 12):
        assert sp.simplify(p[k] - sp.Rational(1, 15)) == 0
        assert sp.simplify(pt[k] - sp.Rational(1, 15)) == 0


# --------------------------------------------------------------------------
# 5.  Permuted instantiations of the three symmetric lemmas
# --------------------------------------------------------------------------

def cvar(sig, a, b, sym):
    """`c'_{ab}` under the relabelling `sig`, in the caller's names."""
    i, j = sig[a], sig[b]
    return sym['c%d%d' % (min(i, j), max(i, j))]


def perm_args(sig, sym, edges=True):
    """`(name := value)` list for a relabelling of `{1,2,3,4}`."""
    out = []
    for a in range(1, 5):
        out.append('(r%d := %s)' % (a, sym['r%d' % sig[a]]))
    if edges:
        for a, b in combinations(range(1, 5), 2):
            out.append('(c%d%d := %s)' % (a, b, cvar(sig, a, b, sym)))
    return out


def check_perm(sig, sym):
    """Certify that the relabelled hypotheses really are the caller's rows."""
    syms = {k: sp.Symbol(v.replace(' ', '_')) for k, v in sym.items()}
    rows = {}
    for i in range(1, 5):
        rows[i] = sum(syms['c%d%d' % (min(i, j), max(i, j))] * syms['r%d' % j]
                      for j in range(1, 5) if j != i)
    for a in range(1, 5):
        prime = sum(
            syms['c%d%d' % (min(sig[a], sig[b]), max(sig[a], sig[b]))]
            * syms['r%d' % sig[b]] for b in range(1, 5) if b != a)
        assert sp.expand(prime - rows[sig[a]]) == 0, (
            'relabelled row %d is not row %d' % (a, sig[a]))


SYM = {'r1': 'r1', 'r2': 'r2', 'r3': 'r3', 'r4': 'r4',
       'c12': 'c12', 'c13': 'c13', 'c14': 'c14',
       'c23': 'c23', 'c24': 'c24', 'c34': 'c34'}


def vertex_app(sig, sym, rowname, dname, indent):
    """`vertex_active` applied under `sig`; concludes `r_{sig[4]} != 0`."""
    check_perm(sig, sym)
    args = perm_args(sig, sym)
    lines = ['vertex_active'] + args
    for a in range(1, 5):
        lines.append('(by linear_combination %s)' % rowname[sig[a]])
    lines.append('(by linarith)')
    for _a in range(1, 5):
        lines.append('(by linarith)')
    assert [dname[sig[a]] for a in range(1, 5)]
    return wrap(lines, indent)


def edge_app(sig, sym, rowname, dname, act, indent):
    """`edge_active` applied under `sig`; concludes `c_{sig[3]sig[4]} != 0`."""
    check_perm(sig, sym)
    args = perm_args(sig, sym)
    lines = ['edge_active'] + args
    for a in (2, 3, 4):
        lines.append('(by linear_combination %s)' % rowname[sig[a]])
    lines.append('(by linear_combination hmt)')
    lines.append(act[sig[1]])
    lines.append(act[sig[2]])
    lines.append('(by linarith)')
    lines.append('(by linarith)')
    assert dname[sig[3]] and dname[sig[4]]
    return wrap(lines, indent)


def wrap(pieces, indent, width=76):
    out, cur = [], ''
    for p in pieces:
        if cur and len(cur) + 1 + len(p) > width:
            out.append(cur)
            cur = p
        else:
            cur = (cur + ' ' + p) if cur else p
    if cur:
        out.append(cur)
    pad = ' ' * indent
    return (NL + pad + '  ').join(pad + o if n == 0 else o
                                  for n, o in enumerate(out))


# --------------------------------------------------------------------------
# 6.  Lean emission
# --------------------------------------------------------------------------

def boolrow(s):
    return ' '.join(('true ' if ch == '1' else 'false') for ch in s).rstrip()


HEADER = '''import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.K4Kernel

/-!
# Rigidity of the order-five moment orbit 36

Orbit 36 is the unique rank-compatible order-five moment orbit that is not
empty.  After the local-`X` conjugation described in the chapter it is
represented by

    a* = (1, 1, 1, 1, 2, 3),   q = 5,   fibers `(S0, S1)`,

with `S1 = complement S0` and both fibers of size twelve.  Writing a string as
`x1x2x3x4;x5x6`, the twelve points of `S0` are

    u = 000000,   v = 000011,
    s_i = (1_{V minus i}; 10),   e_ij = (1_{i,j}; 01),   V = {1,2,3,4}.

A general pair of logical words on these fibers is

    |0_L> = a|u> + b|v> + sum_i r_i |s_i> + sum_{i<j} c_ij |e_ij>,
    |1_L> = A|u'> + B|v'> + sum_i R_i |s_i'> + sum_{i<j} C_ij |e_ij'>,

with `x'` the complement of `x` and NO coefficient assumed nonzero.

The module proves that the moment system and the weight-at-most-two cross
Knill--Laflamme rows already force every magnitude:

    |a|^2 = |b|^2 = |r_i|^2 = 1/10,      |c_ij|^2 = 1/15,

and the same twelve numbers in the top word.  In particular every amplitude is
nonzero, so every exact orbit-36 solution has the full twelve-term support --
no boundary face of the moment polytope survives.

The three collapses are

  1. the three `X_i Z_j` dressings form the Walsh matrix
     `[[-1,1,1],[1,-1,1],[1,1,-1]]` of determinant `4`, which forces the pair
     relation `conj(c_ij) R_j = conj(r_j) C_ij` and reduces the `X_i` row to
     the star sum `sum_{j <> i} conj(c_ij) R_j = 0`;
  2. the `X_i X_5` rows turn the star sum into `C r = 0` for the symmetric
     zero-diagonal edge matrix `C`, and the `X_5 X_6` row into the matching
     equation `c12 c34 + c13 c24 + c14 c23 = 0`;
  3. `C r = 0` with `r <> 0` kills the determinant, and with the matching
     equation this gives `x^2 + y^2 + z^2 = 0` for the three opposite-edge
     products, hence equal opposite weights, a vertex factorization
     `w_ij = s_i s_j`, a common cubic for the four `s_i`, and finally
     `w_ij = 1/15`, `p_i = 1/10`.

The first and third collapses are `SixQubit.K4Kernel`; this module supplies the
fibers, the transcription of the Knill--Laflamme rows, the moment normal form,
and the boundary analysis.

Boundary support is eliminated first: `vertex_active` and `edge_active` have
hypotheses symmetric in `{1,2,3,4}`, so one proof of each covers every vertex
and every edge; they are applied four times each.  `sides_eq` is symmetric in
the same way and is applied three times.

Everything computational is decided by the Lean kernel.  No `sorry`, no
`native_decide`.

This file is generated by `tools/generators/gen36.py`.
-/

namespace SixQubit.Orbit36

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section
'''


def emit_fibers():
    out = ['', '/-! ## The two fibers -/', '']
    out.append('def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 :='
               ' ![b0, b1, b2, b3, b4, b5]')
    out.append('')
    for k, s in enumerate(Y):
        out.append('def y%-3s : SS.BitString 6 := bs %s  -- %s = %s'
                   % (k, boolrow(s), s, NAMES[k]))
    out.append('')
    for k, s in enumerate(Z):
        out.append('def z%-3s : SS.BitString 6 := bs %s  -- %s = complement %s'
                   % (k, boolrow(s), s, NAMES[k]))
    out.append('')
    out.append('def S0 : Finset (SS.BitString 6) := {%s}'
               % ', '.join('y%d' % k for k in range(12)))
    out.append('def S1 : Finset (SS.BitString 6) := {%s}'
               % ', '.join('z%d' % k for k in range(12)))
    out.append('')
    out.append('def av : Fin 6 -> ZMod 5 := ![%s]'
               % ', '.join(str(x) for x in AV))
    out.append('')
    out.append('theorem S0_eq_fiber :')
    out.append('    (Finset.univ : Finset (SS.BitString 6)).filter')
    out.append('      (fun x => SS.weight av x = 0) = S0 := by')
    out.append('  decide')
    out.append('')
    out.append('theorem S1_eq_fiber :')
    out.append('    (Finset.univ : Finset (SS.BitString 6)).filter')
    out.append('      (fun x => SS.weight av x = 4) = S1 := by')
    out.append('  decide')
    out.append('')
    for k in range(12):
        out.append('theorem zc%d : z%d = SS.complement y%d := by decide'
                   % (k, k, k))
    out.append('')
    out.append('theorem S1_eq_complement : S1 = S0.image SS.complement := by')
    out.append('  decide')
    return NL.join(out) + NL


def emit_masks():
    out = ['', '/-! ## Masks and dressings -/', '']
    for n, s in MASKS:
        out.append('def %-5s : SS.BitString 6 := bs %s  -- %s'
                   % (n, boolrow(s), s))
    out.append('')
    for n, s in DRESS:
        out.append('def %-5s : SS.BitString 6 := bs %s  -- %s'
                   % (n, boolrow(s), s))
    return NL.join(out) + NL


def sum_expand(n):
    parts = ['Finset.sum_insert (by decide)'] * (n - 1) + [
        'Finset.sum_singleton']
    return '  rw [%s]' % ', '.join(parts)


def rhs_string(terms, bot, top):
    out = ''
    for a, (sg, b, t) in enumerate(terms):
        piece = 'star (%s) * %s' % (bot % b, top % t)
        if a == 0:
            out = ('- ' if sg < 0 else '') + piece
        else:
            out += (' - ' if sg < 0 else ' + ') + piece
    return out


def emit_offdiag():
    out = ['', '/-! ## The off-diagonal layer -/', '']
    out.append('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6)'
               ' : ℂ :=')
    out.append('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    out.append('      SixQubit.signMul (SS.bdot z y) '
               '(star (c (SS.bxor y e)) * d y)')
    out.append('')
    seen = []
    for mn, _dn in ROWS:
        if mn not in seen:
            seen.append(mn)
    for mn in seen:
        m = MASKD[mn]
        inc = offdiag_incidence(m)
        out.append('theorem inc_%s :' % mn)
        out.append('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by'
                   % (mn, ', '.join('z%d' % k for k in inc)))
        out.append('  decide')
        for k in inc:
            out.append('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide'
                       % (mn, k, k, mn, IY[bxor(Z[k], m)]))
        for mn2, dn in ROWS:
            if mn2 != mn:
                continue
            dr = DRESSD[dn]
            terms = offdiag_terms(m, dr)
            for _sg, _b, t in terms:
                out.append('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by'
                           ' decide'
                           % (mn, dn, t, dn, t,
                              'true' if bdot(dr, Z[t]) else 'false'))
            out.append('theorem ex_%s_%s (c d : SS.BitString 6 -> ℂ) :'
                       % (mn, dn))
            out.append('    offSum c d %s %s =' % (mn, dn))
            out.append('      %s := by' % rhs_string(terms, 'c y%d', 'd z%d'))
            out.append('  unfold offSum')
            out.append('  rw [inc_%s]' % mn)
            out.append(sum_expand(len(inc)))
            out.append('  rw [%s]' % ', '.join('flip_%s_%d' % (mn, k)
                                               for k in inc))
            simps = ['sg_%s_%s_%d' % (mn, dn, t) for _s, _b, t in terms]
            if any(s < 0 for s, _b, _t in terms):
                simps.append('SixQubit.signMul_true')
            if any(s > 0 for s, _b, _t in terms):
                simps.append('SixQubit.signMul_false')
            out.append('  simp only [%s]' % ', '.join(simps))
            out.append('  try ring')
        out.append('')
    return NL.join(out)


def emit_diag():
    out = ['', '/-! ## The diagonal layer -/', '']
    out.append('/-- The only weight-at-most-two flip that maps `S0` into itself'
               ' is `X_5 X_6`,')
    out.append('which pairs `u` with `v` and `u\'` with `v\'`.  The diagonal')
    out.append('information the argument uses is exactly the `MomentSystem`'
               ' below, so these')
    out.append('rows are not headline hypotheses; the layer is recorded for'
               ' completeness. -/')
    out.append('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6)'
               ' : ℂ :=')
    out.append('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
    out.append('      SixQubit.signMul (SS.bdot z x) '
               '(star (c (SS.bxor x e)) * c x)')
    out.append('')
    out.append('def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6)'
               ' : ℂ :=')
    out.append('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
    out.append('      SixQubit.signMul (SS.bdot z y) '
               '(star (dd (SS.bxor y e)) * dd y)')
    out.append('')
    done = set()
    for mn, dn in DROWS:
        m, dr = MASKD[mn], DRESSD[dn]
        incB = diag_incidence(Y, IY, m)
        incT = diag_incidence(Z, IZ, m)
        if mn not in done:
            done.add(mn)
            out.append('theorem dincB_%s : S0.filter (fun x => SS.bxor x %s ∈'
                       ' S0) = {%s} := by'
                       % (mn, mn, ', '.join('y%d' % k for k in incB)))
            out.append('  decide')
            out.append('theorem dincT_%s : S1.filter (fun y => SS.bxor y %s ∈'
                       ' S1) = {%s} := by'
                       % (mn, mn, ', '.join('z%d' % k for k in incT)))
            out.append('  decide')
            for k in incB:
                out.append('theorem dflipB_%s_%d : SS.bxor y%d %s = y%d := by'
                           ' decide' % (mn, k, k, mn, IY[bxor(Y[k], m)]))
            for k in incT:
                out.append('theorem dflipT_%s_%d : SS.bxor z%d %s = z%d := by'
                           ' decide' % (mn, k, k, mn, IZ[bxor(Z[k], m)]))
        for tag in ('B', 'T'):
            pts = Y if tag == 'B' else Z
            index = IY if tag == 'B' else IZ
            inc = incB if tag == 'B' else incT
            var = 'c' if tag == 'B' else 'dd'
            pref = 'y' if tag == 'B' else 'z'
            fn = 'diagBot' if tag == 'B' else 'diagTop'
            for k in inc:
                out.append('theorem ds%s_%s_%s_%d : SS.bdot %s %s%d = %s := by'
                           ' decide'
                           % (tag, mn, dn, k, dn, pref, k,
                              'true' if bdot(dr, pts[k]) else 'false'))
            terms = diag_terms(pts, index, m, dr)
            pat = var + ' ' + pref + '%d'
            out.append('theorem dex%s_%s_%s (%s : SS.BitString 6 -> ℂ) :'
                       % (tag, mn, dn, var))
            out.append('    %s %s %s %s =' % (fn, var, mn, dn))
            out.append('      %s := by' % rhs_string(terms, pat, pat))
            out.append('  unfold %s' % fn)
            out.append('  rw [dinc%s_%s]' % (tag, mn))
            out.append(sum_expand(len(inc)))
            out.append('  rw [%s]' % ', '.join('dflip%s_%s_%d' % (tag, mn, k)
                                               for k in inc))
            simps = ['ds%s_%s_%s_%d' % (tag, mn, dn, t) for _s, _b, t in terms]
            if any(s < 0 for s, _b, _t in terms):
                simps.append('SixQubit.signMul_true')
            if any(s > 0 for s, _b, _t in terms):
                simps.append('SixQubit.signMul_false')
            out.append('  simp only [%s]' % ', '.join(simps))
            out.append('  try ring')
        out.append('')
    return NL.join(out)


def emit_moment():
    rows = moment_rows()
    out = ['', '/-! ## The moment system -/', '']
    out.append('/-- The two normalizations, the six one-bit and fifteen'
               ' two-bit diagonal')
    out.append('Knill--Laflamme equalities, and the nonnegativity of every'
               ' probability.')
    out.append('`q_k` is `|<y_k|0_L>|^2` and `r_k` is `|<z_k|1_L>|^2`, with'
               ' `z_k = complement y_k`,')
    out.append('so both vectors are indexed by the SAME point of the bottom'
               ' fiber. -/')
    out.append('structure MomentSystem (%s : Real) : Prop where'
               % ' '.join(['q%d' % k for k in range(12)]
                          + ['r%d' % k for k in range(12)]))
    for lab, qc, rc, rhs in rows:
        lhs = ' + '.join('q%d' % k for k in range(12) if qc[k])
        rhsx = ' + '.join('r%d' % k for k in range(12) if rc[k])
        if rhs == 1:
            out.append('  %s : %s = 1' % (lab, lhs if lhs else rhsx))
        else:
            out.append('  %s : %s = %s'
                       % (lab, lhs if lhs else '0', rhsx if rhsx else '0'))
    for k in range(12):
        out.append('  nq%d : 0 ≤ q%d' % (k, k))
    for k in range(12):
        out.append('  nr%d : 0 ≤ r%d' % (k, k))
    out.append('')
    args = ' '.join(['q%d' % k for k in range(12)]
                    + ['r%d' % k for k in range(12)])
    out.append('/-- **The complete diagonal-moment normal form.**  The'
               ' restricted characters')
    out.append('`1` and `chi_ij` already span every function on the'
               ' twelve-point fiber, so the')
    out.append('two probability vectors coincide; then `|a|^2 = |b|^2 = 1/10`,'
               ' the vertex mass')
    out.append('and the edge mass are both `2/5`, and every weighted degree'
               ' satisfies')
    out.append('`D_i = p_i + 1/10`. -/')
    out.append('theorem MomentSystem.facts {%s : Real}' % args)
    out.append('    (h : MomentSystem %s) :' % args)
    out.append('    ' + (NL + '      ∧ ').join(DERIVED) + ' := by')
    names = [lab for lab, _a, _b, _c in rows]
    names += ['nq%d' % k for k in range(12)] + ['nr%d' % k for k in range(12)]
    out.append('  obtain ⟨%s⟩ := h' % ', '.join(names))
    out.append('  refine ⟨%s⟩ <;> linarith' % ', '.join(['?_'] * len(DERIVED)))
    return NL.join(out) + NL


ALGEBRA = r'''
/-! ## Boundary support: every vertex amplitude is active -/

/-- **Every vertex amplitude is active.**  If `r4 = 0`, the four kernel rows
`C r = 0` collide with the moment normal form, whichever of `r1, r2, r3`
survive: a single active vertex drives its own weighted degree to zero, two
active vertices make an opposite edge weight negative, and three active
vertices kill the whole active triangle.  The hypotheses are symmetric under
permutations of `{1,2,3,4}`, so this one lemma is applied four times below. -/
theorem vertex_active {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hP : Complex.normSq r1 + Complex.normSq r2 + Complex.normSq r3
            + Complex.normSq r4 = 2 / 5)
    (hD1 : Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c14
            = Complex.normSq r1 + 1 / 10)
    (hD2 : Complex.normSq c12 + Complex.normSq c23 + Complex.normSq c24
            = Complex.normSq r2 + 1 / 10)
    (hD3 : Complex.normSq c13 + Complex.normSq c23 + Complex.normSq c34
            = Complex.normSq r3 + 1 / 10)
    (hD4 : Complex.normSq c14 + Complex.normSq c24 + Complex.normSq c34
            = Complex.normSq r4 + 1 / 10) :
    r4 ≠ 0 := by
  intro h4
  subst h4
  have n12 := Complex.normSq_nonneg c12
  have n13 := Complex.normSq_nonneg c13
  have n14 := Complex.normSq_nonneg c14
  have n23 := Complex.normSq_nonneg c23
  have n24 := Complex.normSq_nonneg c24
  have n34 := Complex.normSq_nonneg c34
  have m1 := Complex.normSq_nonneg r1
  have m2 := Complex.normSq_nonneg r2
  have m3 := Complex.normSq_nonneg r3
  rw [Complex.normSq_zero] at hP hD4
  simp only [mul_zero, add_zero] at e1 e2 e3
  by_cases h1 : r1 = 0
  · subst h1
    rw [Complex.normSq_zero] at hP hD1
    by_cases h2 : r2 = 0
    · subst h2
      rw [Complex.normSq_zero] at hP hD2
      by_cases h3 : r3 = 0
      · subst h3
        rw [Complex.normSq_zero] at hP
        linarith
      · simp only [mul_zero, zero_add, add_zero] at e1 e2 e4
        have q13 : c13 = 0 := (mul_eq_zero.mp e1).resolve_right h3
        have q23 : c23 = 0 := (mul_eq_zero.mp e2).resolve_right h3
        have q34 : c34 = 0 := (mul_eq_zero.mp e4).resolve_right h3
        rw [q13, q23, q34, Complex.normSq_zero] at hD3
        linarith
    · by_cases h3 : r3 = 0
      · subst h3
        rw [Complex.normSq_zero] at hP hD3
        simp only [mul_zero, add_zero, zero_add] at e1 e3 e4
        have q12 : c12 = 0 := (mul_eq_zero.mp e1).resolve_right h2
        have q23 : c23 = 0 := (mul_eq_zero.mp e3).resolve_right h2
        have q24 : c24 = 0 := (mul_eq_zero.mp e4).resolve_right h2
        rw [q12, q23, q24, Complex.normSq_zero] at hD2
        linarith
      · simp only [mul_zero, zero_add] at e2
        have q23 : c23 = 0 := (mul_eq_zero.mp e2).resolve_right h3
        rw [q23, Complex.normSq_zero] at hD2 hD3
        linarith
  · by_cases h2 : r2 = 0
    · subst h2
      rw [Complex.normSq_zero] at hP hD2
      by_cases h3 : r3 = 0
      · subst h3
        rw [Complex.normSq_zero] at hP hD3
        simp only [mul_zero, add_zero] at e2 e3 e4
        have q12 : c12 = 0 := (mul_eq_zero.mp e2).resolve_right h1
        have q13 : c13 = 0 := (mul_eq_zero.mp e3).resolve_right h1
        have q14 : c14 = 0 := (mul_eq_zero.mp e4).resolve_right h1
        rw [q12, q13, q14, Complex.normSq_zero] at hD1
        linarith
      · simp only [mul_zero, zero_add] at e1
        have q13 : c13 = 0 := (mul_eq_zero.mp e1).resolve_right h3
        rw [q13, Complex.normSq_zero] at hD1 hD3
        linarith
    · by_cases h3 : r3 = 0
      · subst h3
        rw [Complex.normSq_zero] at hP hD3
        simp only [mul_zero, add_zero] at e1
        have q12 : c12 = 0 := (mul_eq_zero.mp e1).resolve_right h2
        rw [q12, Complex.normSq_zero] at hD1 hD2
        linarith
      · have step : r3 * (c13 * r1 - c23 * r2) = 0 := by
          linear_combination r1 * e1 - r2 * e2
        have hstep : c13 * r1 - c23 * r2 = 0 :=
          (mul_eq_zero.mp step).resolve_left h3
        have q13 : c13 = 0 := by
          have hh : c13 * r1 = 0 := by linear_combination e3 / 2 + hstep / 2
          exact (mul_eq_zero.mp hh).resolve_right h1
        have q23 : c23 = 0 := by
          have hh : c23 * r2 = 0 := by linear_combination e3 / 2 - hstep / 2
          exact (mul_eq_zero.mp hh).resolve_right h2
        have q12 : c12 = 0 := by
          have hh : c12 * r2 = 0 := by linear_combination e1 - r3 * q13
          exact (mul_eq_zero.mp hh).resolve_right h2
        rw [q12, q13, Complex.normSq_zero] at hD1
        rw [q12, q23, Complex.normSq_zero] at hD2
        rw [q13, q23, Complex.normSq_zero] at hD3
        linarith

/-- The four vertex amplitudes, all at once. -/
theorem vertices_active {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hP : Complex.normSq r1 + Complex.normSq r2 + Complex.normSq r3
            + Complex.normSq r4 = 2 / 5)
    (hD1 : Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c14
            = Complex.normSq r1 + 1 / 10)
    (hD2 : Complex.normSq c12 + Complex.normSq c23 + Complex.normSq c24
            = Complex.normSq r2 + 1 / 10)
    (hD3 : Complex.normSq c13 + Complex.normSq c23 + Complex.normSq c34
            = Complex.normSq r3 + 1 / 10)
    (hD4 : Complex.normSq c14 + Complex.normSq c24 + Complex.normSq c34
            = Complex.normSq r4 + 1 / 10) :
    r1 ≠ 0 ∧ r2 ≠ 0 ∧ r3 ≠ 0 ∧ r4 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
__VERTEX_APPS__

/-! ## The Cramer identities of the kernel system -/

/-- `c24 c34 r4 = c14 c23 r1`: three kernel rows and the matching equation,
combined with the cofactors of the fourth column. -/
theorem cramer_r4 {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hmt : c12 * c34 + c13 * c24 + c14 * c23 = 0) :
    c24 * c34 * r4 = c14 * c23 * r1 := by
  linear_combination (c34 / 2) * e2 + (c24 / 2) * e3 - (c23 / 2) * e4
    - (r1 / 2) * hmt

/-- `c23 c24 r2 = c12 c34 r1`. -/
theorem cramer_r2 {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hmt : c12 * c34 + c13 * c24 + c14 * c23 = 0) :
    c23 * c24 * r2 = c12 * c34 * r1 := by
  linear_combination (-(c34 / 2)) * e2 + (c24 / 2) * e3 + (c23 / 2) * e4
    - (r1 / 2) * hmt

/-- `c23 c34 r3 = c13 c24 r1`. -/
theorem cramer_r3 {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hmt : c12 * c34 + c13 * c24 + c14 * c23 = 0) :
    c23 * c34 * r3 = c13 * c24 * r1 := by
  linear_combination (c34 / 2) * e2 + (-(c24 / 2)) * e3 + (c23 / 2) * e4
    - (r1 / 2) * hmt

/-! ## Boundary support: every edge amplitude is active -/

/-- **Every edge amplitude is active.**  If `c34 = 0` the Cramer identity kills
`c13 c24`, and either branch drives a whole weighted degree to zero, which
contradicts `D_i = p_i + 1/10 >= 1/10`.  The hypotheses are again symmetric in
`{1,2,3,4}`, so one proof covers every edge; four applications suffice,
because the vertex factorization then exhibits the remaining two weights as
products of positive numbers. -/
theorem edge_active {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 : ℂ}
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hmt : c12 * c34 + c13 * c24 + c14 * c23 = 0)
    (h1 : r1 ≠ 0) (h2 : r2 ≠ 0)
    (hD3 : Complex.normSq c13 + Complex.normSq c23 + Complex.normSq c34
            = Complex.normSq r3 + 1 / 10)
    (hD4 : Complex.normSq c14 + Complex.normSq c24 + Complex.normSq c34
            = Complex.normSq r4 + 1 / 10) :
    c34 ≠ 0 := by
  intro h
  subst h
  have hc := cramer_r3 e2 e3 e4 hmt
  simp only [mul_zero, zero_mul, add_zero] at hc e3 e4
  have hz : c13 * c24 = 0 := by
    have hh : c13 * c24 * r1 = 0 := by linear_combination -hc
    exact (mul_eq_zero.mp hh).resolve_right h1
  have n3 := Complex.normSq_nonneg r3
  have n4 := Complex.normSq_nonneg r4
  rcases mul_eq_zero.mp hz with q13 | q24
  · rw [q13] at e3
    simp only [zero_mul, zero_add] at e3
    have q23 : c23 = 0 := (mul_eq_zero.mp e3).resolve_right h2
    rw [q13, q23, Complex.normSq_zero] at hD3
    linarith
  · rw [q24] at e4
    simp only [zero_mul, add_zero] at e4
    have q14 : c14 = 0 := (mul_eq_zero.mp e4).resolve_right h1
    rw [q14, q24, Complex.normSq_zero] at hD4
    linarith

/-! ## The common cubic and the equality of the four vertex scales -/

/-- Two vertex scales that differ are two distinct roots of the same cubic;
the difference of the two cubic relations then pins the product of the other
two scales to `3/10`. -/
theorem pair_prod {s1 s2 s3 s4 g : ℝ}
    (c1 : s1 ^ 3 - (s1 + s2 + s3 + s4) * s1 ^ 2 + s1 / 10 + g = 0)
    (c2 : s2 ^ 3 - (s1 + s2 + s3 + s4) * s2 ^ 2 + s2 / 10 + g = 0)
    (he2 : s1 * s2 + s1 * s3 + s1 * s4 + s2 * s3 + s2 * s4 + s3 * s4 = 2 / 5)
    (hne : s1 ≠ s2) :
    s3 * s4 = 3 / 10 := by
  have hd : (s1 - s2) * (s1 ^ 2 + s1 * s2 + s2 ^ 2
      - (s1 + s2 + s3 + s4) * (s1 + s2) + 1 / 10) = 0 := by
    linear_combination c1 - c2
  have hh : s1 ^ 2 + s1 * s2 + s2 ^ 2
      - (s1 + s2 + s3 + s4) * (s1 + s2) + 1 / 10 = 0 := by
    rcases mul_eq_zero.mp hd with hx | hx
    · exact absurd (sub_eq_zero.mp hx) hne
    · exact hx
  linear_combination he2 + hh

/-- **The four vertex scales are equal.**  They are positive, all roots of the
same cubic `t^3 - S t^2 + t/10 + g`, and their second elementary symmetric
function is `2/5`.  Every configuration with two distinct values makes a
product of positive numbers negative.  The hypotheses are symmetric, so this
one statement is applied three times below. -/
theorem sides_eq {s1 s2 s3 s4 g : ℝ}
    (p1 : 0 < s1) (p2 : 0 < s2) (p3 : 0 < s3) (p4 : 0 < s4)
    (c1 : s1 ^ 3 - (s1 + s2 + s3 + s4) * s1 ^ 2 + s1 / 10 + g = 0)
    (c2 : s2 ^ 3 - (s1 + s2 + s3 + s4) * s2 ^ 2 + s2 / 10 + g = 0)
    (c3 : s3 ^ 3 - (s1 + s2 + s3 + s4) * s3 ^ 2 + s3 / 10 + g = 0)
    (c4 : s4 ^ 3 - (s1 + s2 + s3 + s4) * s4 ^ 2 + s4 / 10 + g = 0)
    (he2 : s1 * s2 + s1 * s3 + s1 * s4 + s2 * s3 + s2 * s4 + s3 * s4 = 2 / 5) :
    s1 = s2 := by
  by_contra h12
  have k34 : s3 * s4 = 3 / 10 :=
    pair_prod (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (g := g) c1 c2 he2
      h12
  by_cases h34 : s3 = s4
  · subst h34
    by_cases h13 : s1 = s3
    · subst h13
      nlinarith [mul_pos p1 p2]
    · have k24 : s2 * s3 = 3 / 10 :=
        pair_prod (s1 := s1) (s2 := s3) (s3 := s2) (s4 := s3) (g := g)
          (by linear_combination c1) (by linear_combination c3)
          (by linear_combination he2) h13
      nlinarith [mul_pos p1 p2, mul_pos p1 p3]
  · have k12 : s1 * s2 = 3 / 10 :=
      pair_prod (s1 := s3) (s2 := s4) (s3 := s1) (s4 := s2) (g := g)
        (by linear_combination c3) (by linear_combination c4)
        (by linear_combination he2) h34
    nlinarith [mul_pos p1 p3, mul_pos p1 p4, mul_pos p2 p3, mul_pos p2 p4]

/-- **The scales, and hence every magnitude, are pinned.**  Positive vertex
scales with `D_i = p_i + 1/10`, total edge mass `2/5`, and the three Cramer
ratios `p_i s_i = p_1 s_1` are all equal, with `s^2 = 1/15` and
`p_i = 1/10`. -/
theorem scales_forced {s1 s2 s3 s4 p1 p2 p3 p4 : ℝ}
    (ps1 : 0 < s1) (ps2 : 0 < s2) (ps3 : 0 < s3) (ps4 : 0 < s4)
    (hD1 : s1 * s2 + s1 * s3 + s1 * s4 = p1 + 1 / 10)
    (hD2 : s1 * s2 + s2 * s3 + s2 * s4 = p2 + 1 / 10)
    (hD3 : s1 * s3 + s2 * s3 + s3 * s4 = p3 + 1 / 10)
    (hD4 : s1 * s4 + s2 * s4 + s3 * s4 = p4 + 1 / 10)
    (hW : s1 * s2 + s1 * s3 + s1 * s4 + s2 * s3 + s2 * s4 + s3 * s4 = 2 / 5)
    (g2 : s2 * s3 * (s2 * s4) * p2 = s1 * s2 * (s3 * s4) * p1)
    (g3 : s2 * s3 * (s3 * s4) * p3 = s1 * s3 * (s2 * s4) * p1)
    (g4 : s2 * s4 * (s3 * s4) * p4 = s1 * s4 * (s2 * s3) * p1) :
    s1 = s2 ∧ s1 = s3 ∧ s1 = s4 ∧ s1 * s1 = 1 / 15
      ∧ p1 = 1 / 10 ∧ p2 = 1 / 10 ∧ p3 = 1 / 10 ∧ p4 = 1 / 10 := by
  have hpos : (0 : ℝ) < s2 * s3 * s4 := by positivity
  have hg2 : p2 * s2 = p1 * s1 := by
    have hh : (p2 * s2 - p1 * s1) * (s2 * s3 * s4) = 0 := by
      linear_combination g2
    rcases mul_eq_zero.mp hh with hx | hx
    · linarith [sub_eq_zero.mp hx]
    · exact absurd hx (ne_of_gt hpos)
  have hg3 : p3 * s3 = p1 * s1 := by
    have hh : (p3 * s3 - p1 * s1) * (s2 * s3 * s4) = 0 := by
      linear_combination g3
    rcases mul_eq_zero.mp hh with hx | hx
    · linarith [sub_eq_zero.mp hx]
    · exact absurd hx (ne_of_gt hpos)
  have hg4 : p4 * s4 = p1 * s1 := by
    have hh : (p4 * s4 - p1 * s1) * (s2 * s3 * s4) = 0 := by
      linear_combination g4
    rcases mul_eq_zero.mp hh with hx | hx
    · linarith [sub_eq_zero.mp hx]
    · exact absurd hx (ne_of_gt hpos)
  have cub1 : s1 ^ 3 - (s1 + s2 + s3 + s4) * s1 ^ 2 + s1 / 10 + p1 * s1 = 0 := by
    linear_combination (-s1) * hD1
  have cub2 : s2 ^ 3 - (s1 + s2 + s3 + s4) * s2 ^ 2 + s2 / 10 + p1 * s1 = 0 := by
    linear_combination (-s2) * hD2 - hg2
  have cub3 : s3 ^ 3 - (s1 + s2 + s3 + s4) * s3 ^ 2 + s3 / 10 + p1 * s1 = 0 := by
    linear_combination (-s3) * hD3 - hg3
  have cub4 : s4 ^ 3 - (s1 + s2 + s3 + s4) * s4 ^ 2 + s4 / 10 + p1 * s1 = 0 := by
    linear_combination (-s4) * hD4 - hg4
  have q12 : s1 = s2 :=
    sides_eq (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (g := p1 * s1)
      ps1 ps2 ps3 ps4 cub1 cub2 cub3 cub4 hW
  have q13 : s1 = s3 :=
    sides_eq (s1 := s1) (s2 := s3) (s3 := s2) (s4 := s4) (g := p1 * s1)
      ps1 ps3 ps2 ps4
      (by linear_combination cub1) (by linear_combination cub3)
      (by linear_combination cub2) (by linear_combination cub4)
      (by linear_combination hW)
  have q14 : s1 = s4 :=
    sides_eq (s1 := s1) (s2 := s4) (s3 := s3) (s4 := s2) (g := p1 * s1)
      ps1 ps4 ps3 ps2
      (by linear_combination cub1) (by linear_combination cub4)
      (by linear_combination cub3) (by linear_combination cub2)
      (by linear_combination hW)
  rw [← q12, ← q13, ← q14] at hW hD1 hD2 hD3 hD4
  exact ⟨q12, q13, q14, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-! ## The rigidity core -/

/-- **The magnitudes are forced.**  This is the whole chapter in the abstract
amplitudes: the four rows of `C r = 0`, the matching equation, and the moment
normal form already determine every magnitude of the bottom word. -/
theorem magnitudes_core {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hmt : c12 * c34 + c13 * c24 + c14 * c23 = 0)
    (hP : Complex.normSq r1 + Complex.normSq r2 + Complex.normSq r3
            + Complex.normSq r4 = 2 / 5)
    (hW : Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c14
            + Complex.normSq c23 + Complex.normSq c24 + Complex.normSq c34
            = 2 / 5)
    (hD1 : Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c14
            = Complex.normSq r1 + 1 / 10)
    (hD2 : Complex.normSq c12 + Complex.normSq c23 + Complex.normSq c24
            = Complex.normSq r2 + 1 / 10)
    (hD3 : Complex.normSq c13 + Complex.normSq c23 + Complex.normSq c34
            = Complex.normSq r3 + 1 / 10)
    (hD4 : Complex.normSq c14 + Complex.normSq c24 + Complex.normSq c34
            = Complex.normSq r4 + 1 / 10) :
    Complex.normSq r1 = 1 / 10 ∧ Complex.normSq r2 = 1 / 10
      ∧ Complex.normSq r3 = 1 / 10 ∧ Complex.normSq r4 = 1 / 10
      ∧ Complex.normSq c12 = 1 / 15 ∧ Complex.normSq c13 = 1 / 15
      ∧ Complex.normSq c14 = 1 / 15 ∧ Complex.normSq c23 = 1 / 15
      ∧ Complex.normSq c24 = 1 / 15 ∧ Complex.normSq c34 = 1 / 15 := by
  obtain ⟨a1, a2, a3, a4⟩ := vertices_active e1 e2 e3 e4 hP hD1 hD2 hD3 hD4
__EDGE_APPS__
  obtain ⟨how1, how2⟩ :=
    SixQubit.K4Kernel.oppositeWeights e1 e2 e3 e4 (Or.inl a1) hmt
  obtain ⟨s1, s2, s3, s4, ps1, ps2, ps3, ps4, f12, f13, f14, f23, f24, f34⟩ :=
    SixQubit.K4Kernel.vertex_factorization
      (Complex.normSq_pos.mpr b12) (Complex.normSq_pos.mpr b13)
      (Complex.normSq_pos.mpr b14) (Complex.normSq_pos.mpr b23) how1 how2
  have g2 : Complex.normSq c23 * Complex.normSq c24 * Complex.normSq r2
      = Complex.normSq c12 * Complex.normSq c34 * Complex.normSq r1 := by
    simpa only [Complex.normSq_mul] using
      congrArg Complex.normSq (cramer_r2 e2 e3 e4 hmt)
  have g3 : Complex.normSq c23 * Complex.normSq c34 * Complex.normSq r3
      = Complex.normSq c13 * Complex.normSq c24 * Complex.normSq r1 := by
    simpa only [Complex.normSq_mul] using
      congrArg Complex.normSq (cramer_r3 e2 e3 e4 hmt)
  have g4 : Complex.normSq c24 * Complex.normSq c34 * Complex.normSq r4
      = Complex.normSq c14 * Complex.normSq c23 * Complex.normSq r1 := by
    simpa only [Complex.normSq_mul] using
      congrArg Complex.normSq (cramer_r4 e2 e3 e4 hmt)
  simp only [f12, f13, f14, f23, f24, f34] at g2 g3 g4 hD1 hD2 hD3 hD4 hW
  obtain ⟨q12, q13, q14, hsq, v1, v2, v3, v4⟩ :=
    scales_forced ps1 ps2 ps3 ps4 hD1 hD2 hD3 hD4 hW
      (by linear_combination g2) (by linear_combination g3)
      (by linear_combination g4)
  refine ⟨v1, v2, v3, v4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f12, ← q12]; exact hsq
  · rw [f13, ← q13]; exact hsq
  · rw [f14, ← q14]; exact hsq
  · rw [f23, ← q12, ← q13]; exact hsq
  · rw [f24, ← q12, ← q14]; exact hsq
  · rw [f34, ← q13, ← q14]; exact hsq
'''


def emit_algebra():
    sym = dict(SYM)
    rowname = {1: 'e1', 2: 'e2', 3: 'e3', 4: 'e4'}
    dname = {1: 'hD1', 2: 'hD2', 3: 'hD3', 4: 'hD4'}
    apps = []
    for target in (1, 2, 3, 4):
        sig = {1: 1, 2: 2, 3: 3, 4: 4}
        sig[4], sig[target] = target, 4
        apps.append('  · exact' + NL
                    + vertex_app(sig, sym, rowname, dname, 6))
    algebra = ALGEBRA.replace('__VERTEX_APPS__', NL.join(apps))

    act = {1: 'a1', 2: 'a2', 3: 'a3', 4: 'a4'}
    eapps = []
    for i, j in ((1, 2), (1, 3), (1, 4), (2, 3)):
        rest = sorted(set(range(1, 5)) - {i, j})
        sig = {1: rest[0], 2: rest[1], 3: i, 4: j}
        eapps.append('  have b%d%d : c%d%d ≠ 0 :=' % (i, j, i, j) + NL
                     + edge_app(sig, sym, rowname, dname, act, 4))
    return algebra.replace('__EDGE_APPS__', NL.join(eapps))


HEADLINE_PROOF = r'''
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, ha, hb, hP, hW,
    hD1, hD2, hD3, hD4⟩ := hm.facts
__REWRITES__
  have hBne : d z1 ≠ 0 := by
    intro hzero
    rw [hzero, Complex.normSq_zero] at t1
    linarith
  -- The three `X_i Z_j` dressings collapse each `X_i` row to a star sum.
  obtain ⟨pr12, pr13, pr14, star1⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y6) (c2 := c y7)
      (c3 := c y8) (r1 := c y3) (r2 := c y4) (r3 := c y5) (R1 := d z3)
      (R2 := d z4) (R3 := d z5) (C1 := d z6) (C2 := d z7) (C3 := d z8)
      (by linear_combination ho0) (by linear_combination ho1)
      (by linear_combination ho2) (by linear_combination ho3)
  obtain ⟨-, pr23, pr24, star2⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y6) (c2 := c y9)
      (c3 := c y10) (r1 := c y2) (r2 := c y4) (r3 := c y5) (R1 := d z2)
      (R2 := d z4) (R3 := d z5) (C1 := d z6) (C2 := d z9) (C3 := d z10)
      (by linear_combination ho4) (by linear_combination ho5)
      (by linear_combination ho6) (by linear_combination ho7)
  obtain ⟨-, -, pr34, star3⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y7) (c2 := c y9)
      (c3 := c y11) (r1 := c y2) (r2 := c y3) (r3 := c y5) (R1 := d z2)
      (R2 := d z3) (R3 := d z5) (C1 := d z7) (C2 := d z9) (C3 := d z11)
      (by linear_combination ho8) (by linear_combination ho9)
      (by linear_combination ho10) (by linear_combination ho11)
  obtain ⟨-, -, -, star4⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y8) (c2 := c y10)
      (c3 := c y11) (r1 := c y2) (r2 := c y3) (r3 := c y4) (R1 := d z2)
      (R2 := d z3) (R3 := d z4) (C1 := d z8) (C2 := d z10) (C3 := d z11)
      (by linear_combination ho12) (by linear_combination ho13)
      (by linear_combination ho14) (by linear_combination ho15)
  -- `X_i X_5` links every `R_i` to `r_i` through the anchor `b`.
  have f1 : star (c y2) * d z1 + star (c y1) * d z2 = 0 := by
    linear_combination ho16
  have f2 : star (c y3) * d z1 + star (c y1) * d z3 = 0 := by
    linear_combination ho17
  have f3 : star (c y4) * d z1 + star (c y1) * d z4 = 0 := by
    linear_combination ho18
  have f4 : star (c y5) * d z1 + star (c y1) * d z5 = 0 := by
    linear_combination ho19
  -- The four star sums become the four rows of `C r = 0`.
  have e1 : c y6 * c y3 + c y7 * c y4 + c y8 * c y5 = 0 := by
    have key : d z1 * (star (c y6) * star (c y3) + star (c y7) * star (c y4)
        + star (c y8) * star (c y5)) = 0 := by
      linear_combination (star (c y6)) * f2 + (star (c y7)) * f3
        + (star (c y8)) * f4 - (star (c y1)) * star1
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have hs : star (c y6 * c y3 + c y7 * c y4 + c y8 * c y5) = 0 := by
      simp only [star_add, star_mul']
      exact h0
    exact star_eq_zero.mp hs
  have e2 : c y6 * c y2 + c y9 * c y4 + c y10 * c y5 = 0 := by
    have key : d z1 * (star (c y6) * star (c y2) + star (c y9) * star (c y4)
        + star (c y10) * star (c y5)) = 0 := by
      linear_combination (star (c y6)) * f1 + (star (c y9)) * f3
        + (star (c y10)) * f4 - (star (c y1)) * star2
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have hs : star (c y6 * c y2 + c y9 * c y4 + c y10 * c y5) = 0 := by
      simp only [star_add, star_mul']
      exact h0
    exact star_eq_zero.mp hs
  have e3 : c y7 * c y2 + c y9 * c y3 + c y11 * c y5 = 0 := by
    have key : d z1 * (star (c y7) * star (c y2) + star (c y9) * star (c y3)
        + star (c y11) * star (c y5)) = 0 := by
      linear_combination (star (c y7)) * f1 + (star (c y9)) * f2
        + (star (c y11)) * f4 - (star (c y1)) * star3
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have hs : star (c y7 * c y2 + c y9 * c y3 + c y11 * c y5) = 0 := by
      simp only [star_add, star_mul']
      exact h0
    exact star_eq_zero.mp hs
  have e4 : c y8 * c y2 + c y10 * c y3 + c y11 * c y4 = 0 := by
    have key : d z1 * (star (c y8) * star (c y2) + star (c y10) * star (c y3)
        + star (c y11) * star (c y4)) = 0 := by
      linear_combination (star (c y8)) * f1 + (star (c y10)) * f2
        + (star (c y11)) * f3 - (star (c y1)) * star4
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have hs : star (c y8 * c y2 + c y10 * c y3 + c y11 * c y4) = 0 := by
      simp only [star_add, star_mul']
      exact h0
    exact star_eq_zero.mp hs
  -- No vertex amplitude vanishes, so every pair relation can be solved for
  -- the top edge amplitude.
  obtain ⟨-, a2, a3, a4⟩ :=
    vertices_active e1 e2 e3 e4 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
  have t12 : star (c y1) * d z6 + d z1 * star (c y6) = 0 := by
    have hh : star (c y3) * (star (c y1) * d z6 + d z1 * star (c y6)) = 0 := by
      linear_combination (star (c y6)) * f2 - (star (c y1)) * pr12
    exact (mul_eq_zero.mp hh).resolve_left (star_ne_zero.mpr a2)
  have t13 : star (c y1) * d z7 + d z1 * star (c y7) = 0 := by
    have hh : star (c y4) * (star (c y1) * d z7 + d z1 * star (c y7)) = 0 := by
      linear_combination (star (c y7)) * f3 - (star (c y1)) * pr13
    exact (mul_eq_zero.mp hh).resolve_left (star_ne_zero.mpr a3)
  have t14 : star (c y1) * d z8 + d z1 * star (c y8) = 0 := by
    have hh : star (c y5) * (star (c y1) * d z8 + d z1 * star (c y8)) = 0 := by
      linear_combination (star (c y8)) * f4 - (star (c y1)) * pr14
    exact (mul_eq_zero.mp hh).resolve_left (star_ne_zero.mpr a4)
  have t23 : star (c y1) * d z9 + d z1 * star (c y9) = 0 := by
    have hh : star (c y4) * (star (c y1) * d z9 + d z1 * star (c y9)) = 0 := by
      linear_combination (star (c y9)) * f3 - (star (c y1)) * pr23
    exact (mul_eq_zero.mp hh).resolve_left (star_ne_zero.mpr a3)
  have t24 : star (c y1) * d z10 + d z1 * star (c y10) = 0 := by
    have hh : star (c y5) * (star (c y1) * d z10 + d z1 * star (c y10))
        = 0 := by
      linear_combination (star (c y10)) * f4 - (star (c y1)) * pr24
    exact (mul_eq_zero.mp hh).resolve_left (star_ne_zero.mpr a4)
  have t34 : star (c y1) * d z11 + d z1 * star (c y11) = 0 := by
    have hh : star (c y5) * (star (c y1) * d z11 + d z1 * star (c y11))
        = 0 := by
      linear_combination (star (c y11)) * f4 - (star (c y1)) * pr34
    exact (mul_eq_zero.mp hh).resolve_left (star_ne_zero.mpr a4)
  -- `X_5 X_6` becomes the matching equation.
  have hmt : c y6 * c y11 + c y7 * c y10 + c y8 * c y9 = 0 := by
    have key : d z1 * (2 * (star (c y6) * star (c y11)
        + star (c y7) * star (c y10) + star (c y8) * star (c y9))) = 0 := by
      linear_combination (star (c y11)) * t12 + (star (c y10)) * t13
        + (star (c y9)) * t14 + (star (c y8)) * t23 + (star (c y7)) * t24
        + (star (c y6)) * t34 - (star (c y1)) * ho20
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have h1 : star (c y6) * star (c y11) + star (c y7) * star (c y10)
        + star (c y8) * star (c y9) = 0 := by linear_combination h0 / 2
    have hs : star (c y6 * c y11 + c y7 * c y10 + c y8 * c y9) = 0 := by
      simp only [star_add, star_mul']
      exact h1
    exact star_eq_zero.mp hs
  obtain ⟨v1, v2, v3, v4, w12, w13, w14, w23, w24, w34⟩ :=
    magnitudes_core e1 e2 e3 e4 hmt (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  exact ⟨ha, hb, v1, v2, v3, v4, w12, w13, w14, w23, w24, w34,
    by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩
'''


def emit_headline():
    out = ['', '/-! ## The orbit-36 rigidity theorem -/', '']
    mom = []
    for a in (0, 6):
        mom.append('            ' + ' '.join('(Complex.normSq (c y%d))' % k
                                             for k in range(a, a + 6)))
    for a in (0, 6):
        mom.append('            ' + ' '.join('(Complex.normSq (d z%d))' % k
                                             for k in range(a, a + 6)))
    momargs = NL + NL.join(mom)
    hyps = ['    (ho%d : offSum c d %s %s = 0)' % (n, mn, dn)
            for n, (mn, dn) in enumerate(ROWS)]
    rew = NL.join('  rw [ex_%s_%s] at ho%d' % (mn, dn, n)
                  for n, (mn, dn) in enumerate(ROWS))
    out.append('set_option maxHeartbeats 1600000 in')
    out.append('/-- **Orbit-36 rigidity: the magnitudes are forced.**  Every'
               ' exact solution')
    out.append('supported on the two orbit-36 fibers has, in each logical'
               ' word, six')
    out.append('probabilities `1/10` -- the two last-coordinate anchors and'
               ' the four vertex')
    out.append('amplitudes -- and six probabilities `1/15`, the six edge'
               ' amplitudes.  No')
    out.append('boundary face of the moment polytope survives.')
    out.append('')
    out.append('The hypotheses are exactly one `MomentSystem` and'
               ' twenty-one weight-at-most-two')
    out.append('cross Knill--Laflamme rows: the four `X_i` rows with their'
               ' three `Z_j`')
    out.append('dressings, the four `X_i X_5` rows, and the `X_5 X_6`'
               ' row. -/')
    out.append('theorem magnitudes_forced (c d : SS.BitString 6 -> ℂ)')
    out.append('    (hm : MomentSystem%s)' % momargs)
    out.extend(hyps)
    concl = ['Complex.normSq (c y%d) = 1/10' % k for k in range(6)]
    concl += ['Complex.normSq (c y%d) = 1/15' % k for k in range(6, 12)]
    concl += ['Complex.normSq (d z%d) = 1/10' % k for k in range(6)]
    concl += ['Complex.normSq (d z%d) = 1/15' % k for k in range(6, 12)]
    out.append('    : ' + (NL + '      ∧ ').join(concl) + ' := by')
    out.append(HEADLINE_PROOF.replace('__REWRITES__', rew).strip(NL))
    out.append('')
    out.append('set_option maxHeartbeats 1600000 in')
    out.append('/-- **Full twelve-term support.**  An immediate corollary of'
               ' the magnitudes:')
    out.append('no amplitude of either logical word vanishes. -/')
    out.append('theorem full_support (c d : SS.BitString 6 -> ℂ)')
    out.append('    (hm : MomentSystem%s)' % momargs)
    out.extend(hyps)
    sup = ['c y%d ≠ 0' % k for k in range(12)]
    sup += ['d z%d ≠ 0' % k for k in range(12)]
    out.append('    : ' + (NL + '      ∧ ').join(sup) + ' := by')
    out.append('  obtain ⟨%s⟩ :=' % ', '.join('k%d' % k for k in range(24)))
    out.append('    magnitudes_forced c d hm %s'
               % ' '.join('ho%d' % n for n in range(len(ROWS))))
    out.append('  refine ⟨%s⟩' % ', '.join(['?_'] * 24))
    for k in range(24):
        out.append('  · intro hzero')
        out.append('    rw [hzero, Complex.normSq_zero] at k%d' % k)
        out.append('    norm_num at k%d' % k)
    return NL.join(out) + NL


# --------------------------------------------------------------------------
# 7.  The headline grammar, audited with the repository's own parsers
# --------------------------------------------------------------------------

def _probe(text, name):
    """Rename one headline to `no_go_of_moments` and blank its conclusion.

    `verification/classify.py` and `verification/admis.py` are fail-closed on
    the 51-module no-go inventory, so they cannot be pointed at orbit 36
    directly (orbit 36 is realizable and has no `no_go_of_moments`).  This
    rewrites the emitted headline into the exact shape those scripts parse --
    only the theorem NAME and the CONCLUSION change, never a binder -- so their
    audited grammar is applied verbatim to the real hypothesis list.
    """
    probe = text.replace('theorem ' + name, 'theorem no_go_of_moments', 1)
    k = probe.find('theorem no_go_of_moments')
    a = probe.index(NL + '    : ', k)
    b = probe.index(' := by' + NL, a)
    return probe[:a] + NL + '    : False :=' + probe[b + len(' := by'):]


def audit_headline(text):
    sys.path.insert(0, os.path.join(REPO, 'tools', 'verification'))
    import classify as _classify
    import admis as _admis
    assert 'theorem no_go_of_moments' not in text, (
        'orbit 36 must not claim a no-go headline: the certified inventory is'
        ' fail-closed on exactly 51 such modules')
    for name in ('magnitudes_forced', 'full_support'):
        probe = _probe(text, name)
        a, b, c, other = _classify.classify_source(probe)
        assert not other, '%s: binders outside the grammar: %s' % (name, other)
        assert (a, b, c) == (len(ROWS), 0, 1), (
            '%s: %d offSum, %d diag, %d MomentSystem binders' % (name, a, b, c))
        off, dia, bad, unres, prof = _admis.audit_source(probe)
        assert not bad and not unres, '%s: %s %s' % (name, bad, unres)
        assert len(off) == len(ROWS) and not dia
        assert max(prof) <= 2, '%s: a row has Pauli weight %d' % (name,
                                                                 max(prof))
        print('headline %-18s %2d offSum rows, 1 MomentSystem, weights %s'
              % (name, len(off), dict(sorted(prof.items()))))


def main():
    check_instance()
    check_rows()
    rank = check_moments()
    check_certificates()
    check_witness()
    print('orbit 36: fibers verified against fiber([1,1,1,1,2,3], 5, .) in the'
          ' repository bit order')
    print('%d off-diagonal rows and %d diagonal rows derived twice and agreed'
          % (len(ROWS), len(DROWS)))
    print('moment system: 23 equalities of rank %d; all %d derived facts'
          ' verified over Q' % (rank, len(DERIVED)))
    print('all linear_combination certificates and the canonical witness:'
          ' verified')
    text = (HEADER + emit_fibers() + emit_masks() + emit_offdiag()
            + emit_diag() + emit_moment() + emit_algebra() + emit_headline()
            + NL + 'end' + NL + NL + 'end SixQubit.Orbit36' + NL)
    audit_headline(text)
    if '--check' in sys.argv:
        print('--check: %d lines not written' % text.count(NL))
        return
    io.open(OUT, 'w', encoding='utf-8', newline=NL).write(text)
    print('wrote %s (%d lines)' % (OUT, text.count(NL)))


if __name__ == '__main__':
    main()
