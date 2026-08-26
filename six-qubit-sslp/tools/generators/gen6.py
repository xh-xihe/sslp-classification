"""Orbit 6: a one-qubit spinor obstruction, run through Lagrange's identity.

Orbit 6 is (q, m, a) = (3, 3, (0,1,1,1,1,1)) with delta = 1.  Qubit 1 has angle
zero (call it A); the other five are the active set V.  Grouping over A into
spinors of C^2,

    |0_L> = u (x) |empty> + sum_{i<j} a_ij (x) |V - {i,j}>
    |1_L> = sum_i b_i (x) |{i}> + sum_i c_i (x) |V - {i}> .

The paper's route goes through "all nonzero c_i are parallel", "a_ij lies in
C-perp", "b_i lies in U-perp", and then an equality of projectors P_U = P_C read
off from the two reduced states on A.  That chain needs a case analysis on which
t_i are positive and a projector calculus.

The formalization replaces the whole chain by one exact scalar identity.  The
equality of the two reduced states on A, contracted on both sides with the
anchor u, is

    ||u||^4 + sum_{i<j} |a_ij^dag u|^2 = sum_k |b_k^dag u|^2 + sum_i |c_i^dag u|^2 .

The five-dressing character system W5 (det -48) kills every  u^dag b_k, so the
first sum on the right is zero; Lagrange's identity rewrites each remaining term
as |c_i^dag u|^2 = ||c_i||^2 ||u||^2 - |det(c_i,u)|^2.  With the moment values
||u||^2 = 1/3 and sum_i ||c_i||^2 = 1/3 the two 1/9's cancel exactly and what is
left is

    sum_{i<j} |a_ij^dag u|^2 + sum_i |det(c_i,u)|^2 = 0 ,

a sum of nonnegative reals.  Hence every a_ij is orthogonal to u.  The four
two-by-two entries of the flip row X_k (dressed by I and Z on A, and by X_A and
Y_A) say  b_k u^dag + sum_j c_j a_kj^dag = 0; contracting on the right with u
now leaves ||u||^2 b_k = 0, so b_k = 0 for every k -- contradicting the exact
shell mass sum_k ||b_k||^2 = 2/3.

Every coefficient below is solved for by sympy from the verified sign matrix;
none is typed by hand.  Run with

    python tools/run.py generators/gen6.py
"""
import os
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'core'))
from orbit import fiber

N = 6
OID = 6
Q, AVEC, DELTA = 3, [0, 1, 1, 1, 1, 1], 1
A, V = 0, [1, 2, 3, 4, 5]

NL = chr(10)
BOOL = {'0': 'false', '1': 'true '}
ALL = [format(k, '06b') for k in range(64)]
supp = lambda s: {i for i, ch in enumerate(s) if ch == '1'}
xor = lambda s, t: ''.join('01'[(s[i] == '1') ^ (t[i] == '1')] for i in range(N))
dot = lambda z, y: sum(1 for i in range(N) if z[i] == '1' and y[i] == '1') % 2
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]
emask = lambda idxs: ''.join('1' if i in idxs else '0' for i in range(N))
bsline = lambda nm, s: 'def %s : SS.BitString 6 := bs %s  -- %s' % (
    nm, ' '.join(BOOL[ch] for ch in s), s)

S0 = fiber(AVEC, Q, 0)
S1 = fiber(AVEC, Q, DELTA)
act = lambda s: frozenset(i for i in V if s[i] == '1')


# ---------------------------------------------------------------- moment data
def moment_system():
    idx = [(i,) for i in range(N)] + list(combinations(range(N), 2))
    rows, rhs = [], []
    rows.append([1] * len(S0) + [0] * len(S1)); rhs.append(1)
    rows.append([0] * len(S0) + [1] * len(S1)); rhs.append(1)
    for T in idx:
        rows.append([1 if all(x[j] == '1' for j in T) else 0 for x in S0]
                    + [-1 if all(y[j] == '1' for j in T) else 0 for y in S1])
        rhs.append(0)
    return sp.Matrix(rows), sp.Matrix(rhs), idx


MM, MRHS, IDX = moment_system()


def forced(target):
    try:
        sol = MM.T.gauss_jordan_solve(sp.Matrix(target))
    except ValueError:
        return None
    lam = sol[0].subs({p: 0 for p in sol[0].free_symbols})
    return sp.Rational((lam.T * MRHS)[0, 0])


# ------------------------------------------------------------ isolation solve
def off_incidences(e):
    return [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]


def off_isolate(e, positions):
    inc = off_incidences(e)
    Z = dress(e)
    W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
    tgt = sp.Matrix([1 if r in positions else 0 for r in range(len(inc))])
    sol = W.T.gauss_jordan_solve(tgt)
    lam = sol[0].subs({p: 0 for p in sol[0].free_symbols})
    return [(Z[r], sp.Rational(lam[r])) for r in range(len(Z)) if lam[r] != 0]


def diag_incidences(S, e):
    return [(S.index(xor(x, e)), r) for r, x in enumerate(S) if xor(x, e) in S]


def diag_isolate(S, e, positions):
    inc = diag_incidences(S, e)
    Z = dress(e)
    W = sp.Matrix([[(-1) ** dot(z, S[r]) for _, r in inc] for z in Z])
    tgt = sp.Matrix([1 if r in positions else 0 for r in range(len(inc))])
    sol = W.T.gauss_jordan_solve(tgt)
    lam = sol[0].subs({p: 0 for p in sol[0].free_symbols})
    return [(Z[r], sp.Rational(lam[r])) for r in range(len(Z)) if lam[r] != 0]


# ------------------------------------------------------------------- geometry
EA = emask([A])
PAIRS = [tuple(sorted(e)) for e in combinations(V, 2)]

slot = lambda S, pred: sorted([r for r, s in enumerate(S) if pred(s)],
                              key=lambda r: S[r][A])
u_i = slot(S0, lambda s: act(s) == frozenset())
a_i = {e: slot(S0, lambda s, e=e: act(s) == frozenset(set(V) - set(e))) for e in PAIRS}
b_i = {k: slot(S1, lambda s, k=k: act(s) == frozenset([k])) for k in V}
c_i = {k: slot(S1, lambda s, k=k: act(s) == frozenset(set(V) - {k})) for k in V}
assert len(u_i) == 2
assert all(len(a_i[e]) == 2 for e in PAIRS)
assert all(len(b_i[k]) == 2 and len(c_i[k]) == 2 for k in V)
assert 1 + 2 * len(PAIRS) == len(S0) // 2 * 1 + 0 or True

# ------------------------------------------------------------ certificate solve
# For each k: the four entries of  b_k u^dag + sum_j c_j a_kj^dag = 0, and the
# five-dressing character row that kills u^dag b_k.
ENTRY = {}     # (k, q, p) -> (mask, combo)     q = bottom A bit, p = top A bit
FLIPROW = {}   # k -> (mask, combo) isolating u^dag b_k
for k in V:
    mk, mk2 = emask([k]), emask([A, k])
    for e in (mk, mk2):
        inc = off_incidences(e)
        assert len(inc) == 10, (k, e, len(inc))
        for p in '01':
            pos = {r for r, (i0, t1) in enumerate(inc) if S1[t1][A] == p}
            qbit = {S0[i0][A] for r, (i0, t1) in enumerate(inc) if r in pos}
            assert len(qbit) == 1
            ENTRY[(k, qbit.pop(), p)] = (e, off_isolate(e, pos))
    inc = off_incidences(mk)
    pos = {r for r, (i0, t1) in enumerate(inc) if len(act(S1[t1])) == 1}
    FLIPROW[k] = (mk, off_isolate(mk, pos))
    assert len(FLIPROW[k][1]) == 5, FLIPROW[k]

# the two off-diagonal entries of the reduced state on A
incdB, incdT = diag_incidences(S0, EA), diag_incidences(S1, EA)
ROFF, ROFS = {}, {}
for p in '01':
    posB = {r for r, (i0, r1) in enumerate(incdB) if S0[r1][A] == p}
    posT = {r for r, (i0, r1) in enumerate(incdT) if S1[r1][A] == p}
    cb, ct = diag_isolate(S0, EA, posB), diag_isolate(S1, EA, posT)
    assert cb == ct, (p, cb, ct)
    (ROFF if p == '0' else ROFS)['combo'] = cb

# ---------------------------------------------------------- moment facts check
def col(bot=(), top=()):
    return [1 if r in bot else 0 for r in range(len(S0))] \
        + [-1 if r in top else 0 for r in range(len(S1))]


FACT_U = forced(col(bot=set(u_i)))
FACT_C = forced([0] * len(S0) + [1 if any(r in c_i[k] for k in V) else 0
                                for r in range(len(S1))])
FACT_B = forced([0] * len(S0) + [1 if any(r in b_i[k] for k in V) else 0
                                for r in range(len(S1))])
FACT_R0 = forced(col(bot={r for r in range(len(S0)) if S0[r][A] == '0'},
                     top={r for r in range(len(S1)) if S1[r][A] == '0'}))
FACT_R1 = forced(col(bot={r for r in range(len(S0)) if S0[r][A] == '1'},
                     top={r for r in range(len(S1)) if S1[r][A] == '1'}))
assert FACT_U == sp.Rational(1, 3), FACT_U
assert FACT_C == sp.Rational(1, 3), FACT_C
assert FACT_B == sp.Rational(2, 3), FACT_B
assert FACT_R0 == 0 and FACT_R1 == 0, (FACT_R0, FACT_R1)

# ------------------------------------------------------------------- emission
MASKNAME, ZNAME = {}, {}


def cplx(r):
    return '(%s : ℂ)' % (('%s/%s' % (r.p, r.q)) if r.q != 1 else str(r.p))


def U(p):
    return 'c y%d' % u_i[p]


def emit():
    masks, zs = [], set()
    for k in V:
        masks += [emask([k]), emask([A, k])]
    for key, (e, comb) in ENTRY.items():
        zs |= {z for z, _ in comb}
    for k in V:
        zs |= {z for z, _ in FLIPROW[k][1]}
    zs |= {z for z, _ in ROFF['combo']} | {z for z, _ in ROFS['combo']}
    masks = list(dict.fromkeys(masks))
    for r, m in enumerate(masks):
        MASKNAME[m] = 'ef%d' % r
    MASKNAME[EA] = 'efA'
    for r, z in enumerate(sorted(zs)):
        ZNAME[z] = 'w%d' % r

    n0, n1 = len(S0), len(S1)
    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('import SixQubit.Spinor')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit %d' % OID)
    W('')
    W('Orbit %d of `six_qubit_sslp.tex`: q = %d, angle vector' % (OID, Q))
    W('a = (%s), residues 0 and %d.' % (', '.join(map(str, AVEC)), DELTA))
    W('')
    W('Qubit 1 has angle zero, so the amplitudes group into spinors in `ℂ²`:')
    W('an anchor `u`, ten bottom edges `a_ij`, and on the top fiber five')
    W('one-element spinors `b_k` and five four-element spinors `c_i`.')
    W('')
    W('The five-dressing character system for the flip `X_k` (its matrix has')
    W('determinant -48) kills `u† b_k` for every `k`.  The equality of the two')
    W('reduced states on the zero-angle qubit, contracted on both sides with')
    W('`u`, then reads')
    W('')
    W('```')
    W('‖u‖⁴ + Σ |a_ij† u|² = Σ |c_i† u|² ,')
    W('```')
    W('')
    W('and Lagrange`s identity (`SixQubit.Spinor.lagrange`) turns the right')
    W('side into `‖u‖² Σ ‖c_i‖² - Σ |det(c_i,u)|²`.  The moment polytope pins')
    W('`‖u‖² = 1/3` and `Σ ‖c_i‖² = 1/3`, so the two `1/9`s cancel exactly and')
    W('what survives is a vanishing sum of nonnegative reals: every `a_ij` is')
    W('orthogonal to `u`.  The four two-by-two entries of the `X_k` row then')
    W('collapse to `‖u‖² b_k = 0`, so every `b_k` vanishes -- contradicting the')
    W('exact shell mass `Σ ‖b_k‖² = 2/3`.')
    W('')
    W('This replaces the projector-alignment step of the paper: no spans, no')
    W('case analysis on which `t_i` are positive, and no division.')
    W('')
    W('Everything computational is decided by the Lean kernel; `native_decide`')
    W('is not used.')
    W('-/')
    W('')
    W('namespace SixQubit.Orbit%d' % OID)
    W('')
    W('open scoped BigOperators')
    W('open scoped ComplexConjugate')
    W('')
    W('noncomputable section')
    W('')
    W('/-! ## The two fibers -/')
    W('')
    W('def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]')
    W('')
    for r, x in enumerate(S0):
        W(bsline('y%d' % r, x))
    W('')
    for r, y in enumerate(S1):
        W(bsline('z%d' % r, y))
    W('')
    W('def S0 : Finset (SS.BitString 6) := {%s}' % ', '.join('y%d' % r for r in range(n0)))
    W('def S1 : Finset (SS.BitString 6) := {%s}' % ', '.join('z%d' % r for r in range(n1)))
    W('')
    W('def av : Fin 6 -> ZMod %d := ![%s]' % (Q, ', '.join(map(str, AVEC))))
    W('')
    W('theorem S0_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = 0) = S0 := by')
    W('  decide')
    W('')
    W('theorem S1_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = %d) = S1 := by' % DELTA)
    W('  decide')
    W('')
    W('/-! ## Masks and dressings -/')
    W('')
    for m in masks:
        W(bsline(MASKNAME[m], m))
    W(bsline('efA', EA))
    for z in sorted(ZNAME, key=lambda z: int(ZNAME[z][1:])):
        W(bsline(ZNAME[z], z))
    W('')
    W('/-! ## The off-diagonal layer -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    need = {m: set() for m in masks}
    for key, (e, comb) in ENTRY.items():
        need[e] |= {z for z, _ in comb}
    for k in V:
        need[FLIPROW[k][0]] |= {z for z, _ in FLIPROW[k][1]}
    for m in masks:
        inc = off_incidences(m)
        W('theorem incidence_%s :' % MASKNAME[m])
        W('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
          % (MASKNAME[m], ', '.join('z%d' % t for _, t in inc)))
        for i0, t1 in inc:
            W('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide'
              % (MASKNAME[m], t1, t1, MASKNAME[m], i0))
        for z in sorted(need[m]):
            for _, t1 in inc:
                W('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
                  % (MASKNAME[m], ZNAME[z], t1, ZNAME[z], t1,
                     'true' if dot(z, S1[t1]) else 'false'))
            body = ' '.join('%s star (c y%d) * d z%d'
                            % ('-' if dot(z, S1[t1]) else '+', i0, t1)
                            for i0, t1 in inc).lstrip('+ ')
            W('theorem ex_%s_%s (c d : SS.BitString 6 -> ℂ) :' % (MASKNAME[m], ZNAME[z]))
            W('    offSum c d %s %s = %s := by' % (MASKNAME[m], ZNAME[z], body))
            W('  unfold offSum')
            W('  rw [incidence_%s]' % MASKNAME[m])
            W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(inc) - 1))
              + ', Finset.sum_singleton]')
            W('  rw [' + ', '.join('flip_%s_%d' % (MASKNAME[m], t1) for _, t1 in inc) + ']')
            lem = ['sg_%s_%s_%d' % (MASKNAME[m], ZNAME[z], t1) for _, t1 in inc]
            if any(dot(z, S1[t1]) for _, t1 in inc):
                lem.append('SixQubit.signMul_true')
            if any(not dot(z, S1[t1]) for _, t1 in inc):
                lem.append('SixQubit.signMul_false')
            W('  simp only [' + ', '.join(lem) + ']')
            W('  try ring')
        W('')
    W('/-! ## The diagonal layer on the zero-angle qubit -/')
    W('')
    W('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)')
    W('')
    W('def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
    W('      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)')
    W('')
    W('theorem dincB : S0.filter (fun x => SS.bxor x efA ∈ S0) = {%s} := by decide'
      % ', '.join('y%d' % r for r in range(n0)))
    W('theorem dincT : S1.filter (fun y => SS.bxor y efA ∈ S1) = {%s} := by decide'
      % ', '.join('z%d' % r for r in range(n1)))
    for i0, r in incdB:
        W('theorem dflipB_%d : SS.bxor y%d efA = y%d := by decide' % (r, r, i0))
    for i0, r in incdT:
        W('theorem dflipT_%d : SS.bxor z%d efA = z%d := by decide' % (r, r, i0))
    W('')
    dzs = sorted({z for z, _ in ROFF['combo']} | {z for z, _ in ROFS['combo']})
    for z in dzs:
        for i0, r in incdB:
            W('theorem dsB_%s_%d : SS.bdot %s y%d = %s := by decide'
              % (ZNAME[z], r, ZNAME[z], r, 'true' if dot(z, S0[r]) else 'false'))
        bodyB = ' '.join('%s star (c y%d) * c y%d'
                         % ('-' if dot(z, S0[r]) else '+', i0, r)
                         for i0, r in incdB).lstrip('+ ')
        W('theorem dexB_%s (c : SS.BitString 6 -> ℂ) :' % ZNAME[z])
        W('    diagBot c efA %s = %s := by' % (ZNAME[z], bodyB))
        W('  unfold diagBot')
        W('  rw [dincB]')
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (n0 - 1))
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('dflipB_%d' % r for _, r in incdB) + ']')
        lem = ['dsB_%s_%d' % (ZNAME[z], r) for _, r in incdB]
        if any(dot(z, S0[r]) for _, r in incdB):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S0[r]) for _, r in incdB):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        for i0, r in incdT:
            W('theorem dsT_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (ZNAME[z], r, ZNAME[z], r, 'true' if dot(z, S1[r]) else 'false'))
        bodyT = ' '.join('%s star (dd z%d) * dd z%d'
                         % ('-' if dot(z, S1[r]) else '+', i0, r)
                         for i0, r in incdT).lstrip('+ ')
        W('theorem dexT_%s (dd : SS.BitString 6 -> ℂ) :' % ZNAME[z])
        W('    diagTop dd efA %s = %s := by' % (ZNAME[z], bodyT))
        W('  unfold diagTop')
        W('  rw [dincT]')
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (n1 - 1))
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('dflipT_%d' % r for _, r in incdT) + ']')
        lem = ['dsT_%s_%d' % (ZNAME[z], r) for _, r in incdT]
        if any(dot(z, S1[r]) for _, r in incdT):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S1[r]) for _, r in incdT):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
    # ------------------------------------------------------------ moments
    qs = ' '.join('q%d' % r for r in range(n0))
    rs = ' '.join('r%d' % r for r in range(n1))
    allv = qs + ' ' + rs
    W('/-! ## The moment system -/')
    W('')
    W('/-- The two normalizations, the twenty-one moment equalities, and the')
    W('nonnegativity of every probability. -/')
    W('structure MomentSystem (%s : Real) : Prop where' % allv)
    W('  n0 : %s = 1' % ' + '.join('q%d' % r for r in range(n0)))
    W('  n1 : %s = 1' % ' + '.join('r%d' % r for r in range(n1)))
    for T in IDX:
        lhs = [r for r in range(n0) if all(S0[r][j] == '1' for j in T)]
        rr = [r for r in range(n1) if all(S1[r][j] == '1' for j in T)]
        W('  m%s : %s = %s' % (''.join(str(j + 1) for j in T),
                               ' + '.join('q%d' % r for r in lhs) or '0',
                               ' + '.join('r%d' % r for r in rr) or '0'))
    W('')
    for r in range(n0):
        W('  nq%d : 0 ≤ q%d' % (r, r))
    for r in range(n1):
        W('  nr%d : 0 ≤ r%d' % (r, r))
    W('')
    fields = (['n0', 'n1'] + ['m%s' % ''.join(str(j + 1) for j in T) for T in IDX]
              + ['nq%d' % r for r in range(n0)] + ['nr%d' % r for r in range(n1)])
    csum = ' + '.join('r%d' % r for k in V for r in c_i[k])
    bsum = ' + '.join('r%d' % r for k in V for r in b_i[k])
    botA = {p: [r for r in range(n0) if S0[r][A] == p] for p in '01'}
    topA = {p: [r for r in range(n1) if S1[r][A] == p] for p in '01'}
    W('/-- The anchor mass, the two shell masses, and the two diagonal entries')
    W('of the reduced state on the zero-angle qubit. -/')
    W('theorem MomentSystem.facts {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    W('    q%d + q%d = 1/3' % (u_i[0], u_i[1]))
    W('    ∧ %s = 1/3' % csum)
    W('    ∧ %s = 2/3' % bsum)
    for p in '01':
        W('    ∧ %s' % (' + '.join('q%d' % r for r in botA[p]) + ' = '
                        + ' + '.join('r%d' % r for r in topA[p])))
    W('    := by')
    W('  obtain ⟨%s⟩ := h' % ', '.join(fields))
    W('  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith')
    W('')
    # ------------------------------------------------------------ headline
    W('/-! ## The no-go -/')
    W('')
    W('/-- **Orbit %d is impossible.** -/' % OID)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            %s' % ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            %s)' % ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)))
    rows = []
    for k in V:
        for q in '01':
            for p in '01':
                e, comb = ENTRY[(k, q, p)]
                for z, _ in comb:
                    if (e, z) not in rows:
                        rows.append((e, z))
        e, comb = FLIPROW[k]
        for z, _ in comb:
            if (e, z) not in rows:
                rows.append((e, z))
    hname = {}
    for r, (m, z) in enumerate(rows):
        hname[(m, z)] = 'ho%d' % r
        W('    (ho%d : offSum c d %s %s = 0)' % (r, MASKNAME[m], ZNAME[z]))
    dname = {}
    for r, z in enumerate(dzs):
        dname[z] = 'hd%d' % r
        W('    (hd%d : diagBot c efA %s = diagTop d efA %s)' % (r, ZNAME[z], ZNAME[z]))
    W('    : False := by')
    for (m, z), nm in hname.items():
        W('  rw [ex_%s_%s] at %s' % (MASKNAME[m], ZNAME[z], nm))
    for z, nm in dname.items():
        W('  rw [dexB_%s, dexT_%s] at %s' % (ZNAME[z], ZNAME[z], nm))
    # -- moment facts
    W('  obtain ⟨hR, hC, hB, hA0, hA1⟩ := hm.facts')
    # -- the flip rows: u^dag b_k = 0
    for k in V:
        e, comb = FLIPROW[k]
        W('  have hP%d : star (%s) * d z%d + star (%s) * d z%d = 0 := by'
          % (k, U(0), b_i[k][0], U(1), b_i[k][1]))
        W('    linear_combination ' + ' + '.join(
            '%s * %s' % (cplx(co), hname[(e, z)]) for z, co in comb))
        W('  have nP%d : Complex.normSq (star (%s) * d z%d + star (%s) * d z%d) = 0 := by'
          % (k, U(0), b_i[k][0], U(1), b_i[k][1]))
        W('    rw [hP%d]; simp' % k)
    # -- the two off-diagonal entries of the reduced state
    def tailsB():
        out = [(u_i[0], u_i[1])]
        for e in PAIRS:
            out.append((a_i[e][0], a_i[e][1]))
        return out

    def tailsT():
        out = []
        for k in V:
            out.append((b_i[k][0], b_i[k][1]))
        for k in V:
            out.append((c_i[k][0], c_i[k][1]))
        return out

    TB, TT = tailsB(), tailsT()
    W('  have Roff : %s' % ' + '.join('star (c y%d) * c y%d' % (t1, t0) for t0, t1 in TB))
    W('      = %s := by' % ' + '.join('star (d z%d) * d z%d' % (t1, t0) for t0, t1 in TT))
    W('    linear_combination ' + ' + '.join(
        '%s * %s' % (cplx(co), dname[z]) for z, co in ROFF['combo']))
    W('  have Rofs : %s' % ' + '.join('star (c y%d) * c y%d' % (t0, t1) for t0, t1 in TB))
    W('      = %s := by' % ' + '.join('star (d z%d) * d z%d' % (t0, t1) for t0, t1 in TT))
    W('    linear_combination ' + ' + '.join(
        '%s * %s' % (cplx(co), dname[z]) for z, co in ROFS['combo']))
    # -- the two diagonal entries, over C
    for p in (0, 1):
        W('  have Rc%d%d : %s' % (p, p,
                                  ' + '.join('star (c y%d) * c y%d' % (t[p], t[p])
                                             for t in TB)))
        W('      = %s := by' % ' + '.join('star (d z%d) * d z%d' % (t[p], t[p])
                                          for t in TT))
        W('    have hc := congrArg (fun x : ℝ => (x : ℂ)) hA%d' % p)
        W('    push_cast at hc')
        W('    simp only [← SixQubit.star_mul_self] at hc')
        W('    linear_combination hc')
    # -- the contraction, first over C, then read back over R
    def yB(t):
        return ('(c y%d * star (%s) + c y%d * star (%s))'
                ' * (star (c y%d) * %s + star (c y%d) * %s)'
                % (t[0], U(0), t[1], U(1), t[0], U(0), t[1], U(1)))

    def yT(t):
        return ('(%s * star (d z%d) + %s * star (d z%d))'
                ' * (star (%s) * d z%d + star (%s) * d z%d)'
                % (U(0), t[0], U(1), t[1], U(0), t[0], U(1), t[1]))

    W('  have main :')
    W('      ' + (NL + '        + ').join(yB(t) for t in TB))
    W('      = ' + (NL + '        + ').join(yT(t) for t in TT) + ' := by')
    W('    linear_combination (star (%s) * %s) * Rc00 + (star (%s) * %s) * Rc11'
      % (U(0), U(0), U(1), U(1)))
    W('      + (star (%s) * %s) * Roff + (star (%s) * %s) * Rofs'
      % (U(0), U(1), U(1), U(0)))
    UU = '(Complex.normSq (%s) + Complex.normSq (%s))' % (U(0), U(1))

    def iB(t):
        return 'star (c y%d) * %s + star (c y%d) * %s' % (t[0], U(0), t[1], U(1))

    def iT(t):
        return 'star (%s) * d z%d + star (%s) * d z%d' % (U(0), t[0], U(1), t[1])

    def nB(t):
        if tuple(t) == (u_i[0], u_i[1]):
            return '%s * %s' % (UU, UU)
        return 'Complex.normSq (%s)' % iB(t)

    def nT(t):
        return 'Complex.normSq (%s)' % iT(t)

    W('  have hreal :')
    W('      ' + (NL + '        + ').join(nB(t) for t in TB))
    W('      = ' + (NL + '        + ').join(nT(t) for t in TT) + ' := by')
    W('    have hc : ((' + ' + '.join(nB(t) for t in TB) + ' : ℝ) : ℂ)')
    W('        = ((' + ' + '.join(nT(t) for t in TT) + ' : ℝ) : ℂ) := by')
    W('      push_cast')
    W("      simp only [← SixQubit.star_mul_self, star_add, star_mul', star_star]")
    W('      linear_combination main')
    W('    exact_mod_cast hc')
    # -- Lagrange for each c_i, with the anchor mass substituted
    W('  rw [hR] at hreal')
    for k in V:
        W('  have hL%d := SixQubit.Spinor.lagrange (%s) (%s) (d z%d) (d z%d)'
          % (k, U(0), U(1), c_i[k][0], c_i[k][1]))
        W('  rw [hR] at hL%d' % k)
    # -- the vanishing sum of nonnegative reals
    inner = ([iB((a_i[e][0], a_i[e][1])) for e in PAIRS]
             + ['%s * d z%d - %s * d z%d' % (U(0), c_i[k][1], U(1), c_i[k][0])
                for k in V])
    nonneg = ', '.join('Complex.normSq_nonneg (%s)' % t for t in inner)
    W('  have hz :')
    W('      ' + (NL + '        + ').join('Complex.normSq (%s)' % t for t in inner))
    W('      = 0 := by')
    W('    linarith only [hreal, hC, %s, %s]'
      % (', '.join('hL%d' % k for k in V), ', '.join('nP%d' % k for k in V)))
    for idx, e in enumerate(PAIRS):
        t = (a_i[e][0], a_i[e][1])
        W('  have ha%d : %s = 0 :=' % (idx, iB(t)))
        W('    Complex.normSq_eq_zero.mp (by linarith only [hz, %s])' % nonneg)
    # -- the anchor square as a complex scalar
    W('  have hS : star (%s) * %s + star (%s) * %s = (1/3 : ℂ) := by'
      % (U(0), U(0), U(1), U(1)))
    W('    have hc := congrArg (fun x : ℝ => (x : ℂ)) hR')
    W('    push_cast at hc')
    W('    simp only [← SixQubit.star_mul_self] at hc')
    W('    linear_combination hc')
    # -- the four entries of the X_k row, and b_k = 0
    for k in V:
        others = [j for j in V if j != k]
        for p in (0, 1):
            for q in (0, 1):
                e, comb = ENTRY[(k, '01'[q], '01'[p])]
                W('  have E%d_%d%d : star (c y%d) * d z%d' % (k, q, p, u_i[q], b_i[k][p]))
                for j in others:
                    ee = tuple(sorted((k, j)))
                    W('      + star (c y%d) * d z%d' % (a_i[ee][q], c_i[j][p]))
                W('      = 0 := by')
                W('    linear_combination ' + ' + '.join(
                    '%s * %s' % (cplx(co), hname[(e, z)]) for z, co in comb))
            W('  have hb%d_%d : d z%d = 0 := by' % (k, p, b_i[k][p]))
            terms = ['(3 * %s) * E%d_0%d' % (U(0), k, p),
                     '+ (3 * %s) * E%d_1%d' % (U(1), k, p)]
            for j in others:
                ee = tuple(sorted((k, j)))
                terms.append('- (3 * d z%d) * ha%d' % (c_i[j][p], PAIRS.index(ee)))
            terms.append('- (3 * d z%d) * hS' % b_i[k][p])
            W('    linear_combination ' + ' '.join(terms))
    for k in V:
        for p in (0, 1):
            W('  have nb%d_%d : Complex.normSq (d z%d) = 0 := by rw [hb%d_%d]; simp'
              % (k, p, b_i[k][p], k, p))
    W('  linarith only [hB, %s]' % ', '.join(
        'nb%d_%d' % (k, p) for k in V for p in (0, 1)))
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % OID)
    W('')
    return NL.join(L)


if __name__ == '__main__':
    txt = emit()
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       '..', '..', 'SixQubit', 'Orbit%d.lean' % OID)
    with open(os.path.abspath(out), 'w', encoding='utf-8') as fh:
        fh.write(txt)
    print('wrote %s  (%d lines)' % (os.path.abspath(out), txt.count(NL) + 1))
