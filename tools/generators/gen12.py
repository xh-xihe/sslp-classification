"""Orbit 12: a zero-angle spinor and a cancelling pair of rank-one matrices.

Orbit 12 is (q, m, a) = (4, 2, (0,1,1,1,1,2)) with delta = 2.  Qubit 1 has angle
zero (call it A), qubits 2-5 carry angle one (call them V), qubit 6 carries angle
two (call it H).  Grouping the amplitudes over A into spinors of C^2, the two
fibers read

    |0_L> = u (x) |empty,0> + v (x) |V,0> + sum_e a_e (x) |e,1>
    |1_L> = ut (x) |empty,1> + vt (x) |V,1> + sum_e b_e (x) |e,0>

with e running over the six two-element subsets of V.

Prior work found only two isolable C^2 inner products for this orbit, so the
block-frame route of `gen13.py` does not apply.  What this generator emits
instead is the rank-one cancellation certificate:

  * the four scalar entries of the cross block  ut u^dag + vt v^dag = 0,
    isolated from the flip masks X_H and X_A X_H (four dressings each);
  * for each complementary pair {e, ebar} of edges, the two physical-pair rows
        a_e^dag ut + v^dag b_ebar = 0 ,   u^dag b_ebar + a_e^dag vt = 0 ,
    isolated from the weight-two flip masks X_e and X_ebar (two dressings each);
  * the off-diagonal entry of the H = 0 block of the reduced state on the pair
    A H, isolated from the four free-qubit diagonal rows for X_A.

`SixQubit.Spinor.cancel_perp` turns the first two groups into  u^dag b_ebar = 0
and  v^dag b_ebar = 0, and `SixQubit.Spinor.edge_zero` turns those plus the
third group into  ||b_ebar||^2 = 0, contradicting the moment polytope, which
forces the three complementary pair masses to sum to 1/4.

Every coefficient below is solved for by sympy from the verified sign matrix;
none is typed by hand.  Run with

    python tools/run.py generators/gen12.py
"""
import os
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'core'))
from orbit import fiber

N = 6
OID = 12
Q, AVEC, DELTA = 4, [0, 1, 1, 1, 1, 2], 2
A, H, V = 0, 5, [1, 2, 3, 4]

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
vp = lambda s: ''.join(s[i] for i in V)


def kind(s):
    """('anchor0'|'anchor4'|'edge', vpart, H bit, A bit)"""
    p = vp(s)
    k = {'0000': 'anchor0', '1111': 'anchor4'}.get(p, 'edge')
    return k, p, s[H], s[A]


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
    """rational value of `target . (q,r)` forced by the moment system, or None"""
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
EH, EAH, EA = emask([H]), emask([A, H]), emask([A])
PAIRS = [tuple(sorted(e)) for e in combinations(V, 2)]
COMP = {e: tuple(sorted(set(V) - set(e))) for e in PAIRS}
# the three complementary pair classes, each represented by its smaller member
CLASSES = []
for e in PAIRS:
    if e < COMP[e] and all(e not in (x, COMP[x]) for x, _ in CLASSES):
        CLASSES.append((e, COMP[e]))

# named amplitude slots
u_i = [S0.index(s) for s in S0 if kind(s)[0] == 'anchor0' and s[H] == '0']
v_i = [S0.index(s) for s in S0 if kind(s)[0] == 'anchor4' and s[H] == '0']
ut_i = [S1.index(s) for s in S1 if kind(s)[0] == 'anchor0' and s[H] == '1']
vt_i = [S1.index(s) for s in S1 if kind(s)[0] == 'anchor4' and s[H] == '1']
u_i.sort(key=lambda r: S0[r][A]); v_i.sort(key=lambda r: S0[r][A])
ut_i.sort(key=lambda r: S1[r][A]); vt_i.sort(key=lambda r: S1[r][A])
a_i = {e: sorted([S0.index(s) for s in S0
                  if kind(s)[0] == 'edge' and s[H] == '1'
                  and {i for i in V if s[i] == '1'} == set(e)],
                 key=lambda r: S0[r][A]) for e in PAIRS}
b_i = {e: sorted([S1.index(s) for s in S1
                  if kind(s)[0] == 'edge' and s[H] == '0'
                  and {i for i in V if s[i] == '1'} == set(e)],
                 key=lambda r: S1[r][A]) for e in PAIRS}

assert len(u_i) == len(v_i) == len(ut_i) == len(vt_i) == 2
assert all(len(a_i[e]) == 2 and len(b_i[e]) == 2 for e in PAIRS)

# ------------------------------------------------------------ certificate solve
# the four cross-block entries K[q][p] = conj(u_q) ut_p + conj(v_q) vt_p
K = {}
for e, tag in ((EH, 'same'), (EAH, 'flip')):
    inc = off_incidences(e)
    for p in '01':
        pos = {r for r, (i0, t1) in enumerate(inc)
               if S1[t1][H] == '1' and S1[t1][A] == p}
        # which bottom A bit does this class carry?
        qbit = {S0[i0][A] for r, (i0, t1) in enumerate(inc) if r in pos}
        assert len(qbit) == 1
        K[(qbit.pop(), p)] = (e, off_isolate(e, pos), sorted(pos))

# the two pair rows for each complementary class
PAIRROW = {}
for e, eb in CLASSES:
    me, mb = emask(e), emask(eb)
    ince, incb = off_incidences(me), off_incidences(mb)
    # P1 from mask e: a_e^dag ut + v^dag b_eb
    p1 = {r for r, (i0, t1) in enumerate(ince)
          if (S1[t1][H] == '1' and kind(S1[t1])[0] == 'anchor0')
          or (S1[t1][H] == '0' and kind(S0[i0])[0] == 'anchor4')}
    # P2 from mask eb: u^dag b_eb + a_e^dag vt
    p2 = {r for r, (i0, t1) in enumerate(incb)
          if (S1[t1][H] == '0' and kind(S0[i0])[0] == 'anchor0')
          or (S1[t1][H] == '1' and kind(S1[t1])[0] == 'anchor4')}
    PAIRROW[(e, eb)] = ((me, off_isolate(me, p1)), (mb, off_isolate(mb, p2)))

# the off-diagonal entry of the H = 0 block, from the free-qubit diagonal rows
incdB, incdT = diag_incidences(S0, EA), diag_incidences(S1, EA)
posB = {r for r, (i0, r1) in enumerate(incdB) if S0[r1][A] == '0' and S0[r1][H] == '0'}
posT = {r for r, (i0, r1) in enumerate(incdT) if S1[r1][A] == '0' and S1[r1][H] == '0'}
DIAGB, DIAGT = diag_isolate(S0, EA, posB), diag_isolate(S1, EA, posT)
assert DIAGB == DIAGT, 'bottom and top isolation combos must agree'

# ---------------------------------------------------------- moment facts check
def col(bot=(), top=()):
    return [1 if r in bot else 0 for r in range(len(S0))] \
        + [-1 if r in top else 0 for r in range(len(S1))]


FACT_U = forced(col(bot=set(u_i)))
FACT_V = forced(col(bot=set(v_i)))
FACT_D0 = forced(col(bot={u_i[0], v_i[0]}, top={b_i[e][0] for e in PAIRS}))
FACT_D1 = forced(col(bot={u_i[1], v_i[1]}, top={b_i[e][1] for e in PAIRS}))
tri = set()
for _, eb in CLASSES:
    tri |= set(b_i[eb])
FACT_TRI = forced([0] * len(S0) + [1 if r in tri else 0 for r in range(len(S1))])
assert FACT_U == sp.Rational(1, 4), FACT_U
assert FACT_V == sp.Rational(1, 4), FACT_V
assert FACT_D0 == 0 and FACT_D1 == 0, (FACT_D0, FACT_D1)
assert FACT_TRI == sp.Rational(1, 4), FACT_TRI

# ------------------------------------------------------------------- emission
MASKNAME = {}
ZNAME = {}


def cplx(r):
    """a rational as a Lean complex literal coefficient"""
    return '(%s : ℂ)' % (('%s/%s' % (r.p, r.q)) if r.q != 1 else str(r.p))


def emit():
    zs = set()
    masks = [EH, EAH]
    for (e, eb), ((me, c1), (mb, c2)) in PAIRROW.items():
        masks += [me, mb]
        zs |= {z for z, _ in c1} | {z for z, _ in c2}
    for key in K:
        zs |= {z for z, _ in K[key][1]}
    zs |= {z for z, _ in DIAGB}
    masks = list(dict.fromkeys(masks))
    for r, m in enumerate(masks):
        MASKNAME[m] = 'ef%d' % r
    MASKNAME[EA] = 'efA'
    for r, z in enumerate(sorted(zs)):
        ZNAME[z] = 'w%d' % r

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
    W('Qubit 1 has angle zero, so the amplitudes group into spinors in `ℂ²`.')
    W('Qubit 6 has the half angle; on the two-qubit subsystem it spans with the')
    W('zero-angle qubit, the cross Knill--Laflamme block reads')
    W('')
    W('```')
    W('ut * u† + vt * v† = 0 ,')
    W('```')
    W('')
    W('a cancellation of two rank-one matrices whose four anchors all have')
    W('squared norm 1/4.  Two complementary physical-pair rows then eliminate')
    W('against it -- see `SixQubit.Spinor.cancel_perp`, which does this without')
    W('spans, unit vectors or division -- leaving the top edge vector `b_ebar`')
    W('orthogonal to both anchors.  The `H = 0` diagonal block of the equality')
    W('of the two reduced states on that subsystem then kills `b_ebar` outright')
    W('(`SixQubit.Spinor.edge_zero`), while the moment polytope forces the three')
    W('complementary pair masses to sum to 1/4, so one of them is positive.')
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
    W('def S0 : Finset (SS.BitString 6) := {%s}'
      % ', '.join('y%d' % r for r in range(len(S0))))
    W('def S1 : Finset (SS.BitString 6) := {%s}'
      % ', '.join('z%d' % r for r in range(len(S1))))
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
    # which dressings each mask needs
    need = {m: set() for m in masks}
    for (qb, p), (e, comb, _) in K.items():
        need[e] |= {z for z, _ in comb}
    for (e, eb), ((me, c1), (mb, c2)) in PAIRROW.items():
        need[me] |= {z for z, _ in c1}
        need[mb] |= {z for z, _ in c2}
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
              + (', ' if len(inc) > 1 else '') + 'Finset.sum_singleton]')
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
      % ', '.join('y%d' % r for r in range(len(S0))))
    W('theorem dincT : S1.filter (fun y => SS.bxor y efA ∈ S1) = {%s} := by decide'
      % ', '.join('z%d' % r for r in range(len(S1))))
    for i0, r in incdB:
        W('theorem dflipB_%d : SS.bxor y%d efA = y%d := by decide' % (r, r, i0))
    for i0, r in incdT:
        W('theorem dflipT_%d : SS.bxor z%d efA = z%d := by decide' % (r, r, i0))
    W('')
    for z in sorted({z for z, _ in DIAGB}):
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
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(S0) - 1))
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
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(S1) - 1))
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
    n0, n1 = len(S0), len(S1)
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
    bsum = ' + '.join('r%d' % b_i[e][0] for e in PAIRS)
    tsum = ' + '.join('r%d' % b_i[e][1] for e in PAIRS)
    trisum = ' + '.join('(r%d + r%d)' % (b_i[eb][0], b_i[eb][1]) for _, eb in CLASSES)
    W('/-- The anchor masses, the two diagonal entries of the `H = 0` block, and')
    W('the total mass of the three complementary pair representatives. -/')
    W('theorem MomentSystem.facts {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    W('    q%d + q%d = 1/4 ∧ q%d + q%d = 1/4' % (u_i[0], u_i[1], v_i[0], v_i[1]))
    W('    ∧ q%d + q%d = %s' % (u_i[0], v_i[0], bsum))
    W('    ∧ q%d + q%d = %s' % (u_i[1], v_i[1], tsum))
    W('    ∧ %s = 1/4 := by' % trisum)
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
    for key in [('0', '0'), ('0', '1'), ('1', '0'), ('1', '1')]:
        e, comb, _ = K[key]
        for z, co in comb:
            if (e, z) not in rows:
                rows.append((e, z))
    for (ee, eb), ((me, c1), (mb, c2)) in PAIRROW.items():
        for z, co in c1:
            if (me, z) not in rows:
                rows.append((me, z))
        for z, co in c2:
            if (mb, z) not in rows:
                rows.append((mb, z))
    hname = {}
    for r, (m, z) in enumerate(rows):
        hname[(m, z)] = 'ho%d' % r
        W('    (ho%d : offSum c d %s %s = 0)' % (r, MASKNAME[m], ZNAME[z]))
    dname = {}
    for r, (z, co) in enumerate(DIAGB):
        dname[z] = 'hd%d' % r
        W('    (hd%d : diagBot c efA %s = diagTop d efA %s)' % (r, ZNAME[z], ZNAME[z]))
    W('    : False := by')
    for (m, z), nm in hname.items():
        W('  rw [ex_%s_%s] at %s' % (MASKNAME[m], ZNAME[z], nm))
    for z, nm in dname.items():
        W('  rw [dexB_%s, dexT_%s] at %s' % (ZNAME[z], ZNAME[z], nm))
    # the four cross-block entries
    for (qb, p), lbl in [(('0', '0'), 'K00'), (('0', '1'), 'K01'),
                         (('1', '0'), 'K10'), (('1', '1'), 'K11')]:
        e, comb, pos = K[(qb, p)]
        qq = 0 if qb == '0' else 1
        pp = 0 if p == '0' else 1
        W('  have %s : star (c y%d) * d z%d + star (c y%d) * d z%d = 0 := by'
          % (lbl, u_i[qq], ut_i[pp], v_i[qq], vt_i[pp]))
        W('    linear_combination ' + ' + '.join(
            '%s * %s' % (cplx(co), hname[(e, z)]) for z, co in comb))
    # the off-diagonal entry of the H = 0 block
    W('  have Doff : star (c y%d) * c y%d + star (c y%d) * c y%d = %s := by'
      % (u_i[1], u_i[0], v_i[1], v_i[0],
         ' + '.join('star (d z%d) * d z%d' % (b_i[e][1], b_i[e][0]) for e in PAIRS)))
    W('    linear_combination ' + ' + '.join(
        '%s * %s' % (cplx(co), dname[z]) for z, co in DIAGB))
    W('  obtain ⟨hu4, hv4, D0, D1, hsum⟩ := hm.facts')
    W('  have hu : (0:ℝ) < Complex.normSq (c y%d) + Complex.normSq (c y%d) := by linarith'
      % (u_i[0], u_i[1]))
    W('  have hv : (0:ℝ) < Complex.normSq (c y%d) + Complex.normSq (c y%d) := by linarith'
      % (v_i[0], v_i[1]))
    W('  have htri : ' + ' ∨ '.join(
        '(0:ℝ) < Complex.normSq (d z%d) + Complex.normSq (d z%d)'
        % (b_i[eb][0], b_i[eb][1]) for _, eb in CLASSES) + ' := by')
    W('    by_contra hcon')
    W('    push_neg at hcon')
    W('    obtain ⟨t1, t2, t3⟩ := hcon')
    W('    linarith')
    W('  rcases htri with hpos | hpos | hpos')
    for (ee, eb), ((me, c1), (mb, c2)) in PAIRROW.items():
        aa, bb = a_i[ee], b_i[eb]
        W('  · have P1 : star (c y%d) * d z%d + star (c y%d) * d z%d'
          % (aa[0], ut_i[0], aa[1], ut_i[1]))
        W('        + (star (c y%d) * d z%d + star (c y%d) * d z%d) = 0 := by'
          % (v_i[0], bb[0], v_i[1], bb[1]))
        W('      linear_combination ' + ' + '.join(
            '%s * %s' % (cplx(co), hname[(me, z)]) for z, co in c1))
        W('    have P2 : star (c y%d) * d z%d + star (c y%d) * d z%d'
          % (u_i[0], bb[0], u_i[1], bb[1]))
        W('        + (star (c y%d) * d z%d + star (c y%d) * d z%d) = 0 := by'
          % (aa[0], vt_i[0], aa[1], vt_i[1]))
        W('      linear_combination ' + ' + '.join(
            '%s * %s' % (cplx(co), hname[(mb, z)]) for z, co in c2))
        W('    obtain ⟨hBu, hBv⟩ :=')
        W('      SixQubit.Spinor.cancel_perp K00 K01 K10 K11 P1 P2 hu hv')
        rest = [e for e in PAIRS if e != eb]
        W('    have D0a : Complex.normSq (c y%d) + Complex.normSq (c y%d)' % (u_i[0], v_i[0]))
        W('        = %s := by linarith' % ' + '.join(
            ['Complex.normSq (d z%d)' % bb[0]]
            + ['Complex.normSq (d z%d)' % b_i[e][0] for e in rest]))
        W('    have D1a : Complex.normSq (c y%d) + Complex.normSq (c y%d)' % (u_i[1], v_i[1]))
        W('        = %s := by linarith' % ' + '.join(
            ['Complex.normSq (d z%d)' % bb[1]]
            + ['Complex.normSq (d z%d)' % b_i[e][1] for e in rest]))
        W('    have Doffa : star (c y%d) * c y%d + star (c y%d) * c y%d'
          % (u_i[1], u_i[0], v_i[1], v_i[0]))
        W('        = %s := by' % ' + '.join(
            ['star (d z%d) * d z%d' % (bb[1], bb[0])]
            + ['star (d z%d) * d z%d' % (b_i[e][1], b_i[e][0]) for e in rest]))
        W('      linear_combination Doff')
        W('    have hz := SixQubit.Spinor.edge_zero D0a D1a Doffa hBu hBv')
        W('    linarith')
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
