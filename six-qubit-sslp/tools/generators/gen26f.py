"""Generator for the orbit-26 transcription layer, SixQubit/Orbit26.lean.

Stages (select with `python gen26f.py <n>`, default 7):

  1  positions, S0/S1, S0_eq_fiber/S1_eq_fiber
  2  the MomentSystem structure and every moment fact
  3  offSum/diagBot/diagTop plus incidence, flip and sign lemmas by `decide`
  4  the Walsh expansion lemmas
  5  the twelve outer-identity entries
  6  the twelve anchor scalars
  7  the matrix moment identity, per group and per entry

Every certificate is recomputed here (never hard-coded) and asserted before it
is printed.
"""
import sys

SCRATCH = (r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue'
           r'/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
sys.path.insert(0, SCRATCH)

import sympy as sp

import o26
from o26 import S0, S1, T0, BOT, TOP, GROUPS
from scan import bits, xor, dot
from kl import dressings_full
from cert import build, reduce_mod_linear

# --------------------------------------------------------------------------
# certificate machinery
# --------------------------------------------------------------------------

E0, EX = '000000', '100000'
# the eight diagonal dressings, in the order used by the certificate
ZS8 = ['000000', '010000', '001000', '000001', '100000', '110000', '101000', '100001']


def incidences(mask):
    """(bottom index in S0, top index in S1) for every off-diagonal incidence."""
    return [(S0.index(xor(y, mask)), t) for t, y in enumerate(S1) if xor(y, mask) in S0]


def solve_dressing(mask, want):
    """Rational combination of admissible dressings picking out `want`.

    `want` is a set of incidence pairs; the returned coefficients c_z satisfy
    sum_z c_z (-1)^{z . y_t} = 1 on those pairs and 0 on the others.
    """
    inc = incidences(mask)
    zs = dressings_full(mask)
    M = sp.Matrix([[sp.Integer((-1) ** dot(z, S1[t])) for z in zs] for (_b, t) in inc])
    rhs = sp.Matrix([[sp.Integer(1) if p in want else sp.Integer(0)] for p in inc])
    rr, piv = M.row_join(rhs).rref()
    ncols = M.cols
    for i in range(rr.rows):
        if all(rr[i, j] == 0 for j in range(ncols)) and rr[i, ncols] != 0:
            raise AssertionError('inconsistent dressing system for %s' % mask)
    x = [sp.Integer(0)] * ncols
    for i, p in enumerate(piv):
        if p < ncols:
            x[p] = rr[i, ncols]
    assert sp.simplify(M * sp.Matrix([[v] for v in x]) - rhs) == sp.zeros(M.rows, 1)
    return [(zs[k], x[k]) for k in range(ncols) if x[k] != 0], inc


# --------------------------------------------------------------------------
# the three relation families
# --------------------------------------------------------------------------

OUTER = {}      # (g, h, a, b) -> (mask, ordered target pairs, dressing cert)
for g in range(3):
    for h in range(g + 1, 3):
        for a in (0, 1):
            for b in (0, 1):
                terms = [(2 * g, 2 * h + 1), (2 * g + 1, 2 * h),
                         (2 * h, 2 * g + 1), (2 * h + 1, 2 * g)]
                pairs = [(BOT[i][a], TOP[j][b]) for (i, j) in terms]
                masks = {xor(S0[p], S1[q]) for (p, q) in pairs}
                assert len(masks) == 1, (g, h, a, b, masks)
                m = masks.pop()
                cof, inc = solve_dressing(m, set(pairs))
                assert len(set(pairs)) == 4
                OUTER[(g, h, a, b)] = (m, pairs, cof)

ANCH = {}       # (i, j) -> (mask, ordered target pairs, dressing cert)
for i in range(6):
    for j in (6, 7):
        # ip C_i D_j + ip C_j D_i  -- block first, the order Block26 consumes
        pairs = [(BOT[i][a], TOP[j][a]) for a in (0, 1)] \
            + [(BOT[j][a], TOP[i][a]) for a in (0, 1)]
        masks = {xor(S0[p], S1[q]) for (p, q) in pairs}
        assert len(masks) == 1, (i, j, masks)
        m = masks.pop()
        cof, inc = solve_dressing(m, set(pairs))
        assert len(set(pairs)) == 4
        ANCH[(i, j)] = (m, pairs, cof)

DIAG = {}       # (g, a, b) -> list of (flip, dressing, rational)
for g in range(4):
    for a in (0, 1):
        for b in (0, 1):
            r = o26.solve(a, b, g)
            assert r is not None, ('matrix moment entry not in span', g, a, b)
            # re-verify the certificate symbolically
            chk = sp.expand(sum(v * o26.cond(e, z) for (e, z, v) in r)
                            - o26.target(a, b, g))
            assert chk == 0, ('certificate mismatch', g, a, b, chk)
            flips = {e for (e, _z, _v) in r}
            assert len(flips) == 1
            assert sorted(z for (_e, z, _v) in r) == sorted(ZS8)
            DIAG[(g, a, b)] = r

OFFMASKS = sorted({m for (m, _p, _c) in OUTER.values()}
                  | {m for (m, _p, _c) in ANCH.values()})
assert len(OFFMASKS) == 12, OFFMASKS
EF = sorted(set(OFFMASKS) | {E0, EX})
WD = sorted({z for (_m, _p, cof) in list(OUTER.values()) + list(ANCH.values())
             for (z, _v) in cof} | set(ZS8))
EFI = {m: k for k, m in enumerate(EF)}
WDI = {z: k for k, z in enumerate(WD)}

# --------------------------------------------------------------------------
# the moment system and the moment facts
# --------------------------------------------------------------------------

Q, R, V, Am, bv, MNAMES = build(S0, S1)
QS = {k: Q[k] for k in range(16)}
RS = {k: R[k] for k in range(16)}


def eqn_lean(row, rhs):
    """`sum of +1 vars = sum of -1 vars (+ constant)`, in Lean syntax."""
    lhs, rgt = [], []
    for k in range(32):
        cv = row[k]
        nm = ('q%d' % k) if k < 16 else ('r%d' % (k - 16))
        if cv == 1:
            lhs.append(nm)
        elif cv == -1:
            rgt.append(nm)
        elif cv != 0:
            raise AssertionError('unexpected coefficient %s' % cv)
    if rhs != 0:
        rgt.append(str(rhs))
    if not lhs:
        lhs = ['0']
    if not rgt:
        rgt = ['0']
    return ' + '.join(lhs) + ' = ' + ' + '.join(rgt)


P = [QS[BOT[i][0]] + QS[BOT[i][1]] for i in range(8)]
QQ_ = [RS[TOP[i][0]] + RS[TOP[i][1]] for i in range(8)]

FACTS = []
for i in range(8):
    FACTS.append(('mPQ%d' % i,
                  'block %d carries the same weight below and above' % i,
                  sp.expand(P[i] - QQ_[i])))
FACTS.append(('mP6', 'the first anchor block holds an eighth',
              sp.expand(P[6] - sp.Rational(1, 8))))
FACTS.append(('mP7', 'the second anchor block holds an eighth',
              sp.expand(P[7] - sp.Rational(1, 8))))
FACTS.append(('mSUM6', 'the six non-anchor blocks hold three quarters',
              sp.expand(sum(P[i] for i in range(6)) - sp.Rational(3, 4))))
for gi in range(4):
    FACTS.append(('mT%d' % gi,
                  'group %d holds a quarter' % gi,
                  sp.expand(P[GROUPS[gi][0]] + P[GROUPS[gi][1]] - sp.Rational(1, 4))))
FACTS.append(('mT2a', 'the first block of each group holds three eighths in all',
              sp.expand(P[0] + P[2] + P[4] - sp.Rational(3, 8))))
FACTS.append(('mT2b', 'the second block of each group holds three eighths in all',
              sp.expand(P[1] + P[3] + P[5] - sp.Rational(3, 8))))

CERT = {}
for name, _doc, ex in FACTS:
    cof, rem = reduce_mod_linear(ex, V, Am, bv)
    assert rem == 0, ('moment fact not in the linear ideal', name, rem)
    CERT[name] = cof


def expr_lean(ex):
    """A sympy linear form in q*/r* as a Lean expression."""
    ex = sp.expand(ex)
    out = []
    for k in range(16):
        cv = ex.coeff(QS[k])
        if cv != 0:
            out.append((cv, 'q%d' % k))
    for k in range(16):
        cv = ex.coeff(RS[k])
        if cv != 0:
            out.append((cv, 'r%d' % k))
    const = ex - sum(cv * sp.Symbol(nm) for cv, nm in out)
    const = sp.simplify(const)
    s = ''
    for cv, nm in out:
        if cv == 1:
            s += (' + ' if s else '') + nm
        elif cv == -1:
            s += (' - ' if s else '-') + nm
        elif cv > 0:
            s += (' + ' if s else '') + '(%s) * %s' % (cv, nm)
        else:
            s += (' - ' if s else '-') + '(%s) * %s' % (-cv, nm)
    if const != 0:
        if const > 0:
            s += ' + %s' % const
        else:
            s += ' - %s' % (-const)
    return s or '0'


def comb_lean(coeffs, names):
    parts = []
    for cv, nm in zip(coeffs, names):
        if cv == 0:
            continue
        parts.append('(%s) * %s' % (cv, nm))
    return ' + '.join(parts) if parts else '0'


# --------------------------------------------------------------------------
# Lean emission
# --------------------------------------------------------------------------

OUT = []


def w(line=''):
    OUT.append(line)


def lean_bs(s):
    return 'bs ' + ' '.join('true ' if ch == '1' else 'false' for ch in s)


def prod_c(i, j):
    return 'star (c y%d) * d z%d' % (i, j)


def sign_lemmas(terms):
    """Only the `signMul` lemmas that actually fire, so no simp argument is unused."""
    out = []
    if any(sg < 0 for sg, _t in terms):
        out.append('SixQubit.signMul_true')
    if any(sg > 0 for sg, _t in terms):
        out.append('SixQubit.signMul_false')
    return out


def signed_sum(terms):
    """terms: list of (sign, string)."""
    s = ''
    for sg, t in terms:
        if not s:
            s = t if sg > 0 else '- ' + t
        else:
            s += (' + ' if sg > 0 else ' - ') + t
    return s


NTH = int(sys.argv[1]) if len(sys.argv) > 1 else 7

# which dressings each off-diagonal mask needs, and in what incidence order
_needed = {m: set() for m in OFFMASKS}
for (mm, _p, cof) in list(OUTER.values()) + list(ANCH.values()):
    for (z, _v) in cof:
        _needed[mm].add(WDI[z])
OFFPLAN = [(EFI[m], sorted(incidences(m), key=lambda p: p[1]), sorted(_needed[m]))
           for m in OFFMASKS]
DIAGPLAN = [(EFI[e], [WDI[z] for z in ZS8]) for e in (E0, EX)]

w('import Mathlib')
w('')
w('import SS.FullKL')
w('import SixQubit.Common')
w('import SixQubit.Block26')
w('')
w('/-!')
w('# Six-qubit no-go for moment orbit 26: the transcription layer')
w('')
w('Orbit 26 of `six_qubit_sslp.tex`: q = 4, angle vector a = (0, 1, 1, 2, 2, 3),')
w('residues 0 and 1, fibers of size sixteen each.  The first angle is zero, so')
w('both fibers are closed under `X_1`, and each splits into eight blocks of two')
w('amplitudes.  Writing `C_i` for the bottom block and `D_i` for the top block')
w('carried by the complementary tail, the Knill-Laflamme system supplies')
w('')
w('* twelve **outer identities**, four matrix entries for each of the three')
w('  pairs of non-anchor groups;')
w('* twelve **anchor scalars** `ip C_i D_j + ip C_j D_i = 0`, one for each')
w('  non-anchor block `i` and each anchor `j`;')
w('* the **matrix moment identity** `C_g C_g^† + D_g D_g^† = ρ/2`, per group and')
w('  per entry, from the diagonal conditions;')
w('')
w('together with the linear **moment facts** `P_i = Q_i`, `P_6 = P_7 = 1/8`, the')
w('group totals `P_{2g} + P_{2g+1} = 1/4` and the load-bearing pair')
w('`P_0 + P_2 + P_4 = P_1 + P_3 + P_5 = 3/8`.')
w('')
w('The algebra that consumes these lives in `SixQubit.Block26`.')
w('')
w('Everything computational is decided by the Lean kernel; `native_decide` is')
w('not used.')
w('-/')
w('')
w('namespace SixQubit.Orbit26')
w('')
w('open scoped BigOperators')
w('')
w('noncomputable section')
w('')
w('def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]')
w('')

# ---------------------------------------------------------------- stage 1
w('/-! ## The two fibers -/')
w('')
for k, s in enumerate(S0):
    w('def y%-2d : SS.BitString 6 := %s -- %s' % (k, lean_bs(s), s))
w('')
for k, s in enumerate(S1):
    w('def z%-2d : SS.BitString 6 := %s -- %s' % (k, lean_bs(s), s))
w('')
w('def S0 : Finset (SS.BitString 6) := {%s}'
  % ', '.join('y%d' % k for k in range(16)))
w('def S1 : Finset (SS.BitString 6) := {%s}'
  % ', '.join('z%d' % k for k in range(16)))
w('')
w('def av : Fin 6 -> ZMod 4 := ![0, 1, 1, 2, 2, 3]')
w('')
w('/-- Each support is exactly its residue fiber, decided over all 64 strings. -/')
w('theorem S0_eq_fiber :')
w('    (Finset.univ : Finset (SS.BitString 6)).filter')
w('      (fun x => SS.weight av x = 0) = S0 := by')
w('  decide')
w('')
w('theorem S1_eq_fiber :')
w('    (Finset.univ : Finset (SS.BitString 6)).filter')
w('      (fun x => SS.weight av x = 1) = S1 := by')
w('  decide')
w('')

# ---------------------------------------------------------------- stage 2
if NTH >= 2:
    w('/-! ## The moment system -/')
    w('')
    w('/-- The two normalizations and the moment equalities, with every probability')
    w('nonnegative. -/')
    w('structure MomentSystem (%s : Real) : Prop where'
      % ' '.join(['q%d' % k for k in range(16)] + ['r%d' % k for k in range(16)]))
    for i, nm in enumerate(MNAMES):
        w('  %s : %s' % (nm, eqn_lean([Am[i, k] for k in range(32)], bv[i])))
    w('')
    for k in range(16):
        w('  nq%d : 0 ≤ q%d' % (k, k))
    for k in range(16):
        w('  nr%d : 0 ≤ r%d' % (k, k))
    w('')

    ARGS = ' '.join(['q%d' % k for k in range(16)] + ['r%d' % k for k in range(16)])
    OB = ', '.join(list(MNAMES) + ['nq%d' % k for k in range(16)]
                   + ['nr%d' % k for k in range(16)])
    for name, doc, ex in FACTS:
        cof = CERT[name]
        used = {MNAMES[j] for j in range(len(MNAMES)) if cof[j] != 0}
        ob = ', '.join([(nm if nm in used else '_' + nm) for nm in MNAMES]
                       + ['_nq%d' % k for k in range(16)]
                       + ['_nr%d' % k for k in range(16)])
        w('/-- %s. -/' % doc)
        w('theorem %s {%s : Real} (h : MomentSystem %s) :' % (name, ARGS, ARGS))
        w('    %s = 0 := by' % expr_lean(ex))
        w('  obtain ⟨%s⟩ := h' % ob)
        w('  linear_combination %s' % comb_lean(cof, MNAMES))
        w('')

# ---------------------------------------------------------------- stage 3
if NTH >= 3:
    w('/-! ## The Walsh sums -/')
    w('')
    for k, m in enumerate(EF):
        w('def ef%-2d : SS.BitString 6 := %s -- flip %s' % (k, lean_bs(m), m))
    w('')
    for k, z in enumerate(WD):
        w('def w%-2d : SS.BitString 6 := %s -- dressing %s' % (k, lean_bs(z), z))
    w('')
    w('/-- `<0_L| X^e Z^z |1_L>` with the global prefactor omitted. -/')
    w('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    w('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    w('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    w('')
    w('/-- `<0_L| X^e Z^z |0_L>`. -/')
    w('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    w('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
    w('      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)')
    w('')
    w('/-- `<1_L| X^e Z^z |1_L>`. -/')
    w('def diagTop (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    w('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
    w('      SixQubit.signMul (SS.bdot z y) (star (d (SS.bxor y e)) * d y)')
    w('')
    w('/-- `star z * z` is the squared modulus. -/')
    w('theorem sq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by')
    w('  rw [Complex.normSq_eq_conj_mul_self]; rfl')
    w('')
    w('/-- The bridge to `SixQubit.Block26`: its `ip` is this file\'s `star`-pairing. -/')
    w('theorem ip_eq (a1 a2 b1 b2 : ℂ) :')
    w('    SixQubit.Block26.ip a1 a2 b1 b2 = star a1 * b1 + star a2 * b2 := rfl')
    w('')

    # sign lemmas, deduplicated over the whole file
    SGY, SGZ = {}, {}

    def need_sy(k, i):
        SGY[(k, i)] = dot(WD[k], S0[i])
        return 'sy_%d_%d' % (k, i)

    def need_sz(k, j):
        SGZ[(k, j)] = dot(WD[k], S1[j])
        return 'sz_%d_%d' % (k, j)

    for (mi, inc, used) in OFFPLAN:
        for k in used:
            for (_b, t) in inc:
                need_sz(k, t)
    for (ei, used) in DIAGPLAN:
        for k in used:
            for i in range(16):
                need_sy(k, i)
            for j in range(16):
                need_sz(k, j)

    w('/-! ### Incidences, flips and signs -/')
    w('')
    for (mi, inc, used) in OFFPLAN:
        w('theorem incO_%d :' % mi)
        w('    S1.filter (fun y => SS.bxor y ef%d ∈ S0) = {%s} := by decide'
          % (mi, ', '.join('z%d' % t for (_b, t) in inc)))
        for (b, t) in inc:
            w('theorem fo_%d_%d : SS.bxor z%d ef%d = y%d := by decide' % (mi, t, t, mi, b))
    w('')
    for (ei, used) in DIAGPLAN:
        e = EF[ei]
        w('theorem incB_%d :' % ei)
        w('    S0.filter (fun x => SS.bxor x ef%d ∈ S0) = {%s} := by decide'
          % (ei, ', '.join('y%d' % i for i in range(16))))
        w('theorem incT_%d :' % ei)
        w('    S1.filter (fun y => SS.bxor y ef%d ∈ S1) = {%s} := by decide'
          % (ei, ', '.join('z%d' % j for j in range(16))))
        for i in range(16):
            w('theorem fb_%d_%d : SS.bxor y%d ef%d = y%d := by decide'
              % (ei, i, i, ei, S0.index(xor(S0[i], e))))
        for j in range(16):
            w('theorem ft_%d_%d : SS.bxor z%d ef%d = z%d := by decide'
              % (ei, j, j, ei, S1.index(xor(S1[j], e))))
    w('')
    for (k, i) in sorted(SGY):
        w('theorem sy_%d_%d : SS.bdot w%d y%d = %s := by decide'
          % (k, i, k, i, 'true' if SGY[(k, i)] else 'false'))
    for (k, j) in sorted(SGZ):
        w('theorem sz_%d_%d : SS.bdot w%d z%d = %s := by decide'
          % (k, j, k, j, 'true' if SGZ[(k, j)] else 'false'))
    w('')

# ---------------------------------------------------------------- stage 4
SUMSPLIT = lambda n: (', '.join(['Finset.sum_insert (by decide)'] * (n - 1))
                      + ', Finset.sum_singleton')

if NTH >= 4:
    w('/-! ## The Walsh expansions -/')
    w('')
    for (mi, inc, used) in OFFPLAN:
        for k in used:
            terms = [(-1 if dot(WD[k], S1[t]) else 1, prod_c(b, t)) for (b, t) in inc]
            w('theorem exO_%d_%d (c d : SS.BitString 6 -> ℂ) :' % (mi, k))
            w('    offSum c d ef%d w%d =' % (mi, k))
            w('      %s := by' % signed_sum(terms))
            w('  unfold offSum')
            w('  rw [incO_%d]' % mi)
            w('  rw [%s]' % SUMSPLIT(len(inc)))
            w('  rw [%s]' % ', '.join('fo_%d_%d' % (mi, t) for (_b, t) in inc))
            w('  simp only [%s]'
              % ', '.join(['sz_%d_%d' % (k, t) for (_b, t) in inc]
                          + sign_lemmas(terms)))
            w('  try ring')
            w('')
    for (ei, used) in DIAGPLAN:
        e = EF[ei]
        for k in used:
            terms = [(-1 if dot(WD[k], S0[i]) else 1,
                      'star (c y%d) * c y%d' % (S0.index(xor(S0[i], e)), i))
                     for i in range(16)]
            w('theorem exB_%d_%d (c : SS.BitString 6 -> ℂ) :' % (ei, k))
            w('    diagBot c ef%d w%d =' % (ei, k))
            w('      %s := by' % signed_sum(terms))
            w('  unfold diagBot')
            w('  rw [incB_%d]' % ei)
            w('  rw [%s]' % SUMSPLIT(16))
            w('  rw [%s]' % ', '.join('fb_%d_%d' % (ei, i) for i in range(16)))
            w('  simp only [%s]'
              % ', '.join(['sy_%d_%d' % (k, i) for i in range(16)]
                          + sign_lemmas(terms)))
            w('  try ring')
            w('')
            terms = [(-1 if dot(WD[k], S1[j]) else 1,
                      'star (d z%d) * d z%d' % (S1.index(xor(S1[j], e)), j))
                     for j in range(16)]
            w('theorem exT_%d_%d (d : SS.BitString 6 -> ℂ) :' % (ei, k))
            w('    diagTop d ef%d w%d =' % (ei, k))
            w('      %s := by' % signed_sum(terms))
            w('  unfold diagTop')
            w('  rw [incT_%d]' % ei)
            w('  rw [%s]' % SUMSPLIT(16))
            w('  rw [%s]' % ', '.join('ft_%d_%d' % (ei, j) for j in range(16)))
            w('  simp only [%s]'
              % ', '.join(['sz_%d_%d' % (k, j) for j in range(16)]
                          + sign_lemmas(terms)))
            w('  try ring')
            w('')

# ---------------------------------------------------------------- stage 5
if NTH >= 5:
    w('/-! ## The outer identities -/')
    w('')
    w('/-- For a pair `(g, h)` of non-anchor groups and each of the four matrix')
    w('entries, `sum_c C_{2g+c}^† D_{2h+1-c} + sum_c C_{2h+c}^† D_{2g+1-c} = 0`. -/')
    for (g, h, a, b) in sorted(OUTER):
        (m, pairs, cof) = OUTER[(g, h, a, b)]
        mi = EFI[m]
        hyp = ['(h%d : offSum c d ef%d w%d = 0)' % (n, mi, WDI[z])
               for n, (z, _v) in enumerate(cof)]
        w('theorem outer_g%dh%d_a%db%d (c d : SS.BitString 6 -> ℂ)' % (g, h, a, b))
        w('    %s :' % ' '.join(hyp))
        w('    %s = 0 := by' % ' + '.join(prod_c(p, q) for (p, q) in pairs))
        for n, (z, _v) in enumerate(cof):
            w('  rw [exO_%d_%d c d] at h%d' % (mi, WDI[z], n))
        w('  linear_combination %s'
          % ' + '.join('(%s) * h%d' % (v, n) for n, (_z, v) in enumerate(cof)))
        w('')

# ---------------------------------------------------------------- stage 6
if NTH >= 6:
    w('/-! ## The anchor scalars -/')
    w('')
    w('/-- For a non-anchor block `i` and an anchor `j`,')
    w('`ip C_i D_j + ip C_j D_i = 0`. -/')
    for (i, j) in sorted(ANCH):
        (m, pairs, cof) = ANCH[(i, j)]
        mi = EFI[m]
        hyp = ['(h%d : offSum c d ef%d w%d = 0)' % (n, mi, WDI[z])
               for n, (z, _v) in enumerate(cof)]
        w('theorem anch_i%d_j%d (c d : SS.BitString 6 -> ℂ)' % (i, j))
        w('    %s :' % ' '.join(hyp))
        w('    %s = 0 := by' % ' + '.join(prod_c(p, q) for (p, q) in pairs))
        for n, (z, _v) in enumerate(cof):
            w('  rw [exO_%d_%d c d] at h%d' % (mi, WDI[z], n))
        w('  linear_combination %s'
          % ' + '.join('(%s) * h%d' % (v, n) for n, (_z, v) in enumerate(cof)))
        w('')

# ---------------------------------------------------------------- stage 7
if NTH >= 7:
    w('/-! ## The matrix moment identity -/')
    w('')
    w('/-! `C_g C_g^† + D_g D_g^† = ρ/2` with `ρ = sum_g C_g C_g^†`, per group and')
    w('per matrix entry. -/')
    w('')
    for g in range(4):
        for a in (0, 1):
            for b in (0, 1):
                cert = DIAG[(g, a, b)]
                e = cert[0][0]
                ei = EFI[e]
                order = {z: v for (_e, z, v) in cert}
                hyp = []
                for n, z in enumerate(ZS8):
                    hyp.append('(D%d : diagBot c ef%d w%d = diagTop d ef%d w%d)'
                               % (n, ei, WDI[z], ei, WDI[z]))
                lhs = ' + '.join(
                    'c y%d * star (c y%d) + d z%d * star (d z%d)'
                    % (BOT[i][a], BOT[i][b], TOP[i][a], TOP[i][b])
                    for i in GROUPS[g])
                rhs = ' + '.join('c y%d * star (c y%d)' % (BOT[i][a], BOT[i][b])
                                 for i in range(8))
                w('set_option maxHeartbeats 2000000 in')
                w('theorem mom_g%d_a%db%d (c d : SS.BitString 6 -> ℂ)' % (g, a, b))
                for hh in hyp:
                    w('    %s' % hh)
                w('    : %s' % lhs)
                w('      = 1/2 * (%s) := by' % rhs)
                for n, z in enumerate(ZS8):
                    w('  rw [exB_%d_%d c, exT_%d_%d d] at D%d'
                      % (ei, WDI[z], ei, WDI[z], n))
                w('  linear_combination %s'
                  % ' + '.join('(%s) * D%d' % (order[z], n)
                               for n, z in enumerate(ZS8)))
                w('')

w('end')
w('')
w('end SixQubit.Orbit26')

txt = '\n'.join(OUT) + '\n'
path = SCRATCH + '/Orbit26.lean'
with open(path, 'w', encoding='utf-8') as f:
    f.write(txt)
print('wrote %s : %d lines, %d theorems'
      % (path, txt.count('\n'), txt.count('\ntheorem ')))
