"""Generator for orbit 53 at the manifest residue delta = q/m = 1.

The fibers are complementary, so the moment system already identifies every
top probability with the bottom probability at the complementary string.
Write `u_i = star (c y_i)` and `v_j = d z_{top j}`.

Three weight-one flips carry a four-incidence Walsh system of rank three; row
reduction gives, for each of them, one *equality* row and two *reciprocal*
rows.  Taking squared moduli of the reciprocal rows turns them into three
quadratic moment relations

    q0 q3 = q1 q2 ,     q0 q5 = q1 q4 ,     q0 q7 = q1 q6 ,

whose quadratic parts cancel identically against the linear moment identities.
They therefore pin the entire moment point: q0 = q1 = 1/6 and every other
probability is 1/12.  In particular no amplitude vanishes.

The two weight-two flips 000011 and 000101 give `u0 v9 + u9 v0 = 0` and
`u1 v9 + u9 v1 = 0`; eliminating `v9` and cancelling the nonzero `u9` gives the
phase-synchronisation identity `u1 v0 = u0 v1`.  Feeding it back through the
two remaining reciprocal rows produces the two binomials

    u1 u4 + u0 u5 = 0 ,      u1 u6 + u0 u7 = 0 ,

and the four-incidence flip 100001 then collapses to `u0 u5 u7 v0 = 0`, which
is impossible.  No division is used anywhere: every cancellation is a
`mul_eq_zero` case split against a probability the moment point pins positive.

    python tools/run.py generators/gen53.py
"""
import io
import json
import os
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from orbit import fiber

NL = chr(10)
OID = 53
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    '..', '..'))
MAN = json.loads(io.open(os.path.join(REPO, 'tools', 'manifest.json'),
                         encoding='utf-8').read())
BOOL = {'0': 'false', '1': 'true '}
bits = lambda s: [int(c) for c in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
comp = lambda s: ''.join('01'[1 - int(c)] for c in s)
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]
bsline = lambda nm, s: 'def %s : SS.BitString 6 := bs %s  -- %s' % (
    nm, ' '.join(BOOL[c] for c in s), s)
IDX = [(i,) for i in range(6)] + list(combinations(range(6), 2))

# Each relation is named, given by its flip mask and its coefficients on the
# monomials  z(i,j) = u_i v_j  of that mask.
WANT = [
    ('K1', '100000', {(1, 2): 1, (3, 0): 1}),
    ('E4', '010000', {(0, 5): 1, (5, 0): -1}),
    ('E5', '010000', {(1, 4): 1, (5, 0): 1}),
    ('E6', '010000', {(4, 1): 1, (5, 0): 1}),
    ('E7', '001000', {(0, 7): 1, (7, 0): -1}),
    ('E8', '001000', {(1, 6): 1, (7, 0): 1}),
    ('E9', '001000', {(6, 1): 1, (7, 0): 1}),
    ('EA', '000011', {(0, 9): 1, (9, 0): 1}),
    ('EB', '000101', {(1, 9): 1, (9, 1): 1}),
    ('GG', '100001', {(4, 7): 1, (5, 6): 1, (6, 5): 1, (7, 4): 1}),
]


def build():
    E = MAN[str(OID)]
    q, a, d = E['q'], E['a'], E['d']
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    assert (len(S0), len(S1)) == (E['n0'], E['n1'])
    assert sorted(comp(x) for x in S0) == sorted(S1)
    top = {r: S1.index(comp(S0[r])) for r in range(len(S0))}
    rel = {}
    for nm, e, tgtmap in WANT:
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        lab = [(i, S0.index(comp(S1[t]))) for i, t in inc]
        tgt = [tgtmap.get(l, 0) for l in lab]
        assert sum(abs(x) for x in tgt) == sum(abs(x) for x in tgtmap.values()), nm
        Z = dress(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        mu = W.T.gauss_jordan_solve(sp.Matrix(tgt))[0]
        mu = mu.subs({s: 0 for s in mu.free_symbols})
        used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z)) if mu[r] != 0]
        rel[nm] = (e, inc, used, tgtmap)
    return E, S0, S1, top, rel


def emit():
    E, S0, S1, top, rel = build()
    q, a, d = E['q'], E['a'], E['d']
    n0, n1 = len(S0), len(S1)
    masks = sorted({rel[nm][0] for nm, _, _ in WANT})
    zall = sorted({z for nm, _, _ in WANT for z, _ in rel[nm][2]})
    mname = {m: 'ef%d' % r for r, m in enumerate(masks)}
    zname = {z: 'w%d' % r for r, z in enumerate(zall)}
    need = {}
    for nm, _, _ in WANT:
        e, inc, used, _ = rel[nm]
        need.setdefault(e, set()).update(z for z, _ in used)
    hyp = []
    for m in masks:
        for z in sorted(need[m]):
            hyp.append((m, z))
    allv = (' '.join('q%d' % r for r in range(n0)) + ' '
            + ' '.join('r%d' % r for r in range(n1)))
    U = lambda i: 'star (c y%d)' % i
    V = lambda j: 'd z%d' % top[j]
    P = lambda i: 'Complex.normSq (c y%d)' % i

    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit %d' % OID)
    W('')
    W('Orbit %d of `six_qubit_sslp.tex`: q = %d, angle vector' % (OID, q))
    W('a = (%s).  The projective order is m = %d, so the residue that has to'
      % (', '.join(map(str, a)), E['m']))
    W('be excluded is delta = q/m = %d: `S0` is the residue-0 fiber, `S1` the' % d)
    W('residue-%d fiber, and the two are complementary.' % d)
    W('')
    W('Write `u i = star (c y i)` and `v j = d z (top j)`, where `top j` indexes')
    W('the complement of `y j`.  The three weight-one flips 100000, 010000 and')
    W('001000 each have four incidences and a rank-three system of admissible')
    W('dressings; row reduction gives one equality row and two reciprocal rows')
    W('per flip.  Squared moduli of the reciprocal rows are the three quadratic')
    W('moment relations')
    W('')
    W('    q0 q3 = q1 q2 ,    q0 q5 = q1 q4 ,    q0 q7 = q1 q6 ,')
    W('')
    W('whose quadratic parts cancel identically against the linear moment')
    W('identities.  They pin the whole moment point: `q0 = q1 = 1/6` and every')
    W('other probability is `1/12`, so no amplitude vanishes (`pinned`).')
    W('')
    W('The flips 000011 and 000101 give `u0 v9 + u9 v0 = 0` and')
    W('`u1 v9 + u9 v1 = 0`; eliminating `v9` and cancelling the nonzero `u9`')
    W('gives `u1 v0 = u0 v1`.  Substituted into the two remaining reciprocal')
    W('rows this yields `u1 u4 + u0 u5 = 0` and `u1 u6 + u0 u7 = 0`, and the')
    W('four-incidence flip 100001 then collapses to `u0 u5 u7 v0 = 0`, which')
    W('contradicts the pinned point.  Nothing is ever divided: each cancellation')
    W('is a `mul_eq_zero` split against a pinned positive probability.')
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
      % ', '.join('y%d' % r for r in range(n0)))
    W('def S1 : Finset (SS.BitString 6) := {%s}'
      % ', '.join('z%d' % r for r in range(n1)))
    W('')
    W('def av : Fin 6 -> ZMod %d := ![%s]' % (q, ', '.join(map(str, a))))
    W('')
    W('theorem S0_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = 0) = S0 := by')
    W('  decide')
    W('')
    W('theorem S1_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = %d) = S1 := by' % d)
    W('  decide')
    W('')
    W('/-! ## Flip masks, incidences and signs -/')
    W('')
    for m in masks:
        W(bsline(mname[m], m))
    for z in zall:
        W(bsline(zname[z], z))
    W('')
    for m in masks:
        inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        W('theorem incidence_%s :' % mname[m])
        W('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
          % (mname[m], ', '.join('z%d' % t for _, t in inc)))
        for i2, t2 in inc:
            W('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide'
              % (mname[m], t2, t2, mname[m], i2))
        for z in sorted(need[m]):
            for _, t2 in inc:
                W('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
                  % (mname[m], zname[z], t2, zname[z], t2,
                     'true' if dot(z, S1[t2]) else 'false'))
        W('')
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
    W('/-- The linear consequences of the moment system that the pinning uses,')
    W('and the four identifications of a top probability with the bottom')
    W('probability at the complementary string. -/')
    W('theorem MomentSystem.facts {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    facts = ['q4 + q5 = 1/6', 'q6 + q7 = 1/6', 'q0 + q1 = 1/3',
             'q3 + 1/4 = q4 + q6 + q0', 'q2 + q4 + q6 + q0 = 5/12',
             'q9 = 1/12',
             'r%d = q2' % top[2], 'r%d = q4' % top[4], 'r%d = q6' % top[6],
             'r%d = q0' % top[0]]
    W('    ' + ' ∧ '.join(facts) + ' := by')
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  refine ⟨' + ', '.join('?_' for _ in facts) + '⟩ <;> linarith')
    W('')
    W('/-- The four identifications of a top probability with the bottom')
    W('probability at the complementary string, used to turn the reciprocal rows')
    W('into relations among bottom probabilities alone. -/')
    W('theorem MomentSystem.endpoints {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    W('    ' + ' ∧ '.join(facts[6:]) + ' := by')
    W('  obtain ⟨_, _, _, _, _, _, a1, a2, a3, a4⟩ := h.facts')
    W('  exact ⟨a1, a2, a3, a4⟩')
    W('')
    W('/-- The one probability the moment polytope pins on its own. -/')
    W('theorem MomentSystem.endpoints_pos {%s : Real} (h : MomentSystem %s) :'
      % (allv, allv))
    W('    0 < q9 := by')
    W('  obtain ⟨_, _, _, _, _, a, _, _, _, _⟩ := h.facts')
    W('  linarith')
    W('')
    W('/-! ## Pinning the moment point -/')
    W('')
    W('/-- The three quadratic relations have identically cancelling quadratic')
    W('parts, so together with the linear moment identities they force the')
    W('unique interior point. -/')
    W('theorem pinned {q0 q1 q2 q3 q4 q5 q6 q7 : Real}')
    W('    (f1 : q4 + q5 = 1/6) (f2 : q6 + q7 = 1/6) (f3 : q0 + q1 = 1/3)')
    W('    (f4 : q3 + 1/4 = q4 + q6 + q0) (f5 : q2 + q4 + q6 + q0 = 5/12)')
    W('    (M1 : q0 * q3 = q1 * q2) (M2 : q0 * q5 = q1 * q4)')
    W('    (M3 : q0 * q7 = q1 * q6) :')
    W('    q0 = 1/6 ∧ q5 = 1/12 ∧ q7 = 1/12 := by')
    W('  have e1 : q1 = 1/3 - q0 := by linarith')
    W('  have e5 : q5 = 1/6 - q4 := by linarith')
    W('  have e7 : q7 = 1/6 - q6 := by linarith')
    W('  rw [e5, e1] at M2')
    W('  rw [e7, e1] at M3')
    W('  have h4 : q4 = q0 / 2 := by linear_combination (-3 : Real) * M2')
    W('  have h6 : q6 = q0 / 2 := by linear_combination (-3 : Real) * M3')
    W('  have e3 : q3 = 2 * q0 - 1/4 := by linarith')
    W('  have e2 : q2 = 5/12 - 2 * q0 := by linarith')
    W('  rw [e3, e2, e1] at M1')
    W('  have h0 : q0 = 1/6 := by linear_combination (6/5 : Real) * M1')
    W('  refine ⟨h0, ?_, ?_⟩')
    W('  · rw [e5, h4, h0]; norm_num')
    W('  · rw [e7, h6, h0]; norm_num')
    W('')
    W('/-! ## The Walsh expansions -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    for m in masks:
        inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        for z in sorted(need[m]):
            body = ' '.join('%s star (c y%d) * d z%d'
                            % ('-' if dot(z, S1[t]) else '+', i, t)
                            for i, t in inc).lstrip('+ ')
            W('theorem ex_%s_%s (c d : SS.BitString 6 -> ℂ) :' % (mname[m], zname[z]))
            W('    offSum c d %s %s = %s := by' % (mname[m], zname[z], body))
            W('  unfold offSum')
            W('  rw [incidence_%s]' % mname[m])
            W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(inc) - 1))
              + (', ' if len(inc) > 1 else '') + 'Finset.sum_singleton]')
            W('  rw [' + ', '.join('flip_%s_%d' % (mname[m], t) for _, t in inc) + ']')
            lem = ['sg_%s_%s_%d' % (mname[m], zname[z], t) for _, t in inc]
            if any(dot(z, S1[t]) for _, t in inc):
                lem.append('SixQubit.signMul_true')
            if any(not dot(z, S1[t]) for _, t in inc):
                lem.append('SixQubit.signMul_false')
            W('  simp only [' + ', '.join(lem) + ']')
            W('  try ring')
            W('')
    W('/-! ## The reduced Walsh rows -/')
    W('')
    stmts = []
    for nm, _, _ in WANT:
        e, inc, used, tgtmap = rel[nm]
        stmts.append((nm, ' '.join('%s %s * %s' % ('+' if v > 0 else '-', U(i), V(j))
                                   for (i, j), v in tgtmap.items()).lstrip('+ ')))
    hsig = ''.join(' h%d' % r for r in range(len(hyp)))
    W('/-- Row reduction of the admissible dressings of the six flip masks. -/')
    W('theorem rows (c d : SS.BitString 6 -> ℂ)')
    for r, (m, z) in enumerate(hyp):
        W('    (h%d : offSum c d %s %s = 0)%s'
          % (r, mname[m], zname[z], ' :' if r == len(hyp) - 1 else ''))
    W('    ' + (NL + '      ∧ ').join('%s = 0' % b for _, b in stmts) + ' := by')
    for r, (m, z) in enumerate(hyp):
        W('  rw [ex_%s_%s] at h%d' % (mname[m], zname[z], r))
    for nm, body in stmts:
        e, inc, used, tgtmap = rel[nm]
        W('  have %s : %s = 0 := by' % (nm, body))
        W('    linear_combination ' + ' + '.join(
            '(%s : ℂ) * h%d' % (mu, hyp.index((e, z))) for z, mu in used))
    W('  exact ⟨' + ', '.join(nm for nm, _ in stmts) + '⟩')
    W('')
    W('/-! ## The target product -/')
    W('')
    W('/-- Phase synchronisation collapses the four-incidence flip 100001 to a')
    W('single product; the only input beyond the Walsh rows is that the amplitude')
    W('at `y9` does not vanish. -/')
    W('theorem target_zero (c d : SS.BitString 6 -> ℂ) (nu9 : %s ≠ 0)' % U(9))
    for r, (m, z) in enumerate(hyp):
        W('    (h%d : offSum c d %s %s = 0)%s'
          % (r, mname[m], zname[z], ' :' if r == len(hyp) - 1 else ''))
    W('    %s * %s * %s * %s = 0 := by' % (U(0), U(5), U(7), V(0)))
    W('  obtain ⟨' + ', '.join(('_' if nm == 'K1' else nm) for nm, _ in stmts)
      + '⟩ := rows c d' + hsig)
    W('  have hP0 : %s * (%s * %s - %s * %s) = 0 := by'
      % (U(9), U(1), V(0), U(0), V(1)))
    W('    linear_combination (%s : ℂ) * EA - (%s : ℂ) * EB' % (U(1), U(0)))
    W('  have hP : %s * %s - %s * %s = 0 := by' % (U(1), V(0), U(0), V(1)))
    W('    rcases mul_eq_zero.mp hP0 with hx | hx')
    W('    · exact absurd hx nu9')
    W('    · exact hx')
    W('  have hQ2a : %s * (%s * %s + %s * %s) = 0 := by'
      % (V(0), U(1), U(4), U(0), U(5)))
    W('    linear_combination (%s : ℂ) * E6 + (%s : ℂ) * hP' % (U(0), U(4)))
    W('  have hQ3a : %s * (%s * %s + %s * %s) = 0 := by'
      % (V(0), U(1), U(6), U(0), U(7)))
    W('    linear_combination (%s : ℂ) * E9 + (%s : ℂ) * hP' % (U(0), U(6)))
    W('  linear_combination (-(%s * %s) / 4 : ℂ) * GG' % (U(0), U(1)))
    W('    + ((%s * %s) / 4 : ℂ) * E7 + ((%s * %s) / 4 : ℂ) * E8'
      % (U(1), U(4), U(0), U(5)))
    W('    + ((%s * %s) / 4 : ℂ) * E4 + ((%s * %s) / 4 : ℂ) * E5'
      % (U(1), U(6), U(0), U(7)))
    W('    + (%s / 4 : ℂ) * hQ2a + (%s / 4 : ℂ) * hQ3a' % (U(7), U(5)))
    W('')
    W('/-! ## The no-go -/')
    W('')
    W('/-- **Orbit %d is impossible.** -/' % OID)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
    for r, (m, z) in enumerate(hyp):
        W('    (h%d : offSum c d %s %s = 0)' % (r, mname[m], zname[z]))
    W('    : False := by')
    W('  obtain ⟨' + ', '.join((nm if nm in ('K1', 'E5', 'E8') else '_')
                               for nm, _ in stmts) + '⟩ := rows c d' + hsig)
    W('  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := hm.facts')
    for nm, src, i1, j1, i2, j2, tgt in [
            ('M1', 'K1', 1, 2, 3, 0, (0, 3, 1, 2)),
            ('M2', 'E5', 1, 4, 5, 0, (0, 5, 1, 4)),
            ('M3', 'E8', 1, 6, 7, 0, (0, 7, 1, 6))]:
        ta, tb, tc, td = tgt
        W('  have %s : %s * %s = %s * %s := by' % (nm, P(ta), P(tb), P(tc), P(td)))
        W('    have hx : %s * %s = -(%s * %s) := by linear_combination %s'
          % (U(i1), V(j1), U(i2), V(j2), src))
        W('    have hy : %s * Complex.normSq (%s)' % (P(i1), V(j1)))
        W('        = %s * Complex.normSq (%s) := by' % (P(i2), V(j2)))
        W('      simpa [Complex.normSq_mul] using congrArg Complex.normSq hx')
        W('    rw [f%d, f10] at hy' % (7 + [2, 4, 6].index(j1)))
        W('    linear_combination (-1 : Real) * hy')
    W('  obtain ⟨p0, p5, p7⟩ := pinned f1 f2 f3 f4 f5 M1 M2 M3')
    for nm, i, src in [('nu0', 0, 'p0'), ('nu5', 5, 'p5'), ('nu7', 7, 'p7'),
                       ('nu9', 9, 'f6')]:
        W('  have %s : %s ≠ 0 := by' % (nm, U(i)))
        W('    intro hzero')
        W('    have hk : c y%d = 0 := by simpa using congrArg star hzero' % i)
        W('    rw [hk, Complex.normSq_zero] at %s' % src)
        W('    norm_num at %s' % src)
    W('  have nv0 : %s ≠ 0 := by' % V(0))
    W('    intro hzero')
    W('    rw [hzero, Complex.normSq_zero, p0] at f10')
    W('    norm_num at f10')
    W('  have hfin := target_zero c d nu9' + hsig)
    W('  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero nu0 nu5) nu7) nv0) hfin')
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % OID)
    return NL.join(L) + NL


if __name__ == '__main__':
    src = emit()
    p = os.path.join(REPO, 'SixQubit', 'Orbit%d.lean' % OID)
    io.open(p, 'w', encoding='utf-8').write(src)
    print('%s : %d lines' % (p, src.count(NL)))
