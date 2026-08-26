"""Emit the kernel-only Lean modules for moment orbits 49 and 51.

Both orbits have complementary fibers, so the top fiber is indexed by bitwise
complement.  The route is division free throughout:

  orbit 49 -- the eight reciprocal relations against index 8 turn each rank-one
             mask equation into a pure `c`-quadric after multiplying by
             `star (c y8)`; taking `normSq` pins the whole polytope to the point
             1/12, and the mixed pair triangle closes it.

  orbit 51 -- the two weight-one kernels pin the polytope directly; the pair
             {6,7} carries mass 1/6, which forces the synchronisation
             `star (c y8) * d z9 = star (c y9) * d z8` without any division;
             then the same mixed pair triangle closes it.

Every coefficient below is solved for by exact linear algebra over the sign
matrix of the admissible dressings; nothing is typed by hand.

Run:  python tools/run.py generators/gen4951.py
"""
import io
import os
from itertools import combinations

from sympy import Matrix, Rational, zeros

from orbit import fiber
from kl import dressings_full
from scan import bits, xor, dot

NL = chr(10)
BOOL = {'0': 'false', '1': 'true '}

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.abspath(os.path.join(HERE, '..', '..', 'SixQubit'))

PAPER = {
    49: ['000000', '000110', '001001', '001111', '010001',
         '010111', '100001', '100111', '111010', '111100'],
    51: ['000000', '000110', '001001', '001111', '011010',
         '011100', '101010', '101100', '110001', '110111'],
}
ANGLES = {49: [1, 1, 1, 3, 3, 5], 51: [1, 1, 2, 3, 3, 4]}


def comp(s):
    return ''.join('0' if ch == '1' else '1' for ch in s)


def ind(s, i):
    return 1 if s[i] == '1' else 0


# ----------------------------------------------------------------- mask specs
# (mask, [(relation name, {(bottom index, top index): coefficient})])
SPEC = {
    49: [('000101', [('rec0', {(8, 0): 1, (0, 8): 1})]),
         ('000011', [('rec1', {(8, 1): 1, (1, 8): 1})]),
         ('001100', [('rec2', {(8, 2): 1, (2, 8): 1})]),
         ('001010', [('rec3', {(8, 3): 1, (3, 8): 1})]),
         ('010100', [('rec4', {(8, 4): 1, (4, 8): 1})]),
         ('010010', [('rec5', {(8, 5): 1, (5, 8): 1})]),
         ('100100', [('rec6', {(8, 6): 1, (6, 8): 1})]),
         ('100010', [('rec7', {(8, 7): 1, (7, 8): 1})]),
         ('110000', [('mk1', 'all')]),
         ('101000', [('mk2', 'all')]),
         ('100001', [('mk3', 'all')]),
         ('011000', [('mk4', 'all')])],
    51: [('001000', [('rA1', {(9, 0): 1, (0, 9): -1}),
                     ('rA2', {(8, 1): 1, (0, 9): 1}),
                     ('rA3', {(1, 8): 1, (0, 9): 1})]),
         ('000001', [('rB1', {(9, 2): 1, (2, 9): -1}),
                     ('rB2', {(8, 3): 1, (2, 9): 1}),
                     ('rB3', {(3, 8): 1, (2, 9): 1})]),
         ('110000', [('rM', 'all')]),
         ('100100', [('rC1', {(8, 6): 1, (6, 8): 1}),
                     ('rC2', {(9, 7): 1, (7, 9): 1})]),
         ('100010', [('rD1', {(9, 6): 1, (6, 9): 1}),
                     ('rD2', {(8, 7): 1, (7, 8): 1})])],
}


def build(oid):
    """Fibers, incidences, chosen dressings and exact combination coefficients."""
    B = PAPER[oid]
    T = [comp(x) for x in B]
    assert sorted(B) == sorted(fiber(ANGLES[oid], 6, 0)), 'bottom fiber mismatch'
    assert sorted(T) == sorted(fiber(ANGLES[oid], 6, 2)), 'top fiber mismatch'

    masks = []
    for e, targets in SPEC[oid]:
        inc = sorted(((B.index(xor(y, e)), t) for t, y in enumerate(T)
                      if xor(y, e) in B), key=lambda p: p[1])
        cand = dressings_full(e)
        rows = [[Rational((-1) ** dot(z, T[t])) for (_s, t) in inc] for z in cand]
        # target vectors over the incidence order
        tvs = []
        for name, spec in targets:
            if spec == 'all':
                vec = [Rational(1)] * len(inc)
            else:
                vec = [Rational(spec.get(p, 0)) for p in inc]
            tvs.append((name, vec))
        # add independent sign rows until every target lies in their span
        chosen, rank = [], 0
        for k in range(len(cand)):
            if all(solve_in(chosen, rows, v) is not None for _n, v in tvs):
                break
            nr = Matrix([rows[j] for j in chosen + [k]]).rank()
            if nr > rank:
                chosen.append(k)
                rank = nr
        assert all(solve_in(chosen, rows, v) is not None for _n, v in tvs), e
        combos = []
        for name, vec in tvs:
            co = solve_in(chosen, rows, vec)
            assert co is not None, (e, name)
            combos.append((name, vec, co))
        # drop dressings that no target actually uses
        used = [j for j, _k in enumerate(chosen)
                if any(co[j] != 0 for _n, _v, co in combos)]
        chosen = [chosen[j] for j in used]
        combos = [(n, v, [co[j] for j in used]) for n, v, co in combos]
        masks.append({'e': e, 'inc': inc,
                      'zs': [cand[k] for k in chosen], 'combos': combos})
    return B, T, masks


def solve_in(chosen, rows, target):
    """Exact rational coefficients expressing `target` in the chosen sign rows."""
    if not chosen:
        return None if any(t != 0 for t in target) else []
    A = Matrix([rows[k] for k in chosen]).T
    b = Matrix(target)
    aug = A.row_join(b)
    R, piv = aug.rref()
    if A.cols in piv:
        return None
    sol = zeros(A.cols, 1)
    for r, pcol in enumerate(piv):
        sol[pcol] = R[r, A.cols]
    if A * sol != b:
        return None
    return [Rational(x) for x in sol]


def rat(x):
    x = Rational(x)
    if x.q == 1:
        return str(x.p)
    return '%d/%d' % (x.p, x.q)


def cxlin(terms):
    """Render a `linear_combination` argument list."""
    out = []
    for coeff, name in terms:
        out.append('%s(%s) * %s' % ('' if not out else '+ ', coeff, name))
    return (NL + '      ').join(out)


def emit(oid, B, T, masks, body):
    n = len(B)
    qs = ' '.join('q%d' % r for r in range(n))
    rs = ' '.join('r%d' % r for r in range(n))
    allv = qs + ' ' + rs
    L = []
    W = L.append

    zall, zname = [], {}
    for m in masks:
        for z in m['zs']:
            if z not in zname:
                zname[z] = 'w%d' % len(zall)
                zall.append(z)

    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('import SixQubit.Triangle')
    W('')
    for line in body['doc']:
        W(line)
    W('')
    W('namespace SixQubit.Orbit%d' % oid)
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
    for r, x in enumerate(B):
        W('def y%d : SS.BitString 6 := bs %s  -- %s'
          % (r, ' '.join(BOOL[ch] for ch in x), x))
    W('')
    for r, y in enumerate(T):
        W('def z%d : SS.BitString 6 := bs %s  -- %s'
          % (r, ' '.join(BOOL[ch] for ch in y), y))
    W('')
    W('def S0 : Finset (SS.BitString 6) := {%s}'
      % ', '.join('y%d' % r for r in range(n)))
    W('def S1 : Finset (SS.BitString 6) := {%s}'
      % ', '.join('z%d' % r for r in range(n)))
    W('')
    W('def av : Fin 6 -> ZMod 6 := ![%s]' % ', '.join(map(str, ANGLES[oid])))
    W('')
    W('theorem S0_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = 0) = S0 := by')
    W('  decide')
    W('')
    W('theorem S1_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = 2) = S1 := by')
    W('  decide')
    W('')
    W('/-! ## Flip masks, dressings, incidences and signs -/')
    W('')
    for k, m in enumerate(masks):
        W('def ef%d : SS.BitString 6 := bs %s  -- %s'
          % (k, ' '.join(BOOL[ch] for ch in m['e']), m['e']))
    W('')
    for z in zall:
        W('def %s : SS.BitString 6 := bs %s  -- %s'
          % (zname[z], ' '.join(BOOL[ch] for ch in z), z))
    W('')
    for k, m in enumerate(masks):
        W('theorem incidence_ef%d :' % k)
        W('    S1.filter (fun y => SS.bxor y ef%d ∈ S0) = {%s} := by decide'
          % (k, ', '.join('z%d' % t for _s, t in m['inc'])))
        for s, t in m['inc']:
            W('theorem flip_ef%d_z%d : SS.bxor z%d ef%d = y%d := by decide'
              % (k, t, t, k, s))
    W('')
    sgs = []
    for m in masks:
        for z in m['zs']:
            for _s, t in m['inc']:
                if (zname[z], t) not in sgs:
                    sgs.append((zname[z], t))
                    W('theorem sg_%s_z%d : SS.bdot %s z%d = %s := by decide'
                      % (zname[z], t, zname[z], t,
                         'true' if dot(z, T[t]) else 'false'))
    W('')
    W('/-! ## The moment system -/')
    W('')
    W('/-- The two normalizations, the twenty-one moment equalities, and the')
    W('nonnegativity of every probability. -/')
    W('structure MomentSystem (%s : Real) : Prop where' % allv)
    W('  n0 : %s = 1' % ' + '.join('q%d' % r for r in range(n)))
    W('  n1 : %s = 1' % ' + '.join('r%d' % r for r in range(n)))
    idx = [(i,) for i in range(6)] + list(combinations(range(6), 2))
    for tup in idx:
        lhs = [r for r in range(n) if all(B[r][j] == '1' for j in tup)]
        rhs = [r for r in range(n) if all(T[r][j] == '1' for j in tup)]
        W('  m%s : %s = %s'
          % (''.join(str(j + 1) for j in tup),
             ' + '.join('q%d' % r for r in lhs) or '0',
             ' + '.join('r%d' % r for r in rhs) or '0'))
    W('')
    for r in range(n):
        W('  nq%d : 0 ≤ q%d' % (r, r))
    for r in range(n):
        W('  nr%d : 0 ≤ r%d' % (r, r))
    W('')
    fields = (['n0', 'n1'] + ['m%s' % ''.join(str(j + 1) for j in tup) for tup in idx]
              + ['nq%d' % r for r in range(n)] + ['nr%d' % r for r in range(n)])
    obtain = '  obtain ⟨' + ', '.join(fields) + '⟩ := h'
    for thm in body['moment'](allv, obtain):
        W(thm)
    W('')
    W('/-! ## The Walsh expansions -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    for k, m in enumerate(masks):
        inc = m['inc']
        for z in m['zs']:
            nm = zname[z]
            terms = ' '.join('%s star (c y%d) * d z%d'
                             % ('-' if dot(z, T[t]) else '+', s, t)
                             for s, t in inc).lstrip('+ ')
            W('theorem ex_ef%d_%s (c d : SS.BitString 6 -> ℂ) :' % (k, nm))
            W('    offSum c d ef%d %s = %s := by' % (k, nm, terms))
            W('  unfold offSum')
            W('  rw [incidence_ef%d]' % k)
            W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(inc) - 1))
              + (', ' if len(inc) > 1 else '') + 'Finset.sum_singleton]')
            W('  rw [' + ', '.join('flip_ef%d_z%d' % (k, t) for _s, t in inc) + ']')
            lem = ['sg_%s_z%d' % (nm, t) for _s, t in inc]
            if any(dot(z, T[t]) for _s, t in inc):
                lem.append('SixQubit.signMul_true')
            if any(not dot(z, T[t]) for _s, t in inc):
                lem.append('SixQubit.signMul_false')
            W('  simp only [' + ', '.join(lem) + ']')
            W('  try ring')
            W('')
    W('/-! ## The no-go -/')
    W('')
    W('/-- **Orbit %d is impossible.** -/' % oid)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n)) + ')')
    hyp, hi = [], 0
    for k, m in enumerate(masks):
        for z in m['zs']:
            W('    (h%d : offSum c d ef%d %s = 0)' % (hi, k, zname[z]))
            hyp.append((hi, k, zname[z]))
            hi += 1
    W('    : False := by')
    for i, k, nm in hyp:
        W('  rw [ex_ef%d_%s] at h%d' % (k, nm, i))
    # the derived relations
    hi = 0
    for m in masks:
        base = hi
        hi += len(m['zs'])
        for name, vec, co in m['combos']:
            terms = ' '.join('%s star (c y%d) * d z%d'
                             % ('+' if v > 0 else '-', s, t)
                             for (s, t), v in zip(m['inc'], vec) if v != 0)
            W('  have %s : %s = 0 := by' % (name, terms.lstrip('+ ')))
            W('    linear_combination ' + ' '.join(
                '%s(%s : ℂ) * h%d' % ('' if j == 0 else '+ ', rat(co[j]), base + j)
                for j in range(len(co)) if co[j] != 0).lstrip('+ '))
    for line in body['endgame']:
        W(line)
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % oid)
    return NL.join(L) + NL


# --------------------------------------------------------------- orbit bodies
def moment49(allv, obtain):
    return [
        '/-- The top probability at the anchor index 8 is pinned by the moment',
        'polytope alone. -/',
        'theorem MomentSystem.top8 {%s : Real}' % allv,
        '    (h : MomentSystem %s) : r8 = 1/6 := by' % allv,
        obtain,
        '  linarith',
        '',
        '/-- With the three quadratic consequences of the rank-one masks the whole',
        'polytope collapses to the single point `1/12`. -/',
        'theorem MomentSystem.pinned {%s : Real}' % allv,
        '    (h : MomentSystem %s)' % allv,
        '    (e1 : q0 * q3 = q1 * q2)',
        '    (e2 : q0 * q5 = q1 * q4)',
        '    (e3 : q0 * q7 = q1 * q6) :',
        '    q1 = 1/12 ∧ q2 = 1/12 ∧ q4 = 1/12 := by',
        obtain,
        '  have hq1 : q1 = 1/6 - q0 := by linarith',
        '  have hq3 : q3 = 1/6 - q2 := by linarith',
        '  have hq5 : q5 = 1/6 - q4 := by linarith',
        '  have hq7 : q7 = 1/6 - q6 := by linarith',
        '  rw [hq1, hq3] at e1',
        '  rw [hq1, hq5] at e2',
        '  rw [hq1, hq7] at e3',
        '  have t1 : q0 = q2 := by linear_combination (6 : Real) * e1',
        '  have t2 : q0 = q4 := by linear_combination (6 : Real) * e2',
        '  have t3 : q0 = q6 := by linear_combination (6 : Real) * e3',
        '  refine ⟨?_, ?_, ?_⟩ <;> linarith',
    ]


def moment51(allv, obtain):
    return [
        '/-- The two weight-one kernel relations pin the polytope: four of the ten',
        'bottom probabilities become `1/12` and the anchor pair becomes `1/6`. -/',
        'theorem MomentSystem.pinned {%s : Real}' % allv,
        '    (h : MomentSystem %s)' % allv,
        '    (e1 : q1 * r8 = q0 * r9)',
        '    (e2 : q3 * r8 = q2 * r9) :',
        '    q1 = 1/12 ∧ q2 = 1/12 ∧ q8 = 1/6 ∧ r8 = 1/6 ∧ r9 = 1/6',
        '      ∧ r6 + r7 = 1/6 := by',
        obtain,
        '  have hq1 : q1 = 1/6 - q0 := by linarith',
        '  have hq3 : q3 = 1/6 - q2 := by linarith',
        '  have h8 : r8 = 1/3 - q0 - q2 := by linarith',
        '  have h9 : r9 = q0 + q2 := by linarith',
        '  rw [hq1, h8, h9] at e1',
        '  rw [hq3, h8, h9] at e2',
        '  have t1 : 9 * q0 + 3 * q2 = 1 := by linear_combination (-18 : Real) * e1',
        '  have t2 : 3 * q0 + 9 * q2 = 1 := by linear_combination (-18 : Real) * e2',
        '  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith',
    ]


U = lambda i: 'star (c y%d)' % i
V = lambda i: 'd z%d' % i


def star_to_c(name, out, pairs):
    """Conjugate a relation `star .. * star .. + .. = 0` into plain `c`s."""
    lhs = ' + '.join('c y%d * c y%d' % (i, j) for i, j in pairs)
    return ['  have %s : %s = 0 := by' % (out, lhs),
            '    have hst := congrArg star %s' % name,
            '    simp only [star_add, star_mul, star_star, star_zero] at hst',
            '    linear_combination hst']


def normsq_of(name, out, i, j, k, l):
    return ['  have %s : Complex.normSq (c y%d) * Complex.normSq (c y%d)' % (out, i, j),
            '      = Complex.normSq (c y%d) * Complex.normSq (c y%d) := by' % (k, l),
            '    have hne : c y%d * c y%d = -(c y%d * c y%d) := by linear_combination %s'
            % (i, j, k, l, name),
            '    have hsq := congrArg Complex.normSq hne',
            '    simpa [Complex.normSq_mul] using hsq']


def endgame49():
    L = []
    W = L.append
    W('  have hz8 : d z8 ≠ 0 :=')
    W('    Complex.normSq_pos.mp (by rw [hm.top8]; norm_num)')
    quad = [('mk1', 'P1', (0, 3), (1, 2), [(8, 3, 'rec0'), (8, 2, 'rec1'),
                                           (8, 1, 'rec2'), (8, 0, 'rec3')]),
            ('mk2', 'P2', (0, 5), (1, 4), [(8, 5, 'rec0'), (8, 4, 'rec1'),
                                           (8, 1, 'rec4'), (8, 0, 'rec5')]),
            ('mk3', 'P3', (2, 5), (3, 4), [(8, 5, 'rec2'), (8, 4, 'rec3'),
                                           (8, 3, 'rec4'), (8, 2, 'rec5')]),
            ('mk4', 'P4', (0, 7), (1, 6), [(8, 7, 'rec0'), (8, 6, 'rec1'),
                                           (8, 1, 'rec6'), (8, 0, 'rec7')])]
    for mk, P, (a, b), (x, y), recs in quad:
        expr = '%s * %s + %s * %s' % (U(a), U(b), U(x), U(y))
        W('  have %s : %s = 0 := by' % (P, expr))
        W('    have key : (%s) * %s = 0 := by' % (expr, V(8)))
        parts = ['(-%s / 2) * %s' % (U(8), mk)]
        for _e, co, rc in recs:
            parts.append('+ (%s / 2) * %s' % (U(co), rc))
        W('      linear_combination ' + (NL + '        ').join(
            [parts[0]] + [' '.join(parts[1:])]))
        W('    exact (mul_eq_zero.mp key).resolve_right hz8')
    for P, Q, pairs in [('P1', 'Q1', [(0, 3), (1, 2)]),
                        ('P2', 'Q2', [(0, 5), (1, 4)]),
                        ('P3', 'Q3', [(2, 5), (3, 4)]),
                        ('P4', 'Q4', [(0, 7), (1, 6)])]:
        L.extend(star_to_c(P, Q, pairs))
    L.extend(normsq_of('Q1', 'E1', 0, 3, 1, 2))
    L.extend(normsq_of('Q2', 'E2', 0, 5, 1, 4))
    L.extend(normsq_of('Q4', 'E3', 0, 7, 1, 6))
    W('  obtain ⟨g1, g2, g4⟩ := hm.pinned E1 E2 E3')
    W('  exact SixQubit.Triangle.pair_contradiction_of_normSq Q2 Q3 Q1')
    W('    (by rw [g1]; norm_num) (by rw [g2]; norm_num) (by rw [g4]; norm_num)')
    return L


def endgame51():
    L = []
    W = L.append
    W('  have E1 : Complex.normSq (c y1) * Complex.normSq (d z8)')
    W('      = Complex.normSq (c y0) * Complex.normSq (d z9) := by')
    W('    have hne : star (c y1) * d z8 = -(star (c y0) * d z9) := by')
    W('      linear_combination rA3')
    W('    have hsq := congrArg Complex.normSq hne')
    W('    simpa [Complex.normSq_mul] using hsq')
    W('  have E2 : Complex.normSq (c y3) * Complex.normSq (d z8)')
    W('      = Complex.normSq (c y2) * Complex.normSq (d z9) := by')
    W('    have hne : star (c y3) * d z8 = -(star (c y2) * d z9) := by')
    W('      linear_combination rB3')
    W('    have hsq := congrArg Complex.normSq hne')
    W('    simpa [Complex.normSq_mul] using hsq')
    W('  obtain ⟨g1, g2, g8, gr8, gr9, g67⟩ := hm.pinned E1 E2')
    W('  have hz8 : d z8 ≠ 0 := Complex.normSq_pos.mp (by rw [gr8]; norm_num)')
    W('  have hz9 : d z9 ≠ 0 := Complex.normSq_pos.mp (by rw [gr9]; norm_num)')
    W('  have hc8 : star (c y8) ≠ 0 :=')
    W('    star_ne_zero.mpr (Complex.normSq_pos.mp (by rw [g8]; norm_num))')
    W('  have kw6 : d z6 * (star (c y8) * d z9 - star (c y9) * d z8) = 0 := by')
    W('    linear_combination (d z9) * rC1 - (d z8) * rD1')
    W('  have kw7 : d z7 * (star (c y8) * d z9 - star (c y9) * d z8) = 0 := by')
    W('    linear_combination (d z9) * rD2 - (d z8) * rC2')
    W('  have hW : star (c y8) * d z9 - star (c y9) * d z8 = 0 := by')
    W('    rcases eq_or_ne (d z6) 0 with h6 | h6')
    W('    · have h7 : d z7 ≠ 0 := by')
    W('        refine Complex.normSq_pos.mp ?_')
    W('        have hz6 : Complex.normSq (d z6) = 0 := by rw [h6]; simp')
    W('        have hnn := Complex.normSq_nonneg (d z7)')
    W('        linarith')
    W('      exact (mul_eq_zero.mp kw7).resolve_left h7')
    W('    · exact (mul_eq_zero.mp kw6).resolve_left h6')
    W('  have G1 : star (c y0) * star (c y9) + star (c y1) * star (c y8) = 0 := by')
    W('    have key : (star (c y0) * star (c y9) + star (c y1) * star (c y8))')
    W('        * d z8 = 0 := by')
    W('      linear_combination (star (c y8)) * rA3 - (star (c y0)) * hW')
    W('    exact (mul_eq_zero.mp key).resolve_right hz8')
    W('  have G2 : star (c y2) * star (c y9) + star (c y3) * star (c y8) = 0 := by')
    W('    have key : (star (c y2) * star (c y9) + star (c y3) * star (c y8))')
    W('        * d z8 = 0 := by')
    W('      linear_combination (star (c y8)) * rB3 - (star (c y2)) * hW')
    W('    exact (mul_eq_zero.mp key).resolve_right hz8')
    W('  have G3 : star (c y0) * star (c y3) + star (c y1) * star (c y2) = 0 := by')
    W('    have key : (star (c y0) * star (c y3) + star (c y1) * star (c y2))')
    W('        * (star (c y8) * d z9) = 0 := by')
    W('      linear_combination (star (c y8) * star (c y9) / 2) * rM')
    W('        - (star (c y8) * star (c y3) / 2) * rA1')
    W('        - (star (c y9) * star (c y2) / 2) * rA2')
    W('        + (star (c y9) * star (c y2) / 2) * rA3')
    W('        - (star (c y8) * star (c y1) / 2) * rB1')
    W('        - (star (c y9) * star (c y0) / 2) * rB2')
    W('        + (star (c y9) * star (c y0) / 2) * rB3')
    W('        + ((star (c y0) * star (c y3) + star (c y1) * star (c y2)) / 2) * hW')
    W('    exact (mul_eq_zero.mp key).resolve_right (mul_ne_zero hc8 hz9)')
    L.extend(star_to_c('G1', 'H1', [(0, 9), (1, 8)]))
    L.extend(star_to_c('G2', 'H2', [(2, 9), (3, 8)]))
    L.extend(star_to_c('G3', 'H3', [(0, 3), (1, 2)]))
    W('  exact SixQubit.Triangle.pair_contradiction_of_normSq H1 H2 H3')
    W('    (by rw [g1]; norm_num) (by rw [g2]; norm_num) (by rw [g8]; norm_num)')
    return L


DOC49 = """/-!
# Six-qubit no-go for moment orbit 49

Orbit 49 of `six_qubit_sslp.tex`: q = 6, angle vector a = (1, 1, 1, 3, 3, 5),
residues 0 and 2.  The two fibers are complementary, so the top fiber is
indexed by bitwise complement of the bottom one.

The eight weight-two masks that pair an index `i <= 7` with the anchor index 8
each isolate a *reciprocal* relation `star (c y8) * d zi + star (c yi) * d z8 = 0`.
Four further masks have a single rank-one row, for instance

```
star (c y3) * d z0 + star (c y2) * d z1 + star (c y1) * d z2 + star (c y0) * d z3 = 0 .
```

The paper divides by amplitudes to introduce phase ratios `rho_i = d_i / conj(c_i)`
and propagates a uniform phase.  This module never divides.  Multiplying a
rank-one row by `star (c y8)` and substituting the four reciprocal relations
gives, identically,

```
star (c y8) * (row)  =  -2 * (d z8) * (star (c y0) * star (c y3) + star (c y1) * star (c y2)) ,
```

and the moment polytope pins `normSq (d z8) = 1/6`, so the quadric factor
vanishes.  Conjugating turns it into `c y0 * c y3 + c y1 * c y2 = 0`; taking
`normSq` turns the four such quadrics into the three moment equations
`p0 p3 = p1 p2`, `p0 p5 = p1 p4`, `p0 p7 = p1 p6`, which collapse the whole
three-dimensional polytope to the single point where `p0 = ... = p7 = 1/12`.
With every amplitude nonzero, `SixQubit.Triangle.pair_contradiction_of_normSq`
closes the resulting mixed pair triangle.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/"""

DOC51 = """/-!
# Six-qubit no-go for moment orbit 51

Orbit 51 of `six_qubit_sslp.tex`: q = 6, angle vector a = (1, 1, 2, 3, 3, 4),
residues 0 and 2.  The two fibers are complementary, so the top fiber is
indexed by bitwise complement of the bottom one.

The weight-one masks `X_3` and `X_6` each have four incidences and rank three,
so each pins its incidence vector to a one-dimensional kernel spanned by
`(1, -1, -1, 1)`.  Taking `normSq` of the two resulting relations gives the two
moment equations `p1 r8 = p0 r9` and `p3 r8 = p2 r9`, which collapse the
three-dimensional polytope to `p0 = p1 = p2 = p3 = 1/12`, `p8 = p9 = 1/6`.

The paper then divides by amplitudes to synchronize the phase ratios of the two
anchors.  This module never divides.  The masks `e1+e4` and `e1+e5` give four
reciprocal relations on the pair `{6, 7}`, and eliminating between them gives
identically

```
d z6 * (star (c y8) * d z9 - star (c y9) * d z8) = 0 ,
d z7 * (star (c y8) * d z9 - star (c y9) * d z8) = 0 ;
```

the moment system forces `normSq (d z6) + normSq (d z7) = 1/6`, so one of the
two factors is nonzero and the synchronisation `star (c y8) * d z9 = star (c y9) * d z8`
holds outright.  With it, the two kernel relations and the rank-one mask
`e1+e2` become the three pure quadrics `c0 c9 + c1 c8 = 0`, `c2 c9 + c3 c8 = 0`,
`c0 c3 + c1 c2 = 0`, and
`SixQubit.Triangle.pair_contradiction_of_normSq` closes the mixed pair triangle.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/"""

BODIES = {
    49: {'doc': DOC49.split(NL), 'moment': moment49, 'endgame': None},
    51: {'doc': DOC51.split(NL), 'moment': moment51, 'endgame': None},
}

if __name__ == '__main__':
    BODIES[49]['endgame'] = endgame49()
    BODIES[51]['endgame'] = endgame51()
    for oid in (49, 51):
        B, T, masks = build(oid)
        txt = emit(oid, B, T, masks, BODIES[oid])
        path = os.path.join(OUT, 'Orbit%d.lean' % oid)
        io.open(path, 'w', encoding='utf-8', newline=NL).write(txt)
        print('wrote %s  (%d lines, %d masks, %d dressed rows)'
              % (path, len(txt.splitlines()), len(masks),
                 sum(len(m['zs']) for m in masks)))
