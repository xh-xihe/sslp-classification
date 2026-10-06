"""Generate SixQubit/Orbit17.lean from the verified orbit data.

Orbit 17 = (q, m, a) = (4, 2, (1,1,1,1,1,1)), residues 0 and 2.  The two fibers
are the Hamming shells {wt 0, 4} and {wt 2, 6}; weight-two strings are the edges
of K_6 and weight-four strings their complements.

For every edge mask f the two admissible dressings z = 0 and z = e_i (i in f)
split the eight incidences into the anchor flip and the pair flip; eliminating
the top amplitudes against the anchor relations turns the pair flip into the
four-set hafnian equation.  `SixQubit.Hafnian` finishes.
"""
from itertools import combinations

from orbit import fiber
from scan import bits, xor

N = 6
A = [1] * 6
S0 = fiber(A, 4, 0)
S1 = fiber(A, 4, 2)
assert len(S0) == 16 and len(S1) == 16
V = list(range(6))
EDGES = list(combinations(V, 2))
FOURS = list(combinations(V, 4))


def estr(e):
    return ''.join('1' if i in e else '0' for i in range(6))


def cstr(e):
    return ''.join('0' if i in e else '1' for i in range(6))


i0 = {s: k for k, s in enumerate(S0)}
i1 = {s: k for k, s in enumerate(S1)}
EMPTY = i0['000000']
FULL = i1['111111']
assert EMPTY == 0 and FULL == 15


def bot(e):
    """index in S0 of the weight-four string complementary to edge e"""
    return i0[cstr(e)]


def top(e):
    return i1[estr(e)]


def boolstr(s):
    return ' '.join('true ' if ch == '1' else 'false' for ch in s).rstrip()


def ename(e):
    return 'e%d%d' % e


def C(e):
    return 'star (c y%d)' % bot(e)


L = []
W = L.append

W('import Mathlib')
W('')
W('import SS.FullKL')
W('import SixQubit.Common')
W('import SixQubit.Hafnian')
W('')
W('/-!')
W('# Six-qubit no-go for moment orbit 17')
W('')
W('Orbit 17 of `six_qubit_sslp.tex`: q = 4, angle vector')
W('a = (1, 1, 1, 1, 1, 1), residues 0 and 2.')
W('')
W('The two fibers are the Hamming shells `{wt 0, 4}` and `{wt 2, 6}`.  Index the')
W('weight-two strings by the edges of `K_6`; the weight-four strings are their')
W('complements.  Writing `a` for the bottom anchor amplitude, `b` for the top')
W('anchor amplitude, `c_e` for the bottom edge amplitudes and `d_e` for the top')
W('ones, the moment polytope forces')
W('')
W('```')
W('|a|^2 = |b|^2 = 1/4 ,     sum_{e ni v} |c_e|^2 = 1/4   (v = 0, ..., 5) ,')
W('```')
W('')
W('a scaled fractional perfect matching of `K_6`.')
W('')
W('Every edge mask `f` has exactly eight incidences and exactly two independent')
W('dressings, `z = 0` and `z = e_i` with `i` in `f`.  Their half sum and half')
W('difference are the *pair flip* and the *anchor flip*')
W('')
W('```')
W('sum_{g subset V - f} conj(c_{V-f-g}) d_g = 0 ,   conj(a) d_f + conj(c_f) b = 0 .')
W('```')
W('')
W('Multiplying the pair flip by `conj(a)` and substituting the anchor flips')
W('eliminates every top amplitude at once and leaves `2 b` times the four-set')
W('hafnian.  Since `|b|^2 = 1/4` the fifteen hafnian equations hold, and')
W('`SixQubit.Hafnian.no_go` shows they are incompatible with the fractional')
W('perfect matching.  No division is used anywhere: the phase ratio')
W('`lambda = -b / conj(a)` of the paper never appears.')
W('')
W('Everything computational is decided by the Lean kernel; `native_decide`')
W('is not used.')
W('-/')
W('')
W('namespace SixQubit.Orbit17')
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
for k, s in enumerate(S0):
    W('def y%d : SS.BitString 6 := bs %-40s -- %s' % (k, boolstr(s), s))
W('')
for k, s in enumerate(S1):
    W('def z%d : SS.BitString 6 := bs %-40s -- %s' % (k, boolstr(s), s))
W('')
W('def S0 : Finset (SS.BitString 6) := {%s}' % ', '.join('y%d' % k for k in range(16)))
W('def S1 : Finset (SS.BitString 6) := {%s}' % ', '.join('z%d' % k for k in range(16)))
W('')
W('def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 1, 1, 1]')
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
W('/-! ## The fifteen edge masks and their dressings -/')
W('')
for e in EDGES:
    W('def %s : SS.BitString 6 := bs %-40s -- %s' % (ename(e), boolstr(estr(e)), estr(e)))
W('')
W('def wz : SS.BitString 6 := bs %-40s -- 000000' % boolstr('000000'))
for i in range(6):
    s = ''.join('1' if k == i else '0' for k in range(6))
    W('def wp%d : SS.BitString 6 := bs %-40s -- %s' % (i, boolstr(s), s))
W('')
W('/-! ## The off-diagonal layer -/')
W('')
W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
W('')

INC = {}
for e in EDGES:
    inc = []
    for t, y in enumerate(S1):
        if xor(y, estr(e)) in i0:
            inc.append((t, i0[xor(y, estr(e))]))
    assert len(inc) == 8, (e, inc)
    INC[e] = inc

for e in EDGES:
    inc = INC[e]
    nm = ename(e)
    W('theorem inc_%s : S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
      % (nm, nm, ', '.join('z%d' % t for (t, _) in inc)))
    for n, (t, s) in enumerate(inc):
        W('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide' % (nm, n, t, nm, s))
    # dressing z = 0
    for n, (t, s) in enumerate(inc):
        W('theorem sgz_%s_%d : SS.bdot wz z%d = false := by decide' % (nm, n, t))
    terms = ' + '.join('star (c y%d) * d z%d' % (s, t) for (t, s) in inc)
    W('theorem ex_%s_z (c d : SS.BitString 6 -> ℂ) :' % nm)
    W('    offSum c d %s wz = %s := by' % (nm, terms))
    W('  unfold offSum')
    W('  rw [inc_%s]' % nm)
    W('  rw [%s, Finset.sum_singleton]' % ', '.join(['Finset.sum_insert (by decide)'] * 7))
    W('  rw [%s]' % ', '.join('flip_%s_%d' % (nm, n) for n in range(8)))
    W('  simp only [%s, SixQubit.signMul_false]'
      % ', '.join('sgz_%s_%d' % (nm, n) for n in range(8)))
    W('  try ring')
    # dressing z = e_i, i the smaller endpoint
    i = e[0]
    sg = [S1[t][i] == '1' for (t, _) in inc]
    for n, (t, s) in enumerate(inc):
        W('theorem sgp_%s_%d : SS.bdot wp%d z%d = %s := by decide'
          % (nm, n, i, t, 'true' if sg[n] else 'false'))
    parts = []
    for n, (t, s) in enumerate(inc):
        parts.append(('- ' if sg[n] else ('+ ' if n else '')) + 'star (c y%d) * d z%d' % (s, t))
    W('theorem ex_%s_p (c d : SS.BitString 6 -> ℂ) :' % nm)
    W('    offSum c d %s wp%d = %s := by' % (nm, i, ' '.join(parts)))
    W('  unfold offSum')
    W('  rw [inc_%s]' % nm)
    W('  rw [%s, Finset.sum_singleton]' % ', '.join(['Finset.sum_insert (by decide)'] * 7))
    W('  rw [%s]' % ', '.join('flip_%s_%d' % (nm, n) for n in range(8)))
    W('  simp only [%s, SixQubit.signMul_true, SixQubit.signMul_false]'
      % ', '.join('sgp_%s_%d' % (nm, n) for n in range(8)))
    W('  try ring')
    W('')

# ------------------------------------------------------------------ moments
QS = ' '.join('q%d' % k for k in range(16))
RS = ' '.join('r%d' % k for k in range(16))
ALL = QS + ' ' + RS


def sum0(pred):
    return ' + '.join('q%d' % k for k, x in enumerate(S0) if pred(x))


def sum1(pred):
    return ' + '.join('r%d' % k for k, y in enumerate(S1) if pred(y))


W('/-! ## The moment system -/')
W('')
W('/-- The two normalizations, the twenty-one moment equalities, and the')
W('nonnegativity of every probability. -/')
W('structure MomentSystem (%s : Real) : Prop where' % ALL)
W('  n0 : %s = 1' % ' + '.join('q%d' % k for k in range(16)))
W('  n1 : %s = 1' % ' + '.join('r%d' % k for k in range(16)))
for i in range(6):
    W('  m%d : %s = %s' % (i + 1, sum0(lambda x, i=i: x[i] == '1'), sum1(lambda y, i=i: y[i] == '1')))
for (i, j) in combinations(range(6), 2):
    W('  m%d%d : %s = %s' % (i + 1, j + 1,
                             sum0(lambda x, i=i, j=j: x[i] == '1' and x[j] == '1'),
                             sum1(lambda y, i=i, j=j: y[i] == '1' and y[j] == '1')))
W('')
for k in range(16):
    W('  nq%d : 0 ≤ q%d' % (k, k))
for k in range(16):
    W('  nr%d : 0 ≤ r%d' % (k, k))
W('')


def degq(v):
    return ' + '.join('q%d' % bot(tuple(sorted((v, u)))) for u in V if u != v)


W('/-- The moment normal form: the top anchor carries mass `1/4`, and the')
W('bottom edge masses are a scaled fractional perfect matching of `K_6`. -/')
W('theorem MomentSystem.normalForm {%s : Real}' % ALL)
W('    (h : MomentSystem %s) :' % ALL)
W('    r15 = 1/4 ∧ %s := ' % ' ∧ '.join('(%s = 1/4)' % degq(v) for v in V))
W('  by')
labels = ['n0', 'n1'] + ['m%d' % (i + 1) for i in range(6)] \
    + ['m%d%d' % (i + 1, j + 1) for (i, j) in combinations(range(6), 2)] \
    + ['nq%d' % k for k in range(16)] + ['nr%d' % k for k in range(16)]
W('  obtain ⟨%s⟩ := h' % ', '.join(labels))
W('  refine ⟨%s⟩ <;> linarith' % ', '.join(['?_'] * 7))
W('')
W('/-! ## The no-go -/')
W('')
W('/-- Conjugation does not change the squared modulus. -/')
W('theorem nsq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by')
W('  rw [Complex.star_def, Complex.normSq_conj]')
W('')
W('/-- **Orbit 17 is impossible.** -/')
W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
W('    (hm : MomentSystem')
W('            %s' % ' '.join('(Complex.normSq (c y%d))' % k for k in range(16)))
W('            %s)' % ' '.join('(Complex.normSq (d z%d))' % k for k in range(16)))
for e in EDGES:
    W('    (ho%d%da : offSum c d %s wz = 0)' % (e + (ename(e),)))
    W('    (ho%d%db : offSum c d %s wp%d = 0)' % (e + (ename(e), e[0])))
W('    : False := by')
for e in EDGES:
    W('  rw [ex_%s_z] at ho%d%da' % (ename(e), e[0], e[1]))
    W('  rw [ex_%s_p] at ho%d%db' % (ename(e), e[0], e[1]))
W('  obtain ⟨hr15, hg0, hg1, hg2, hg3, hg4, hg5⟩ := hm.normalForm')
W('  have hz15 : d z15 ≠ 0 := by')
W('    intro hx')
W('    rw [hx] at hr15')
W('    simp at hr15')
for e in EDGES:
    W('  have an%d%d : star (c y0) * d z%d + %s * d z15 = 0 := by'
      % (e + (top(e), C(e))))
    W('    linear_combination (1/2 : ℂ) * ho%d%da - (1/2 : ℂ) * ho%d%db' % (e + e))
for e in EDGES:
    Q = tuple(u for u in V if u not in e)
    gs = list(combinations(Q, 2))
    terms = ' + '.join('%s * d z%d' % (C(tuple(u for u in Q if u not in g)), top(g)) for g in gs)
    W('  have pf%d%d : %s = 0 := by' % (e + (terms,)))
    W('    linear_combination (1/2 : ℂ) * ho%d%da + (1/2 : ℂ) * ho%d%db' % (e + e))
for q in FOURS:
    f = tuple(u for u in V if u not in q)
    i, j, k, l = q
    haf = '%s * %s + %s * %s + %s * %s' % (C((i, j)), C((k, l)), C((i, k)), C((j, l)),
                                           C((i, l)), C((j, k)))
    gs = list(combinations(q, 2))
    comb = ' + '.join('%s * an%d%d' % (C(tuple(u for u in q if u not in g)), g[0], g[1])
                      for g in gs)
    W('  have hf%d%d%d%d : %s = 0 := by' % (q + (haf,)))
    W('    have hk : (2 : ℂ) * d z15 * (%s) = 0 := by' % haf)
    W('      linear_combination %s - star (c y0) * pf%d%d' % (comb, f[0], f[1]))
    W('    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)')
for v in V:
    terms = ' + '.join('Complex.normSq (%s)' % C(tuple(sorted((v, u)))) for u in V if u != v)
    W('  have hs%d : %s = 1/4 := by' % (v, terms))
    W('    simp only [nsq_star]')
    W('    linarith [hg%d]' % v)
W('  have hsys : SixQubit.Hafnian.Sys %s :=' % ' '.join('(%s)' % C(e) for e in EDGES))
W('    ⟨%s,' % ', '.join('hf%d%d%d%d' % q for q in FOURS))
W('     %s⟩' % ', '.join('hs%d' % v for v in V))
W('  exact SixQubit.Hafnian.no_go hsys')
W('')
W('end')
W('')
W('end SixQubit.Orbit17')

out = 'SixQubit/Orbit17.lean'
with open(out, 'w', encoding='utf-8') as f:
    f.write('\n'.join(L) + '\n')
print('wrote', out, len(L), 'lines')
