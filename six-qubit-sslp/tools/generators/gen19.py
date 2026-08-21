"""Emit the kernel-only Lean module for moment orbit 19.

Orbit 19 = (q,m,a) = (4,2,(1,1,1,1,2,2)), delta = 2.  Coordinates 5 and 6 are
both half-angle, so each of the flip masks e_5 = 000010 and e_6 = 000001 maps
the bottom fiber bijectively onto the top fiber.  For each mask the twelve
admissible dressings {z : |supp(e) u supp(z)| <= 2} span, among others, the
four restricted product projectors Phi^{(i)}_{alpha,beta} of the paper, and
each of those isolates a single anchor incidence.  The eight resulting
monomials are exactly the four products between the two bottom w=0 anchors and
the two top w=0 anchors, and the same at w=4.

Everything the module asserts about the fibers, the incidences and the signs is
decided by the Lean kernel; every probability fact is derived from the moment
structure by linarith.
"""
import io
import os
from itertools import combinations

import sympy as sp

NL = chr(10)
N = 6
BOOL = {'0': 'false', '1': 'true '}

Q, A, DELTA = 4, [1, 1, 1, 1, 2, 2], 2


def fiber(res):
    out = []
    for k in range(1 << N):
        s = format(k, '06b')
        if sum(A[i] for i in range(N) if s[i] == '1') % Q == res:
            out.append(s)
    return out


def xor(s, t):
    return ''.join('1' if (s[i] == '1') != (t[i] == '1') else '0' for i in range(N))


def dot(z, x):
    return sum(1 for i in range(N) if z[i] == '1' and x[i] == '1') % 2


def dressings(e):
    sup = {i for i in range(N) if e[i] == '1'}
    return [format(m, '06b') for m in range(64)
            if len(sup | {i for i in range(N) if format(m, '06b')[i] == '1'}) <= 2]


S0 = fiber(0)
S1 = fiber(DELTA)
n0, n1 = len(S0), len(S1)

MASKS = [('A', '000010'), ('B', '000001')]
ZS = {tag: dressings(e) for tag, e in MASKS}
ZALL = sorted(set(sum(ZS.values(), [])))
ZNAME = {z: 'w%d' % r for r, z in enumerate(ZALL)}

# incidences: mask -> list of (bottom index, top index), ordered by top index
INC = {tag: [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
       for tag, e in MASKS}

# the eight anchors
ANCH0_BOT = ['000000', '000011']
ANCH0_TOP = ['000001', '000010']
ANCH4_BOT = ['111100', '111111']
ANCH4_TOP = ['111101', '111110']


def isolate(tag, e, top):
    """rational lambda over the dressings of `tag` isolating the incidence at `top`"""
    zs = ZS[tag]
    inc = INC[tag]
    t0 = S1.index(top)
    M = sp.Matrix([[sp.Integer(-1) ** dot(z, S1[t]) for z in zs] for (_, t) in inc])
    b = sp.Matrix([1 if t == t0 else 0 for (_, t) in inc])
    lam = sp.symbols('l0:%d' % len(zs))
    sols = sp.linsolve((M, b), lam)
    assert sols, (tag, top)
    s = [v.subs({x: 0 for x in lam}) for v in list(sols)[0]]
    assert M * sp.Matrix(s) == b, (tag, top)
    return [(zs[k], s[k]) for k in range(len(zs)) if s[k] != 0]


def qname(r):
    return 'q%d' % r


def emit():
    L = []
    W = L.append
    qs = ' '.join('q%d' % r for r in range(n0))
    rs = ' '.join('r%d' % r for r in range(n1))
    allv = qs + ' ' + rs

    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit 19')
    W('')
    W('Orbit 19 of `six_qubit_sslp.tex`: q = 4, angle vector')
    W('a = (1, 1, 1, 1, 2, 2), residues 0 and 2.')
    W('')
    W('Coordinates 5 and 6 are both half-angle, so each of the flip masks')
    W('`efA = 000010` and `efB = 000001` is a bijection from the bottom fiber to')
    W('the top fiber.  For each mask the twelve admissible dressings span the')
    W('four restricted product projectors of the paper, and each of those')
    W('isolates a single anchor incidence.  The eight isolated monomials are')
    W('exactly the four products between the two bottom `w = 0` anchors and the')
    W('two top `w = 0` anchors, together with the same four at `w = 4`.')
    W('')
    W('The pure-`Z` (moment) layer forces `P0 = Q0`, `P4 = Q4` and')
    W('`P0 + P4 = 1/2` for the anchor masses.  The vanishing products give')
    W('`P0 * Q0 = 0` and `P4 * Q4 = 0`, hence `P0 = P4 = 0`, contradicting the')
    W('half-mass identity.')
    W('')
    W('Everything computational is decided by the Lean kernel; `native_decide`')
    W('is not used.')
    W('-/')
    W('')
    W('namespace SixQubit.Orbit19')
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
        W('def y%d : SS.BitString 6 := bs %s  -- %s'
          % (r, ' '.join(BOOL[ch] for ch in x), x))
    W('')
    for r, y in enumerate(S1):
        W('def z%d : SS.BitString 6 := bs %s  -- %s'
          % (r, ' '.join(BOOL[ch] for ch in y), y))
    W('')
    W('def S0 : Finset (SS.BitString 6) := {%s}' % ', '.join('y%d' % r for r in range(n0)))
    W('def S1 : Finset (SS.BitString 6) := {%s}' % ', '.join('z%d' % r for r in range(n1)))
    W('')
    W('def av : Fin 6 -> ZMod %d := ![%s]' % (Q, ', '.join(map(str, A))))
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
    W('/-! ## Two elementary facts about squared moduli -/')
    W('')
    W('theorem nsqStar (a b : ℂ) :')
    W('    Complex.normSq (star a * b) = Complex.normSq a * Complex.normSq b := by')
    W('  rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]')
    W('')
    W('theorem nsqZero {a b : ℂ} (h : star a * b = 0) :')
    W('    Complex.normSq a * Complex.normSq b = 0 := by')
    W('  rw [← nsqStar, h, Complex.normSq_zero]')
    W('')
    W('/-! ## The two half-angle flip masks and their dressings -/')
    W('')
    for tag, e in MASKS:
        W('def ef%s : SS.BitString 6 := bs %s  -- %s'
          % (tag, ' '.join(BOOL[ch] for ch in e), e))
    W('')
    for z in ZALL:
        W('def %s : SS.BitString 6 := bs %s  -- %s'
          % (ZNAME[z], ' '.join(BOOL[ch] for ch in z), z))
    W('')
    for tag, e in MASKS:
        inc = INC[tag]
        W('theorem incidence%s :' % tag)
        W('    S1.filter (fun y => SS.bxor y ef%s ∈ S0) = {%s} := by decide'
          % (tag, ', '.join('z%d' % t for _, t in inc)))
        for i, t in inc:
            W('theorem flip%s_%d : SS.bxor z%d ef%s = y%d := by decide' % (tag, t, t, tag, i))
        W('')
    for z in ZALL:
        for t in range(n1):
            W('theorem sg_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (ZNAME[z], t, ZNAME[z], t, BOOL['1' if dot(z, S1[t]) else '0'].strip()))
    W('')
    W('/-! ## The Walsh expansions -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    for tag, e in MASKS:
        inc = INC[tag]
        for z in ZS[tag]:
            body = ' '.join('%s star (c y%d) * d z%d' % ('-' if dot(z, S1[t]) else '+', i, t)
                            for i, t in inc).lstrip('+ ')
            W('theorem ex%s_%s (c d : SS.BitString 6 -> ℂ) :' % (tag, ZNAME[z]))
            W('    offSum c d ef%s %s =' % (tag, ZNAME[z]))
            W('      %s := by' % body)
            W('  unfold offSum')
            W('  rw [incidence%s]' % tag)
            W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(inc) - 1))
              + ', Finset.sum_singleton]')
            W('  rw [' + ', '.join('flip%s_%d' % (tag, t) for _, t in inc) + ']')
            lem = ['sg_%s_%d' % (ZNAME[z], t) for _, t in inc]
            if any(dot(z, S1[t]) for _, t in inc):
                lem.append('SixQubit.signMul_true')
            if any(not dot(z, S1[t]) for _, t in inc):
                lem.append('SixQubit.signMul_false')
            W('  simp only [' + ', '.join(lem) + ']')
            W('  try ring')
            W('')
    W('/-! ## The moment system -/')
    W('')
    W('/-- The two normalizations, the twenty-one moment equalities, and the')
    W('nonnegativity of every probability.  These are exactly the pure-`Z`')
    W('Knill-Laflamme rows of physical weight at most two. -/')
    W('structure MomentSystem (%s : Real) : Prop where' % allv)
    W('  n0 : %s = 1' % ' + '.join('q%d' % r for r in range(n0)))
    W('  n1 : %s = 1' % ' + '.join('r%d' % r for r in range(n1)))
    idx = [(i,) for i in range(6)] + list(combinations(range(6), 2))
    for T in idx:
        lhs = [r for r in range(n0) if all(S0[r][j] == '1' for j in T)]
        rhs = [r for r in range(n1) if all(S1[r][j] == '1' for j in T)]
        W('  m%s : %s = %s'
          % (''.join(str(j + 1) for j in T),
             ' + '.join('q%d' % r for r in lhs) or '0',
             ' + '.join('r%d' % r for r in rhs) or '0'))
    W('')
    for r in range(n0):
        W('  nq%d : 0 ≤ q%d' % (r, r))
    for r in range(n1):
        W('  nr%d : 0 ≤ r%d' % (r, r))
    W('')
    fields = (['n0', 'n1'] + ['m%s' % ''.join(str(j + 1) for j in T) for T in idx]
              + ['nq%d' % r for r in range(n0)] + ['nr%d' % r for r in range(n1)])

    b00, b01 = S0.index(ANCH0_BOT[0]), S0.index(ANCH0_BOT[1])
    t00, t01 = S1.index(ANCH0_TOP[0]), S1.index(ANCH0_TOP[1])
    b40, b41 = S0.index(ANCH4_BOT[0]), S0.index(ANCH4_BOT[1])
    t40, t41 = S1.index(ANCH4_TOP[0]), S1.index(ANCH4_TOP[1])

    W('/-- The anchor masses.  `P0 = Q0` and `P4 = Q4` come from the two degree-two')
    W('shell projectors `g0` and `g4`; `P0 + P4 = 1/2` comes from the indicator')
    W('`u = n5 + n6 - 2 n5 n6` of `x5 != x6`. -/')
    W('theorem MomentSystem.anchors {%s : Real}' % allv)
    W('    (h : MomentSystem %s) :' % allv)
    W('    q%d + q%d = r%d + r%d ∧ q%d + q%d = r%d + r%d ∧ q%d + q%d + q%d + q%d = 1/2 := by'
      % (b00, b01, t00, t01, b40, b41, t40, t41, b00, b01, b40, b41))
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  refine ⟨?_, ?_, ?_⟩ <;> linarith')
    W('')
    W('/-! ## The no-go -/')
    W('')
    W('/-- **Orbit 19 is impossible.** -/')
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
    hyp = []
    for tag, e in MASKS:
        for z in ZS[tag]:
            hyp.append((tag, z))
    for k, (tag, z) in enumerate(hyp):
        W('    (h%d : offSum c d ef%s %s = 0)' % (k, tag, ZNAME[z]))
    W('    : False := by')
    for k, (tag, z) in enumerate(hyp):
        W('  rw [ex%s_%s] at h%d' % (tag, ZNAME[z], k))

    # the eight isolated monomials
    prods = []
    for tag, e in MASKS:
        for top in ANCH0_TOP + ANCH4_TOP:
            used = isolate(tag, e, top)
            t = S1.index(top)
            i = S0.index(xor(top, e))
            pos = {(tg, zz): k for k, (tg, zz) in enumerate(hyp)}
            comb = ' + '.join('(%s : ℂ) * h%d' % (m, pos[(tag, zz)]) for zz, m in used)
            prods.append((i, t, comb))
    for r, (i, t, comb) in enumerate(prods):
        W('  have p%d : star (c y%d) * d z%d = 0 := by' % (r, i, t))
        W('    linear_combination %s' % comb)
    for r, (i, t, _) in enumerate(prods):
        W('  have n%d : Complex.normSq (c y%d) * Complex.normSq (d z%d) = 0 := nsqZero p%d'
          % (r, i, t, r))
    at_ = {(i, t): r for r, (i, t, _) in enumerate(prods)}
    g0 = [at_[(i, t)] for i in (b00, b01) for t in (t00, t01)]
    g4 = [at_[(i, t)] for i in (b40, b41) for t in (t40, t41)]
    W('  obtain ⟨a0, a4, ah⟩ := hm.anchors')
    W('  have z0m : (Complex.normSq (c y%d) + Complex.normSq (c y%d)) *' % (b00, b01))
    W('      (Complex.normSq (d z%d) + Complex.normSq (d z%d)) = 0 := by' % (t00, t01))
    W('    linear_combination %s' % ' + '.join('n%d' % r for r in g0))
    W('  have z4m : (Complex.normSq (c y%d) + Complex.normSq (c y%d)) *' % (b40, b41))
    W('      (Complex.normSq (d z%d) + Complex.normSq (d z%d)) = 0 := by' % (t40, t41))
    W('    linear_combination %s' % ' + '.join('n%d' % r for r in g4))
    W('  have sq0 : (Complex.normSq (c y%d) + Complex.normSq (c y%d)) *' % (b00, b01))
    W('      (Complex.normSq (c y%d) + Complex.normSq (c y%d)) = 0 := by' % (b00, b01))
    W('    linear_combination z0m + (Complex.normSq (c y%d) + Complex.normSq (c y%d)) * a0'
      % (b00, b01))
    W('  have sq4 : (Complex.normSq (c y%d) + Complex.normSq (c y%d)) *' % (b40, b41))
    W('      (Complex.normSq (c y%d) + Complex.normSq (c y%d)) = 0 := by' % (b40, b41))
    W('    linear_combination z4m + (Complex.normSq (c y%d) + Complex.normSq (c y%d)) * a4'
      % (b40, b41))
    W('  have e0 := mul_self_eq_zero.mp sq0')
    W('  have e4 := mul_self_eq_zero.mp sq4')
    W('  linarith')
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit19')
    return NL.join(L) + NL


if __name__ == '__main__':
    here = os.path.dirname(os.path.abspath(__file__))
    out = os.path.abspath(os.path.join(here, '..', '..', 'SixQubit', 'Orbit19.lean'))
    src = emit()
    io.open(out, 'w', encoding='utf-8', newline=NL).write(src)
    print('%s : %d lines' % (out, src.count(NL)))
