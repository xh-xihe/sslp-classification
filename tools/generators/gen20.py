"""Emit the kernel-only Lean module for moment orbit 20.

Orbit 20 = (q,m,a) = (4,2,(1,1,1,2,2,2)), delta = 2.  A string is (r,y) with r
the first three bits; only the even-parity r in {000,011,101,110} occur, and for
each r the bottom tails form a parity class P_r of size four while the top tails
form the opposite class.  Complementing the last three bits matches the two.

Each of qubits 4,5,6 is half-angle.  For the flip mask e_k the eight dressings
{0,e_k} x {0,e_1,e_2,e_3} span the restricted projectors Pi_r (1 +- chi_k)/2,
and each of those isolates a two-term reciprocal relation

    conj(c_{r,y}) dt_{r,y'} + conj(c_{r,y'}) dt_{r,y} = 0

for the unique pair y != y' of P_r agreeing in coordinate k.  Six pairs per
block, twenty-four relations in all.

Squared moduli make every 2x2 minor of the two-row block matrix vanish; equal
block masses (from the moment layer) then force |c| = |dt| pointwise; the
Z_k and Z_i Z_k moment rows then make each block uniform.  A block of positive
mass carries an odd triangle, killed by `SixQubit.Triangle.contradiction_of_normSq`.
"""
import io
import os
from itertools import combinations

import sympy as sp

NL = chr(10)
N = 6
BOOL = {'0': 'false', '1': 'true '}

Q, A, DELTA = 4, [1, 1, 1, 2, 2, 2], 2
COMP = '000111'


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


S0 = fiber(0)
S1 = fiber(DELTA)
n0, n1 = len(S0), len(S1)

BLOCKS = []
seen = []
for i, x in enumerate(S0):
    if x[:3] not in seen:
        seen.append(x[:3])
for r in seen:
    BLOCKS.append((r, [i for i in range(n0) if S0[i][:3] == r]))

MATCH = {i: S1.index(xor(S0[i], COMP)) for i in range(n0)}

MASKS = [('A', '000100'), ('B', '000010'), ('C', '000001')]

# matching equalities that linarith does not need inside `MomentSystem.uniform`
# (one per block is redundant given the block mass); named with a leading `_`
# so the unused-variable linter stays quiet while linarith still sees them.
UNUSED_MATCH = {7, 11, 15}


def dressings(e):
    """the eight rows Pi_r (1 +- chi_k)/2 actually use: {0,e_k} x {0,e_1,e_2,e_3}"""
    out = []
    for hi in ['000000', '100000', '010000', '001000']:
        out.append(hi)
        out.append(xor(hi, e))
    return sorted(set(out))


ZS = {tag: dressings(e) for tag, e in MASKS}
ZALL = sorted(set(sum(ZS.values(), [])))
ZNAME = {z: 'w%d' % r for r, z in enumerate(ZALL)}

INC = {tag: [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
       for tag, e in MASKS}
for tag, e in MASKS:
    assert len(INC[tag]) == n1, tag
    assert all(len({i for i in range(N) if e[i] == '1'}
                   | {i for i in range(N) if z[i] == '1'}) <= 2 for z in ZS[tag])


def pair_data(i, j):
    """the flip mask and the isolating rational combination for the pair (i,j)"""
    e = xor(S1[MATCH[j]], S0[i])
    assert xor(S1[MATCH[i]], e) == S0[j]
    tag = [t for t, ee in MASKS if ee == e][0]
    zs, inc = ZS[tag], INC[tag]
    tg = {MATCH[i], MATCH[j]}
    M = sp.Matrix([[sp.Integer(-1) ** dot(z, S1[t]) for z in zs] for (_, t) in inc])
    b = sp.Matrix([1 if t in tg else 0 for (_, t) in inc])
    lam = sp.symbols('l0:%d' % len(zs))
    sols = sp.linsolve((M, b), lam)
    assert sols, (i, j)
    s = [v.subs({x: 0 for x in lam}) for v in list(sols)[0]]
    assert M * sp.Matrix(s) == b, (i, j)
    return tag, [(zs[k], s[k]) for k in range(len(zs)) if s[k] != 0]


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
    W('import SixQubit.Triangle')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit 20')
    W('')
    W('Orbit 20 of `six_qubit_sslp.tex`: q = 4, angle vector')
    W('a = (1, 1, 1, 2, 2, 2), residues 0 and 2.')
    W('')
    W('Write a string as `(r, y)` with `r` the first three bits.  Only the four')
    W('even-parity `r` occur, and for each of them the bottom tails form a parity')
    W('class of size four while the top tails form the opposite class; the two are')
    W('matched by complementing the last three bits.')
    W('')
    W('Each of qubits 4, 5, 6 is half-angle.  For the flip mask `e_k` the eight')
    W('dressings `{0, e_k} x {0, e_1, e_2, e_3}` span the restricted projectors')
    W('`Pi_r (1 +- chi_k)/2`, and each of those isolates a two-term reciprocal')
    W('relation between the two points of a block that agree in coordinate `k`.')
    W('Six pairs per block, twenty-four relations in all.')
    W('')
    W('Squared moduli make every `2x2` minor of the two-row block matrix vanish;')
    W('the moment layer supplies equal block masses, which forces the two rows to')
    W('agree pointwise; the `Z_k` and `Z_i Z_k` moment rows then make every block')
    W('uniform.  Some block has positive mass, and on it any three points carry an')
    W('odd triangle of reciprocal relations, killed by')
    W('`SixQubit.Triangle.contradiction_of_normSq`.')
    W('')
    W('Everything computational is decided by the Lean kernel; `native_decide`')
    W('is not used.')
    W('-/')
    W('')
    W('namespace SixQubit.Orbit20')
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
    W('/-! ## Squared moduli and the two-row block lemma -/')
    W('')
    W('theorem nsqStar (a b : ℂ) :')
    W('    Complex.normSq (star a * b) = Complex.normSq a * Complex.normSq b := by')
    W('  rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]')
    W('')
    W('/-- A reciprocal relation makes the corresponding `2x2` minor vanish. -/')
    W("theorem minorEq {a b a' b' : ℂ} (h : star a * b + star a' * b' = 0) :")
    W("    Complex.normSq a * Complex.normSq b = Complex.normSq a' * Complex.normSq b' := by")
    W("  have h2 : star a * b = -(star a' * b') := by linear_combination h")
    W('  have h3 := congrArg Complex.normSq h2')
    W('  rwa [Complex.normSq_neg, nsqStar, nsqStar] at h3')
    W('')
    W('/-- Two nonnegative rows of length four with equal sums and vanishing `2x2`')
    W('minors are equal.  No positivity hypothesis is needed: the zero-mass case is')
    W('handled by the same argument. -/')
    W('theorem blockMatch {p0 p1 p2 p3 q0 q1 q2 q3 : Real}')
    W('    (h01 : p0 * q1 = p1 * q0) (h02 : p0 * q2 = p2 * q0) (h03 : p0 * q3 = p3 * q0)')
    W('    (h12 : p1 * q2 = p2 * q1) (h13 : p1 * q3 = p3 * q1) (h23 : p2 * q3 = p3 * q2)')
    W('    (hs : p0 + p1 + p2 + p3 = q0 + q1 + q2 + q3)')
    W('    (n0 : 0 ≤ p0) (n1 : 0 ≤ p1) (n2 : 0 ≤ p2) (n3 : 0 ≤ p3)')
    W('    (m0 : 0 ≤ q0) (m1 : 0 ≤ q1) (m2 : 0 ≤ q2) (m3 : 0 ≤ q3) :')
    W('    p0 = q0 ∧ p1 = q1 ∧ p2 = q2 ∧ p3 = q3 := by')
    W('  have k0 : (p0 - q0) * (q0 + q1 + q2 + q3) = 0 := by')
    W('    linear_combination h01 + h02 + h03 + q0 * hs')
    W('  have k1 : (p1 - q1) * (q0 + q1 + q2 + q3) = 0 := by')
    W('    linear_combination -h01 + h12 + h13 + q1 * hs')
    W('  have k2 : (p2 - q2) * (q0 + q1 + q2 + q3) = 0 := by')
    W('    linear_combination -h02 - h12 + h23 + q2 * hs')
    W('  have k3 : (p3 - q3) * (q0 + q1 + q2 + q3) = 0 := by')
    W('    linear_combination -h03 - h13 - h23 + q3 * hs')
    W('  rcases eq_or_lt_of_le (show (0:Real) ≤ q0 + q1 + q2 + q3 by linarith) with h | h')
    W('  · exact ⟨by linarith, by linarith, by linarith, by linarith⟩')
    W('  · refine ⟨?_, ?_, ?_, ?_⟩')
    for k in range(4):
        W('    · rcases mul_eq_zero.mp k%d with t | t' % k)
        W('      · linarith')
        W('      · linarith')
    W('')
    W('/-! ## The three half-angle flip masks and their dressings -/')
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

    W('/-- The four point projectors on the three-bit head separate the blocks:')
    W('bottom and top block masses agree. -/')
    W('theorem MomentSystem.blockMass {%s : Real}' % allv)
    W('    (h : MomentSystem %s) :' % allv)
    concl = []
    for r, bsx in BLOCKS:
        concl.append('%s = %s'
                     % (' + '.join('q%d' % i for i in bsx),
                        ' + '.join('r%d' % MATCH[i] for i in bsx)))
    W('    ' + ' ∧ '.join(concl) + ' := by')
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  refine ⟨' + ', '.join(['?_'] * len(BLOCKS)) + '⟩ <;> linarith')
    W('')
    W('/-- Once bottom and top masses agree pointwise under the complement matching,')
    W('the `Z_k` and `Z_i Z_k` rows force every block to be uniform. -/')
    W('theorem MomentSystem.uniform {%s : Real}' % allv)
    W('    (h : MomentSystem %s)' % allv)
    for i in range(n0):
        W('    (%se%d : q%d = r%d)' % ('_' if i in UNUSED_MATCH else '', i, i, MATCH[i]))
    W('    :')
    ucon = []
    for r, bsx in BLOCKS:
        for i in bsx[1:]:
            ucon.append('q%d = q%d' % (i, bsx[0]))
    ucon.append('4 * (%s) = 1' % ' + '.join('q%d' % bsx[0] for _, bsx in BLOCKS))
    W('    ' + ' ∧ '.join(ucon) + ' := by')
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  refine ⟨' + ', '.join(['?_'] * len(ucon)) + '⟩ <;> linarith')
    W('')
    W('/-! ## The no-go -/')

    hyp = []
    for tag, e in MASKS:
        for z in ZS[tag]:
            hyp.append((tag, z))
    pos = {(tg, zz): k for k, (tg, zz) in enumerate(hyp)}

    W('')
    W('set_option maxHeartbeats 4000000 in')
    W('/-- **Orbit 20 is impossible.** -/')
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
    for k, (tag, z) in enumerate(hyp):
        W('    (h%d : offSum c d ef%s %s = 0)' % (k, tag, ZNAME[z]))
    W('    : False := by')
    for k, (tag, z) in enumerate(hyp):
        W('  rw [ex%s_%s] at h%d' % (tag, ZNAME[z], k))
    for r, bsx in BLOCKS:
        for i, j in combinations(bsx, 2):
            tag, used = pair_data(i, j)
            comb = ' + '.join('(%s : ℂ) * h%d' % (m, pos[(tag, zz)]) for zz, m in used)
            W('  have rel_%d_%d : star (c y%d) * d z%d + star (c y%d) * d z%d = 0 := by'
              % (i, j, i, MATCH[j], j, MATCH[i]))
            W('    linear_combination %s' % comb)
    for r, bsx in BLOCKS:
        for i, j in combinations(bsx, 2):
            W('  have min_%d_%d : Complex.normSq (c y%d) * Complex.normSq (d z%d)'
              % (i, j, i, MATCH[j]))
            W('      = Complex.normSq (c y%d) * Complex.normSq (d z%d) := minorEq rel_%d_%d'
              % (j, MATCH[i], i, j))
    W('  obtain ⟨' + ', '.join('bm%d' % k for k in range(len(BLOCKS))) + '⟩ := hm.blockMass')
    for k, (r, bsx) in enumerate(BLOCKS):
        args = ' '.join('min_%d_%d' % (i, j) for i, j in combinations(bsx, 2))
        W('  obtain ⟨' + ', '.join('mt%d' % i for i in bsx) + '⟩ :=')
        W('    blockMatch %s bm%d' % (args, k))
        W('      ' + ' '.join('(Complex.normSq_nonneg (c y%d))' % i for i in bsx))
        W('      ' + ' '.join('(Complex.normSq_nonneg (d z%d))' % MATCH[i] for i in bsx))
    W('  obtain ⟨' + ', '.join(
        ['u%d' % i for _, bsx in BLOCKS for i in bsx[1:]] + ['usum']) + '⟩ :=')
    W('    hm.uniform ' + ' '.join('mt%d' % i for i in range(n0)))
    W('  clear hm ' + ' '.join('h%d' % k for k in range(len(hyp))))
    W('  clear ' + ' '.join('min_%d_%d' % (i, j)
                            for _, bsx in BLOCKS for i, j in combinations(bsx, 2)))
    W('  clear ' + ' '.join('bm%d' % k for k in range(len(BLOCKS))))

    def case_lines(k):
        """the nested `some block has positive mass` case split, as relative lines"""
        _, bsx = BLOCKS[k]
        a, b, cc = bsx[0], bsx[1], bsx[2]
        out = ['rcases lt_or_ge (0 : Real) (Complex.normSq (c y%d)) with hp%d | hp%d'
               % (a, k, k),
               '· exact SixQubit.Triangle.contradiction_of_normSq rel_%d_%d rel_%d_%d rel_%d_%d'
               % (a, b, a, cc, b, cc),
               '    (by linarith only [hp%d, u%d]) (by linarith only [hp%d, mt%d])'
               % (k, cc, k, a),
               '    (by linarith only [hp%d, u%d, mt%d])' % (k, b, b)]
        if k + 1 < len(BLOCKS):
            sub = case_lines(k + 1)
        else:
            sub = ['linarith only [%s, usum]'
                   % ', '.join('hp%d' % t for t in range(len(BLOCKS)))]
        out.append('· ' + sub[0])
        out.extend('  ' + s for s in sub[1:])
        return out

    for line in case_lines(0):
        W('  ' + line)
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit20')
    return NL.join(L) + NL


if __name__ == '__main__':
    here = os.path.dirname(os.path.abspath(__file__))
    out = os.path.abspath(os.path.join(here, '..', '..', 'SixQubit', 'Orbit20.lean'))
    src = emit()
    io.open(out, 'w', encoding='utf-8', newline=NL).write(src)
    print('%s : %d lines' % (out, src.count(NL)))
