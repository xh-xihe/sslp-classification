"""Kernel-only Lean certificate for orbit 33: the block reflection."""
import io
import sys

import sympy as sp

sys.path.insert(0, '.')
from orbit import fiber
from scan import bits, xor, dot
from cert import build, reduce_mod_linear
from kl import dressings_full
from o33 import S0, S1, BOT, TOP, RV, CONDS, Pc, Pd, solve_target

NL = chr(10)
AVEC, QQ, DELTA = [0, 1, 1, 3, 3, 3], 5, 1
n0, n1 = len(S0), len(S1)
MD = '100000'
CROSS = ['010000', '110000', '001000', '101000',
         '000110', '000101', '000011', '001001', '001010', '001100']
MASKS = [MD] + CROSS
mid = {m: k for k, m in enumerate(MASKS)}
INC = {m: [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
       for m in MASKS}
# dressings actually used
USE = {MD: dressings_full(MD)}
for m in CROSS:
    USE[m] = [bits(0), MD] if m in ('010000', '110000', '001000', '101000') else [bits(0)]
zall = sorted({z for m in MASKS for z in USE[m]})
zname = {z: 'w%d' % k for k, z in enumerate(zall)}
Q, R, V, Am, bv, enames = build(S0, S1)
fields = list(enames) + ['nq%d' % k for k in range(n0)] + ['nr%d' % k for k in range(n1)]


def blit(s):
    return ' '.join('true ' if ch == '1' else 'false' for ch in s)


def pname(i):
    for k, (a, b) in enumerate(BOT):
        if i == a:
            return 'c y%d' % a, 'p%d' % k
        if i == b:
            return 'c y%d' % b, 'q%d' % k


def tname(j):
    for k, (a, b) in enumerate(TOP):
        if j == a:
            return 'd z%d' % a, 's%d' % k
        if j == b:
            return 'd z%d' % b, 't%d' % k


def solve_row(m, tgt):
    """Coefficients over USE[m] realising the target sign pattern on INC[m]."""
    M = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in INC[m]] for z in USE[m]])
    sol = M.T.gauss_jordan_solve(sp.Matrix(tgt))[0]
    mu = sol.subs({p: 0 for p in sol.free_symbols})
    return [(USE[m][u], sp.Rational(mu[u])) for u in range(len(USE[m])) if mu[u] != 0]


L = []
W = L.append
W('import Mathlib')
W('')
W('import SS.FullKL')
W('import SixQubit.Common')
W('import SixQubit.Block33')
W('')
W('/-!')
W('# Six-qubit no-go for moment orbit 33: a block reflection')
W('')
W('Orbit 33 of `six_qubit_sslp_v7.tex`: q = 5, angle vector a = (0, 1, 1, 3, 3, 3),')
W('residues 0 and 1, fibers of size twelve each.')
W('')
W('The first qubit carries angle zero, so both fibers are closed under flipping it')
W('and split into six blocks of two.  Writing `c_i` and `d_i` for the resulting')
W('two-component vectors, the moment system pins every block norm to')
W('`R = (3, 2, 2, 1, 1, 1)/10`, and the diagonal Knill-Laflamme conditions for')
W('`F` on the first qubit together with `F Z_j` on a second give the reflection')
W('identities `c_i c_i^dagger + d_i d_i^dagger = 2 R_i rho`.  The cross conditions')
W('force blocks 1 and 2 to be collinear with block 0 on both fibers, and then force')
W('blocks 3, 4, 5 to be orthogonal to block 0 on the opposite fiber.  Those two')
W('facts push `rho` to `I/2` and simultaneously to a rank-one multiple of it, which')
W('is impossible.  `SixQubit.Block33.block_contradiction` carries that argument;')
W('this module supplies its hypotheses from the Knill-Laflamme conditions.')
W('')
W('Everything computational is decided by the Lean kernel; `native_decide` is')
W('not used.')
W('-/')
W('')
W('namespace SixQubit.Orbit33')
W('')
W('open scoped BigOperators')
W('open scoped ComplexConjugate')
W('')
W('noncomputable section')
W('')
W('def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]')
W('')
for k, s in enumerate(S0):
    W('def y%d : SS.BitString 6 := bs %s  -- %s' % (k, blit(s), s))
W('')
for k, s in enumerate(S1):
    W('def z%d : SS.BitString 6 := bs %s  -- %s' % (k, blit(s), s))
W('')
W('def S0 : Finset (SS.BitString 6) := {%s}' % ', '.join('y%d' % k for k in range(n0)))
W('def S1 : Finset (SS.BitString 6) := {%s}' % ', '.join('z%d' % k for k in range(n1)))
W('')
W('def av : Fin 6 -> ZMod %d := ![%s]' % (QQ, ', '.join(map(str, AVEC))))
W('')
W('/-- Each support is exactly its residue fiber, decided over all 64 strings. -/')
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
for m in MASKS:
    W('def ef%d : SS.BitString 6 := bs %s  -- mask %s' % (mid[m], blit(m), m))
for z in zall:
    W('def %s : SS.BitString 6 := bs %s  -- dressing %s' % (zname[z], blit(z), z))
W('')
io.open('gen16_head.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('head: %d lines; masks %s' % (len(L), MASKS))
print('incidence counts:', {m: len(INC[m]) for m in MASKS})

# ---------------------------------------------------------------- part 2
L = []
W = L.append
W('/-! ## The Knill-Laflamme sums -/')
W('')
W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
W('')
W('/-- `<0_L| X^e Z^z |0_L>` with the global prefactor omitted. -/')
W('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
W('      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)')
W('')
W('/-- `<1_L| X^e Z^z |1_L>`. -/')
W('def diagTop (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
W('      SixQubit.signMul (SS.bdot z y) (star (d (SS.bxor y e)) * d y)')
W('')
W('/-- `star z * z` is the squared modulus. -/')
W('theorem sq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by')
W('  rw [mul_comm, Complex.normSq_eq_conj_mul_self]; rfl')
W('')
W('/-! ## Incidences, all decided -/')
W('')
W('theorem diagB_inc :')
W('    S0.filter (fun x => SS.bxor x ef0 ∈ S0) = {%s} := by decide'
  % ', '.join('y%d' % i for i in range(n0)))
W('theorem diagT_inc :')
W('    S1.filter (fun y => SS.bxor y ef0 ∈ S1) = {%s} := by decide'
  % ', '.join('z%d' % j for j in range(n1)))
for i, x in enumerate(S0):
    W('theorem dfb%d : SS.bxor y%d ef0 = y%d := by decide'
      % (i, i, S0.index(xor(x, MD))))
for j, y in enumerate(S1):
    W('theorem dft%d : SS.bxor z%d ef0 = z%d := by decide'
      % (j, j, S1.index(xor(y, MD))))
for z in USE[MD]:
    for i, x in enumerate(S0):
        W('theorem dsb%s_%d : SS.bdot %s y%d = %s := by decide'
          % (zname[z], i, zname[z], i, 'true' if dot(z, x) else 'false'))
    for j, y in enumerate(S1):
        W('theorem dst%s_%d : SS.bdot %s z%d = %s := by decide'
          % (zname[z], j, zname[z], j, 'true' if dot(z, y) else 'false'))
for m in CROSS:
    nn, ii = mid[m], INC[m]
    W('theorem incidence%d :' % nn)
    W('    S1.filter (fun y => SS.bxor y ef%d ∈ S0) = {%s} := by decide'
      % (nn, ', '.join('z%d' % t for _, t in ii)))
    for i, t in ii:
        W('theorem fl%d_%d : SS.bxor z%d ef%d = y%d := by decide' % (nn, t, t, nn, i))
    for z in USE[m]:
        for i, t in ii:
            W('theorem sg%d_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (nn, zname[z], t, zname[z], t, 'true' if dot(z, S1[t]) else 'false'))
W('')
W('/-! ## Walsh expansions -/')
W('')
for z in USE[MD]:
    nm = zname[z]
    body = ' '.join('%s star (c y%d) * c y%d'
                    % ('-' if dot(z, S0[i]) else '+', S0.index(xor(S0[i], MD)), i)
                    for i in range(n0)).lstrip('+ ')
    W('theorem dbot_%s (c : SS.BitString 6 -> ℂ) :' % nm)
    W('    diagBot c ef0 %s = %s := by' % (nm, body))
    W('  unfold diagBot')
    W('  rw [diagB_inc]')
    W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (n0 - 1))
      + ', Finset.sum_singleton]')
    W('  rw [' + ', '.join('dfb%d' % i for i in range(n0)) + ']')
    lem = ['dsb%s_%d' % (nm, i) for i in range(n0)]
    if any(dot(z, S0[i]) for i in range(n0)):
        lem.append('SixQubit.signMul_true')
    if any(not dot(z, S0[i]) for i in range(n0)):
        lem.append('SixQubit.signMul_false')
    W('  simp only [' + ', '.join(lem) + ']')
    W('  try ring')
    W('')
    body = ' '.join('%s star (d z%d) * d z%d'
                    % ('-' if dot(z, S1[j]) else '+', S1.index(xor(S1[j], MD)), j)
                    for j in range(n1)).lstrip('+ ')
    W('theorem dtop_%s (d : SS.BitString 6 -> ℂ) :' % nm)
    W('    diagTop d ef0 %s = %s := by' % (nm, body))
    W('  unfold diagTop')
    W('  rw [diagT_inc]')
    W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (n1 - 1))
      + ', Finset.sum_singleton]')
    W('  rw [' + ', '.join('dft%d' % j for j in range(n1)) + ']')
    lem = ['dst%s_%d' % (nm, j) for j in range(n1)]
    if any(dot(z, S1[j]) for j in range(n1)):
        lem.append('SixQubit.signMul_true')
    if any(not dot(z, S1[j]) for j in range(n1)):
        lem.append('SixQubit.signMul_false')
    W('  simp only [' + ', '.join(lem) + ']')
    W('  try ring')
    W('')
for m in CROSS:
    nn, ii = mid[m], INC[m]
    for z in USE[m]:
        body = ' '.join('%s star (c y%d) * d z%d' % ('-' if dot(z, S1[t]) else '+', i, t)
                        for i, t in ii).lstrip('+ ')
        W('theorem ex%d_%s (c d : SS.BitString 6 -> ℂ) :' % (nn, zname[z]))
        W('    offSum c d ef%d %s = %s := by' % (nn, zname[z], body))
        W('  unfold offSum')
        W('  rw [incidence%d]' % nn)
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(ii) - 1))
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('fl%d_%d' % (nn, t) for _, t in ii) + ']')
        lem = ['sg%d_%s_%d' % (nn, zname[z], t) for _, t in ii]
        if any(dot(z, S1[t]) for _, t in ii):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S1[t]) for _, t in ii):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
io.open('gen16_mid.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('mid: %d lines' % len(L))

# ---------------------------------------------------------------- part 3
L = []
W = L.append
qs = ' '.join('q%d' % k for k in range(n0))
rs = ' '.join('r%d' % k for k in range(n1))
W('/-! ## The moment system -/')
W('')
W('/-- The two normalizations and the moment equalities, with every probability')
W('nonnegative. -/')
W('structure MomentSystem (%s %s : Real) : Prop where' % (qs, rs))
for row in range(Am.rows):
    if enames[row] in ('n0', 'n1'):
        trm = ' + '.join(('q%d' % k) if k < n0 else ('r%d' % (k - n0))
                         for k in range(n0 + n1) if Am[row, k] != 0)
        W('  %s : %s = 1' % (enames[row], trm))
    else:
        lhs = ' + '.join('q%d' % k for k in range(n0) if Am[row, k] > 0) or '0'
        rhs = ' + '.join('r%d' % (k - n0) for k in range(n0, n0 + n1) if Am[row, k] < 0) or '0'
        W('  %s : %s = %s' % (enames[row], lhs, rhs))
W('')
for k in range(n0):
    W('  nq%d : 0 ≤ q%d' % (k, k))
for k in range(n1):
    W('  nr%d : 0 ≤ r%d' % (k, k))
W('')


def emit_real(name, expr, doc):
    cof, rem = reduce_mod_linear(expr, V, Am, bv)
    assert sp.simplify(rem) == 0, (name, rem)
    W('/-- %s -/' % doc)
    W('theorem %s {%s %s : Real} (h : MomentSystem %s %s) :' % (name, qs, rs, qs, rs))
    W('    %s = 0 := by' % sp.printing.sstr(expr).replace('**', '^'))
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    terms = ['(%s) * %s' % (sp.printing.sstr(cof[row]).replace('**', '^'), enames[row])
             for row in range(Am.rows) if cof[row] != 0]
    W('  linear_combination ' + ' + '.join(terms))
    W('')


RHO00 = sum(Q[BOT[k][0]] for k in range(6))
RHO11 = sum(Q[BOT[k][1]] for k in range(6))
for i in range(6):
    emit_real('blkc%d' % i, Q[BOT[i][0]] + Q[BOT[i][1]] - RV[i],
              'Bottom block %d has norm %s.' % (i, RV[i]))
for i in (0, 3):
    emit_real('blkd%d' % i, R[TOP[i][0]] + R[TOP[i][1]] - RV[i],
              'Top block %d has norm %s.' % (i, RV[i]))
emit_real('rr00_0', Q[BOT[0][0]] + R[TOP[0][0]] - 2 * RV[0] * RHO00,
          'Reflection identity, block 0, entry (0,0).')
emit_real('rr11_0', Q[BOT[0][1]] + R[TOP[0][1]] - 2 * RV[0] * RHO11,
          'Reflection identity, block 0, entry (1,1).')
emit_real('rr00_3', Q[BOT[3][0]] + R[TOP[3][0]] - 2 * RV[3] * RHO00,
          'Reflection identity, block 3, entry (0,0).')

W('/-! ## The reflection identity off the diagonal -/')
W('')
DGN = ['Dg_%s' % zname[z] for z in USE[MD]]
CO = ' + '.join('c y%d * star (c y%d)' % (k, k + 6) for k in range(6))
for i in (0, 3):
    sol = solve_target(0, 1, i)
    assert all(e == MD for e, z, v in sol), sol
    W('set_option maxHeartbeats 1000000 in')
    W('/-- Entry `(0,1)` of the reflection identity at block %d. -/' % i)
    W('theorem refl01_%d (c d : SS.BitString 6 -> ℂ)' % i)
    for z in USE[MD]:
        W('    (Dg_%s : diagBot c ef0 %s = diagTop d ef0 %s)'
          % (zname[z], zname[z], zname[z]))
    W('    : c y%d * star (c y%d) + d z%d * star (d z%d)'
      % (BOT[i][0], BOT[i][1], TOP[i][0], TOP[i][1]))
    W('      = (%s : ℂ) * (%s) := by' % (2 * RV[i], CO))
    for z in USE[MD]:
        W('  rw [dbot_%s, dtop_%s] at Dg_%s' % (zname[z], zname[z], zname[z]))
    W('  linear_combination ' + ' + '.join(
        '(%s : ℂ) * Dg_%s' % (v, zname[z]) for e, z, v in sol))
    W('')
io.open('gen16_sys.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('sys: %d lines' % len(L))

# ---------------------------------------------------------------- part 4
PB = lambda k: 'c y%d' % BOT[k][0]
QB = lambda k: 'c y%d' % BOT[k][1]
SB = lambda k: 'd z%d' % TOP[k][0]
TB_ = lambda k: 'd z%d' % TOP[k][1]
WMD = zname[MD]
L = []
W = L.append
W('/-! ## The cross relations -/')
W('')
XPAIR = {1: ('010000', 0), 2: ('110000', 1), 3: ('001000', 0), 4: ('101000', 1)}
XNAME = {}
for n, blk in ((1, 1), (2, 2)):
    for which, m in ((0, '010000' if blk == 1 else '001000'),
                     (1, '110000' if blk == 1 else '101000')):
        nn = mid[m]
        ii = INC[m]
        for half, (lo, hi) in ((0, (0, 2)), (1, (2, 4))):
            tgt = [1 if lo <= u < hi else 0 for u in range(4)]
            used = solve_row(m, tgt)
            i1, t1 = ii[lo]
            i2, t2 = ii[lo + 1]
            # identify which entry (a,b) of the matrix this is
            a = 0 if i1 in [BOT[k][0] for k in range(6)] else 1
            b = 0 if t1 in [TOP[k][0] for k in range(6)] else 1
            nm = 'xr%d_%d%d' % (blk, b, a)
            XNAME[(blk, b, a)] = nm
            W('/-- Entry `(%d,%d)` of the vanishing rank-one sum at block %d. -/'
              % (b, a, blk))
            W('theorem %s (c d : SS.BitString 6 -> ℂ)' % nm)
            for u, (z, mu) in enumerate(used):
                W('    (h%d : offSum c d ef%d %s = 0)' % (u, nn, zname[z]))
            W('    : d z%d * star (c y%d) + d z%d * star (c y%d) = 0 := by'
              % (t1, i1, t2, i2))
            for u, (z, mu) in enumerate(used):
                W('  rw [ex%d_%s] at h%d' % (nn, zname[z], u))
            W('  linear_combination ' + ' + '.join(
                '(%s : ℂ) * h%d' % (mu, u) for u, (z, mu) in enumerate(used)))
            W('')
YM = {3: ('000110', '001001'), 4: ('000101', '001010'), 5: ('000011', '001100')}
for j in (3, 4, 5):
    for b, m in ((0, YM[j][0]), (1, YM[j][1])):
        nn = mid[m]
        W('/-- The scalar cross relation joining block %d to block %d. -/' % (b, j))
        W('theorem yr%d_%d (c d : SS.BitString 6 -> ℂ)' % (b, j))
        W('    (h : offSum c d ef%d %s = 0)' % (nn, zname[bits(0)]))
        W('    : star (%s) * %s + star (%s) * %s'
          % (PB(j), SB(b), QB(j), TB_(b)))
        W('      + (star (%s) * %s + star (%s) * %s) = 0 := by'
          % (PB(b), SB(j), QB(b), TB_(j)))
        W('  rw [ex%d_%s] at h' % (nn, zname[bits(0)]))
        W('  linear_combination h')
        W('')
W('/-! ## The no-go -/')
W('')
W('set_option maxHeartbeats 1000000 in')
W('/-- Orbit 33 admits no six-qubit `((6,2,3))` code. -/')
W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
W('    (hm : MomentSystem')
W('            %s' % ' '.join('(Complex.normSq (c y%d))' % k for k in range(n0)))
W('            %s)' % ' '.join('(Complex.normSq (d z%d))' % k for k in range(n1)))
for z in USE[MD]:
    W('    (Dg_%s : diagBot c ef0 %s = diagTop d ef0 %s)'
      % (zname[z], zname[z], zname[z]))
for m in CROSS:
    for z in USE[m]:
        W('    (E%d_%s : offSum c d ef%d %s = 0)'
          % (mid[m], zname[z], mid[m], zname[z]))
W('    : False := by')
for i in range(6):
    W('  have nc%dr : Complex.normSq (%s) + Complex.normSq (%s) = %s := by'
      % (i, PB(i), QB(i), RV[i]))
    W('    have h := blkc%d hm; linarith' % i)
    W('  have nc%d : %s * star (%s) + %s * star (%s) = (%s : ℂ) := by'
      % (i, PB(i), PB(i), QB(i), QB(i), RV[i]))
    W('    have hc := congrArg (fun x : Real => (x : ℂ)) nc%dr' % i)
    W('    push_cast at hc')
    W('    simp only [sq]')
    W('    linear_combination hc')
for i in (0, 3):
    W('  have nd%dr : Complex.normSq (%s) + Complex.normSq (%s) = %s := by'
      % (i, SB(i), TB_(i), RV[i]))
    W('    have h := blkd%d hm; linarith' % i)
    W('  have nd%d : %s * star (%s) + %s * star (%s) = (%s : ℂ) := by'
      % (i, SB(i), SB(i), TB_(i), TB_(i), RV[i]))
    W('    have hc := congrArg (fun x : Real => (x : ℂ)) nd%dr' % i)
    W('    push_cast at hc')
    W('    simp only [sq]')
    W('    linear_combination hc')
SUMP = ' + '.join('Complex.normSq (%s)' % PB(k) for k in range(6))
SUMQ = ' + '.join('Complex.normSq (%s)' % QB(k) for k in range(6))
CSUMP = ' + '.join('%s * star (%s)' % (PB(k), PB(k)) for k in range(6))
CSUMQ = ' + '.join('%s * star (%s)' % (QB(k), QB(k)) for k in range(6))
for nm, i, a, real_sum, cplx_sum, XX, YY in (
        ('r00_0', 0, 0, SUMP, CSUMP, PB, SB), ('r11_0', 0, 1, SUMQ, CSUMQ, QB, TB_),
        ('r00_3', 3, 0, SUMP, CSUMP, PB, SB)):
    src = {'r00_0': 'rr00_0', 'r11_0': 'rr11_0', 'r00_3': 'rr00_3'}[nm]
    W('  have %sr : Complex.normSq (%s) + Complex.normSq (%s)' % (nm, XX(i), YY(i)))
    W('      = (%s) * (%s) := by' % (2 * RV[i], real_sum))
    W('    have h := %s hm; linarith' % src)
    W('  have %s : %s * star (%s) + %s * star (%s)'
      % (nm, XX(i), XX(i), YY(i), YY(i)))
    W('      = (%s : ℂ) * (%s) := by' % (2 * RV[i], cplx_sum))
    W('    have hc := congrArg (fun x : Real => (x : ℂ)) %sr' % nm)
    W('    push_cast at hc')
    W('    simp only [sq]')
    W('    linear_combination hc')
for i in (0, 3):
    W('  have r01_%d := refl01_%d c d %s' % (i, i, ' '.join(DGN)))
W('  exact Block33.block_contradiction')
W('    %s' % ' '.join('(%s)' % PB(k) for k in range(6)))
W('    %s' % ' '.join('(%s)' % QB(k) for k in range(6)))
W('    %s' % ' '.join('(%s)' % SB(k) for k in range(6)))
W('    %s' % ' '.join('(%s)' % TB_(k) for k in range(6)))
W('    %s nd0 nd3' % ' '.join('nc%d' % k for k in range(6)))
W('    r00_0 r01_0 r11_0 r00_3 r01_3')
XARG = []
for blk in (1, 2):
    for (b, a) in ((0, 0), (1, 0), (0, 1), (1, 1)):
        nm = XNAME[(blk, b, a)]
        # the same-entry pair rides the weight-one flip, the mixed pair the weight-two
        m = ({True: '010000', False: '110000'} if blk == 1
             else {True: '001000', False: '101000'})[b == a]
        XARG.append('(%s c d %s)' % (nm, ' '.join(
            'E%d_%s' % (mid[m], zname[z]) for z in USE[m])))
W('    %s' % ' '.join(XARG[:4]))
W('    %s' % ' '.join(XARG[4:]))
YARG = []
for j in (3, 4, 5):
    for b in (0, 1):
        YARG.append('(yr%d_%d c d E%d_%s)'
                    % (b, j, mid[YM[j][b]], zname[bits(0)]))
W('    %s' % ' '.join(YARG))
W('')
W('end')
W('')
W('end SixQubit.Orbit33')
io.open('gen16_end.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('end: %d lines; XNAME %s' % (len(L), sorted(XNAME)))
