"""Transcription layer for orbit 29."""
import io
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from o29data import (S0, S1, n0, n1, Q, R, V, Am, bv, enames, fields,
                     VERT, EDGE, EMASK, FAM, INC, MASKS, edge_combo, solve_row)
from scan import bits, xor, dot
from kl import dressings_full
from cert import reduce_mod_linear

NL = chr(10)
AVEC, QQ, DELTA = [1, 1, 1, 1, 2, 2], 4, 1
TFR = {3: (0, 1, 2), 5: (0, 1, 4), 6: (0, 2, 4), 7: (1, 2, 4)}
FAMM = {3: ('100001', '100010', '000001', '000010'),
        5: ('010001', '010010', '000001', '000010'),
        6: ('001001', '001010', '000001', '000010'),
        7: ('000101', '000110', '000001', '000010')}
USE = {}
for m, n in EMASK:
    e, cmb = edge_combo(m, n)
    USE.setdefault(e, set()).update(z for z, _ in cmb)
for n, (eu, ec, zu, zc) in FAMM.items():
    USE.setdefault(eu, set()).update([bits(0), zu])
    USE.setdefault(ec, set()).update([bits(0), zc])
USE = {k: sorted(v) for k, v in USE.items()}
ORDER = sorted(USE)
mid = {m: k for k, m in enumerate(ORDER)}
zall = sorted({z for v in USE.values() for z in v})
zname = {z: 'w%d' % k for k, z in enumerate(zall)}
blit = lambda s: ' '.join('true ' if c == '1' else 'false' for c in s)

L = []
W = L.append
W('import Mathlib')
W('')
W('import SS.FullKL')
W('import SixQubit.Common')
W('import SixQubit.Pair29')
W('')
W('/-!')
W('# Six-qubit no-go for moment orbit 29')
W('')
W('Orbit 29 of `six_qubit_sslp_v7.tex`: q = 4, angle vector a = (1, 1, 1, 1, 2, 2),')
W('residues 0 and 1, fibers of size sixteen each.')
W('')
W('Both fibers are closed under `X_5 X_6`, so each splits into eight pairs.  Read')
W('a pair as a vector in `Cx^2`; then every two-term Knill-Laflamme relation is an')
W('orthogonality, and the twelve that survive realise exactly the six edges of')
W('`K_4` on the four top pairs carrying them.  The moment system supplies the')
W('probabilities, including the uniform identity `P_e = Q_n + Q_m - 1/4` for the')
W('bottom pair on edge `{n,m}`.  `SixQubit.Pair29.pair_contradiction` closes it.')
W('')
W('Everything computational is decided by the Lean kernel; `native_decide` is')
W('not used.')
W('-/')
W('')
W('namespace SixQubit.Orbit29')
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
for m in ORDER:
    W('def ef%d : SS.BitString 6 := bs %s  -- mask %s' % (mid[m], blit(m), m))
for z in zall:
    W('def %s : SS.BitString 6 := bs %s  -- dressing %s' % (zname[z], blit(z), z))
W('')
W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
W('')
W('/-- `z * star z` is the squared modulus. -/')
W('theorem sq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by')
W('  rw [mul_comm, Complex.normSq_eq_conj_mul_self]; rfl')
W('')
for m in ORDER:
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
for m in ORDER:
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
io.open('gen29c_head.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('head+expansions: %d lines, %d masks, %d dressings' % (len(L), len(ORDER), len(zall)))

# ----------------------------------------------------------------- part 2
PARTNER = {3: 4, 5: 2, 6: 1, 7: 0}
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
    W('  linear_combination ' + ' + '.join(
        '(%s) * %s' % (sp.printing.sstr(cof[row]).replace('**', '^'), enames[row])
        for row in range(Am.rows) if cof[row] != 0))
    W('')


QP = {n: R[2 * n] + R[2 * n + 1] for n in range(8)}
emit_real('mq', sum(QP[n] for n in VERT) - sp.Rational(3, 4),
          'The four top pairs carrying edges hold three quarters of the weight.')
emit_real('me', sum(R[2 * n] - R[2 * n + 1] for n in VERT),
          'Their pair differences cancel.')
emit_real('mn7', Q[14] + Q[15] - sp.Rational(1, 4),
          'The pinned bottom pair holds a quarter.')
for m, (n, p) in EDGE.items():
    emit_real('mc%d' % m, (Q[2 * m] + Q[2 * m + 1]) - QP[n] - QP[p] + sp.Rational(1, 4),
              'Bottom pair %d sits on edge {%d,%d}.' % (m, n, p))
for n in VERT:
    emit_real('mp%d' % n, QP[n] + QP[PARTNER[n]] - sp.Rational(1, 4),
              'Top pair %d and its partner %d hold a quarter.' % (n, PARTNER[n]))
W('/-! ## The orthogonality relations -/')
W('')
for m, n in sorted(EMASK):
    e, cmb = edge_combo(m, n)
    nn = mid[e]
    W('/-- Bottom pair %d is orthogonal to top pair %d. -/' % (m, n))
    W('theorem orth%d_%d (c d : SS.BitString 6 -> ℂ)' % (m, n))
    for u, (z, _) in enumerate(cmb):
        W('    (h%d : offSum c d ef%d %s = 0)' % (u, nn, zname[z]))
    W('    : star (c y%d) * d z%d + star (c y%d) * d z%d = 0 := by'
      % (2 * m, 2 * n, 2 * m + 1, 2 * n + 1))
    for u, (z, _) in enumerate(cmb):
        W('  rw [ex%d_%s] at h%d' % (nn, zname[z], u))
    W('  linear_combination ' + ' + '.join(
        '(%s : ℂ) * h%d' % (co, u) for u, (z, co) in enumerate(cmb)))
    W('')
W('/-! ## The Walsh combinations at the pinned pair -/')
W('')
NAMES = {}
for n in VERT:
    eu, ec, zu, zc = FAMM[n]
    for tag, e, z, keep in (('A', eu, zu, 0), ('B', eu, zu, 1),
                            ('C', ec, zc, 0), ('D', ec, zc, 1)):
        nn = mid[e]
        terms = [(i, t) for i, t in INC[e] if dot(z, S1[t]) == keep]
        assert len(terms) == 4, (n, tag, terms)
        body = ' + '.join('star (c y%d) * d z%d' % (i, t) for i, t in terms)
        W('theorem wc%d%s (c d : SS.BitString 6 -> ℂ)' % (n, tag))
        W('    (hA : offSum c d ef%d %s = 0)' % (nn, zname[bits(0)]))
        W('    (hB : offSum c d ef%d %s = 0)' % (nn, zname[z]))
        W('    : %s = 0 := by' % body)
        W('  rw [ex%d_%s] at hA' % (nn, zname[bits(0)]))
        W('  rw [ex%d_%s] at hB' % (nn, zname[z]))
        sgn = '+' if keep == 0 else '-'
        W('  linear_combination (1/2 : ℂ) * hA %s (1/2 : ℂ) * hB' % sgn)
        W('')
        NAMES[(n, tag)] = (nn, z)
io.open('gen29c_sys.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('system+relations: %d lines' % len(L))

# ----------------------------------------------------------------- part 3
L = []
W = L.append
NS = lambda t: 'Complex.normSq (%s)' % t
DZ = lambda j: 'd z%d' % j
CY = lambda i: 'c y%d' % i
QR = {n: '(%s + %s)' % (NS(DZ(2 * n)), NS(DZ(2 * n + 1))) for n in range(8)}
W('/-! ## The no-go -/')
W('')
W('set_option maxHeartbeats 2000000 in')
W('/-- Orbit 29 admits no six-qubit `((6,2,3))` code. -/')
W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
W('    (hm : MomentSystem')
W('            %s' % ' '.join('(%s)' % NS(CY(k)) for k in range(n0)))
W('            %s)' % ' '.join('(%s)' % NS(DZ(k)) for k in range(n1)))
for m in ORDER:
    for z in USE[m]:
        W('    (E%d_%s : offSum c d ef%d %s = 0)' % (mid[m], zname[z], mid[m], zname[z]))
W('    : False := by')
W('  have n7 : %s * star (%s) + %s * star (%s) = 1/4 := by'
  % (CY(14), CY(14), CY(15), CY(15)))
W('    have hr : %s + %s = 1/4 := by have h := mn7 hm; linarith' % (NS(CY(14)), NS(CY(15))))
W('    have hc := congrArg (fun x : Real => (x : ℂ)) hr')
W('    push_cast at hc')
W('    simp only [sq]')
W('    linear_combination hc')
for n in VERT:
    W('  have nq%d : %s * star (%s) + %s * star (%s) = ((%s : Real) : ℂ) := by'
      % (n, DZ(2 * n), DZ(2 * n), DZ(2 * n + 1), DZ(2 * n + 1), QR[n][1:-1]))
    W('    simp only [sq]; push_cast; ring')
for m, (n, p) in EDGE.items():
    W('  have nc%d : %s * star (%s) + %s * star (%s)'
      % (m, CY(2 * m), CY(2 * m), CY(2 * m + 1), CY(2 * m + 1)))
    W('      = ((%s + %s - 1/4 : Real) : ℂ) := by' % (QR[n], QR[p]))
    W('    have hr : %s + %s = %s + %s - 1/4 := by'
      % (NS(CY(2 * m)), NS(CY(2 * m + 1)), QR[n], QR[p]))
    W('      have h := mc%d hm; linarith' % m)
    W('    have hc := congrArg (fun x : Real => (x : ℂ)) hr')
    W('    push_cast at hc')
    W('    simp only [sq]')
    W('    push_cast')
    W('    linear_combination hc')
W('  have qsum : %s = 3/4 := by' % ' + '.join(QR[n] for n in VERT))
W('    have h := mq hm; linarith')
W('  have esum : (%s * star (%s) - %s * star (%s))'
  % (DZ(6), DZ(6), DZ(7), DZ(7)))
for n in VERT[1:]:
    W('      + (%s * star (%s) - %s * star (%s))'
      % (DZ(2 * n), DZ(2 * n), DZ(2 * n + 1), DZ(2 * n + 1)))
W('      = 0 := by')
W('    have hr : %s = 0 := by have h := me hm; linarith'
  % ' + '.join('(%s - %s)' % (NS(DZ(2 * n)), NS(DZ(2 * n + 1))) for n in VERT))
W('    have hc := congrArg (fun x : Real => (x : ℂ)) hr')
W('    push_cast at hc')
W('    simp only [sq]')
W('    linear_combination hc')
for n in VERT:
    W('  have qle%d : %s ≤ 1/4 := by' % (n, QR[n]))
    W('    have h := mp%d hm' % n)
    W('    have h1 := Complex.normSq_nonneg (%s)' % DZ(2 * PARTNER[n]))
    W('    have h2 := Complex.normSq_nonneg (%s)' % DZ(2 * PARTNER[n] + 1))
    W('    linarith')
W('  exact SixQubit.Pair29.pair_contradiction')
W('    ' + ' '.join('(%s) (%s)' % (CY(2 * m), CY(2 * m + 1)) for m in range(1, 8)))
W('    ' + ' '.join('(%s) (%s) (%s)' % (DZ(2 * n), DZ(2 * n + 1), QR[n]) for n in VERT))
W('    ' + ' '.join('(%s) (%s)' % (DZ(2 * k), DZ(2 * k + 1)) for k in (0, 1, 2, 4)))
W('    n7 ' + ' '.join('nq%d' % n for n in VERT))
W('    ' + ' '.join('nc%d' % m for m in range(1, 7)) + ' qsum esum')
for m in range(1, 7):
    nn, pp = EDGE[m]
    for tgt in (nn, pp):
        e, cmb = edge_combo(m, tgt)
        W('    (orth%d_%d c d %s)'
          % (m, tgt, ' '.join('E%d_%s' % (mid[e], zname[z]) for z, _ in cmb)))
for n in VERT:
    eu, ec, zu, zc = FAMM[n]
    for tag, e, z in (('A', eu, zu), ('B', eu, zu), ('C', ec, zc), ('D', ec, zc)):
        W('    (wc%d%s c d E%d_%s E%d_%s)'
          % (n, tag, mid[e], zname[bits(0)], mid[e], zname[z]))
W('    ' + ' '.join('qle%d' % n for n in VERT))
W('')
W('end')
W('')
W('end SixQubit.Orbit29')
io.open('gen29c_end.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('main: %d lines' % len(L))
