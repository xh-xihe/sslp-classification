"""Dump phase-2 certificates (isolate several incidences, endpoints linearly
tied, vanishing set contradicts the moment system) and emit Lean modules."""
import io
import json
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
sys.path.insert(0, '.')
from orbit import fiber

NL = chr(10)
BOOL = {'0': 'false', '1': 'true '}
ORB = {52: (6, [1, 2, 3, 3, 4, 4], 2, '000001'),
       44: (6, [1, 1, 2, 3, 3, 4], 3, '000010'),
       46: (6, [1, 2, 2, 2, 3, 3], 3, '000001')}

bits = lambda s: [int(ch) for ch in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
supp = lambda s: {i for i, ch in enumerate(s) if ch == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dressings = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]


def bsline(nm, s):
    return 'def %s : SS.BitString 6 := bs %s  -- %s' % (
        nm, ' '.join(BOOL[c] for c in s), s)


def build(oid):
    q, a, d, e = ORB[oid]
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    n0, n1 = len(S0), len(S1)
    inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
    Z = dressings(e)
    W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
    # affine solution of the moment system, to read off the endpoint ratios
    rows, rhs = [[1] * n0 + [0] * n1, [0] * n0 + [1] * n1], [1, 1]
    idx = [(i,) for i in range(6)] + list(combinations(range(6), 2))
    for T in idx:
        rows.append([1 if all(S0[r][j] == '1' for j in T) else 0 for r in range(n0)]
                    + [-1 if all(S1[r][j] == '1' for j in T) else 0 for r in range(n1)])
        rhs.append(0)
    Mm = sp.Matrix(rows)
    v = sp.Matrix(sp.symbols('t0:%d' % (n0 + n1)))
    sol = sp.solve([sp.Eq(x, y) for x, y in zip(Mm * v, sp.Matrix(rhs))],
                   list(v), dict=True)[0]
    expr = [sp.expand(sol.get(v[k], v[k])) for k in range(n0 + n1)]

    cert = []
    zused = set()
    for k, (i2, t2) in enumerate(inc):
        tgt = sp.Matrix([1 if r == k else 0 for r in range(len(inc))])
        try:
            mu = W.T.gauss_jordan_solve(tgt)[0]
        except ValueError:
            continue
        mu = mu.subs({s: 0 for s in mu.free_symbols})
        used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z)) if mu[r] != 0]
        pe, qe = expr[i2], expr[n0 + t2]
        if qe == 0:
            continue
        lam = sp.simplify(pe / qe)
        if not (lam.is_number and lam > 0):
            continue
        cert.append((k, i2, t2, sp.Rational(lam), used))
        zused |= {z for z, _ in used}
    return q, a, d, e, S0, S1, inc, sorted(zused), cert, idx


def emit(oid):
    q, a, d, e, S0, S1, inc, zall, cert, idx = build(oid)
    n0, n1 = len(S0), len(S1)
    zname = {z: 'w%d' % r for r, z in enumerate(zall)}
    qs = ' '.join('q%d' % r for r in range(n0))
    rs = ' '.join('r%d' % r for r in range(n1))
    allv = qs + ' ' + rs
    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit %d' % oid)
    W('')
    W('Orbit %d of `six_qubit_sslp.tex`: q = %d, angle vector' % (oid, q))
    W('a = (%s), residues 0 and %d.' % (', '.join(map(str, a)), d))
    W('')
    W('The flip mask %s has %d incidences, and the admissible dressings' % (e, len(inc)))
    W('isolate %d of them individually.  For each isolated incidence the' % len(cert))
    W('moment system ties the two endpoint probabilities by a positive ratio,')
    W('so either branch of `mul_eq_zero` kills both.  The resulting vanishing')
    W('set is inconsistent with the moment system.')
    W('')
    W('Everything computational is decided by the Lean kernel; `native_decide`')
    W('is not used.')
    W('-/')
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
    W('/-! ## The flip mask and its incidences -/')
    W('')
    W(bsline('ef', e))
    W('')
    W('theorem incidence :')
    W('    S1.filter (fun y => SS.bxor y ef ∈ S0) = {%s} := by decide'
      % ', '.join('z%d' % t for _, t in inc))
    W('')
    for i2, t2 in inc:
        W('theorem flip_z%d : SS.bxor z%d ef = y%d := by decide' % (t2, t2, i2))
    W('')
    for z in zall:
        W(bsline(zname[z], z))
    for z in zall:
        for _, t2 in inc:
            W('theorem sg_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (zname[z], t2, zname[z], t2,
                 'true' if dot(z, S1[t2]) else 'false'))
    W('')
    W('/-! ## The moment system -/')
    W('')
    W('structure MomentSystem (%s : Real) : Prop where' % allv)
    W('  n0 : %s = 1' % ' + '.join('q%d' % r for r in range(n0)))
    W('  n1 : %s = 1' % ' + '.join('r%d' % r for r in range(n1)))
    for T in idx:
        lhs = [r for r in range(n0) if all(S0[r][j] == '1' for j in T)]
        rhs2 = [r for r in range(n1) if all(S1[r][j] == '1' for j in T)]
        W('  m%s : %s = %s'
          % (''.join(str(j + 1) for j in T),
             ' + '.join('q%d' % r for r in lhs) or '0',
             ' + '.join('r%d' % r for r in rhs2) or '0'))
    W('')
    for r in range(n0):
        W('  nq%d : 0 ≤ q%d' % (r, r))
    for r in range(n1):
        W('  nr%d : 0 ≤ r%d' % (r, r))
    W('')
    fields = (['n0', 'n1'] + ['m%s' % ''.join(str(j + 1) for j in T) for T in idx]
              + ['nq%d' % r for r in range(n0)] + ['nr%d' % r for r in range(n1)])
    for k, i2, t2, lam, _ in cert:
        W('/-- Endpoint ratio at incidence %d. -/' % k)
        W('theorem MomentSystem.ratio%d {%s : Real} (h : MomentSystem %s) :'
          % (k, allv, allv))
        W('    q%d = (%s) * r%d := by' % (i2, lam, t2))
        W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
        W('  linarith')
        W('')
    W('/-- Every isolated bottom probability vanishing is impossible. -/')
    W('theorem MomentSystem.absurd_zero {%s : Real} (h : MomentSystem %s)'
      % (allv, allv))
    for k, i2, t2, lam, _ in cert:
        W('    (v%d : q%d = 0)' % (k, i2))
    W('    : False := by')
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  linarith')
    W('')
    W('/-! ## The Walsh expansions -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    for z in zall:
        body = ' '.join('%s star (c y%d) * d z%d'
                        % ('-' if dot(z, S1[t2]) else '+', i2, t2)
                        for i2, t2 in inc).lstrip('+ ')
        W('theorem ex_%s (c d : SS.BitString 6 -> ℂ) :' % zname[z])
        W('    offSum c d ef %s = %s := by' % (zname[z], body))
        W('  unfold offSum')
        W('  rw [incidence]')
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(inc) - 1))
          + (', ' if len(inc) > 1 else '') + 'Finset.sum_singleton]')
        W('  rw [' + ', '.join('flip_z%d' % t2 for _, t2 in inc) + ']')
        lem = ['sg_%s_%d' % (zname[z], t2) for _, t2 in inc]
        if any(dot(z, S1[t2]) for _, t2 in inc):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S1[t2]) for _, t2 in inc):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
    W('/-! ## The no-go -/')
    W('')
    W('/-- **Orbit %d is impossible.** -/' % oid)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
    for r, z in enumerate(zall):
        W('    (h%d : offSum c d ef %s = 0)' % (r, zname[z]))
    W('    : False := by')
    for r, z in enumerate(zall):
        W('  rw [ex_%s] at h%d' % (zname[z], r))
    for k, i2, t2, lam, used in cert:
        W('  have key%d : star (c y%d) * d z%d = 0 := by' % (k, i2, t2))
        W('    linear_combination ' + ' + '.join(
            '(%s : ℂ) * h%d' % (m, zall.index(z)) for z, m in used))
        W('  have rat%d := hm.ratio%d' % (k, k))
        W('  have van%d : Complex.normSq (c y%d) = 0 := by' % (k, i2))
        W('    rcases mul_eq_zero.mp key%d with hh | hh' % k)
        W('    · have : c y%d = 0 := by simpa using congrArg star hh' % i2)
        W('      simp [this]')
        W('    · have hz : Complex.normSq (d z%d) = 0 := by simp [hh]' % t2)
        W('      rw [rat%d, hz]; ring' % k)
    W('  exact hm.absurd_zero ' + ' '.join('van%d' % k for k, _, _, _, _ in cert))
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % oid)
    return NL.join(L) + NL


if __name__ == '__main__':
    for o in sys.argv[1:]:
        src = emit(int(o))
        io.open('Orbit%s.lean' % o, 'w', encoding='utf-8').write(src)
        print('Orbit%s.lean : %d lines' % (o, src.count(NL)))
