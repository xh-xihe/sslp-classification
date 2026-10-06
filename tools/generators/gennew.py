"""Emit a complete kernel-only Lean module for an orbit closed by an
ISOLATION CERTIFICATE: a rational combination of admissible dressings that
isolates one incidence monomial, whose two endpoint probabilities the moment
polytope forces to fixed positive values.
"""
import io
import json
import sys
from itertools import combinations

import sympy as sp

NL = chr(10)
CERTS = json.loads(io.open('newcerts.json', encoding='utf-8').read())

BOOL = {'0': 'false', '1': 'true '}


def bsline(name, s):
    return ('def %s : SS.BitString 6 := bs %s  -- %s'
            % (name, ' '.join(BOOL[ch] for ch in s), s))


def emit(oid, C):
    q, a, d = C['q'], C['a'], C['d']
    S0, S1 = C['S0'], C['S1']
    n0, n1 = len(S0), len(S1)
    e, inc = C['e'], [tuple(t) for t in C['inc']]
    kk, ii, tt = C['k'], C['i'], C['t']
    used = [(z, sp.Rational(m)) for z, m in C['used']]
    pk, qk = sp.Rational(C['pk']), sp.Rational(C['qk'])
    bits = lambda s: [int(ch) for ch in s]
    dot = lambda z, x: sum(bits(z)[r] * bits(x)[r] for r in range(6)) % 2

    qs = ' '.join('q%d' % r for r in range(n0))
    rs = ' '.join('r%d' % r for r in range(n1))
    allv = qs + ' ' + rs
    L, W = [], None
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
    W('The flip mask %s has %d incidences on the two fibers.  A rational' % (e, len(inc)))
    W('combination of %d admissible dressings isolates the single monomial' % len(used))
    W('at (%s, %s), while the moment polytope pins its two endpoint' % (S0[ii], S1[tt]))
    W('probabilities to %s and %s.  Both are positive, so the isolated' % (pk, qk))
    W('monomial cannot vanish.')
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
    zall = sorted({z for z, _ in used})
    zname = {z: 'w%d' % r for r, z in enumerate(zall)}
    for z in zall:
        W(bsline(zname[z], z))
    for z in zall:
        for _, t2 in inc:
            W('theorem sg_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (zname[z], t2, zname[z], t2, BOOL['1' if dot(z, S1[t2]) else '0'].strip()))
    W('')
    W('/-! ## The moment system -/')
    W('')
    W('/-- The two normalizations, the twenty-one moment equalities, and the')
    W('nonnegativity of every probability. -/')
    W('structure MomentSystem (%s : Real) : Prop where' % allv)
    W('  n0 : %s = 1' % ' + '.join('q%d' % r for r in range(n0)))
    W('  n1 : %s = 1' % ' + '.join('r%d' % r for r in range(n1)))
    idx = [(i2,) for i2 in range(6)] + list(combinations(range(6), 2))
    for T in idx:
        lhs = [r for r in range(n0) if all(S0[r][j] == '1' for j in T)]
        rhs = [r for r in range(n1) if all(S1[r][j] == '1' for j in T)]
        nm = 'm%s' % ''.join(str(j + 1) for j in T)
        W('  %s : %s = %s'
          % (nm,
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
    W('/-- The two endpoint probabilities of the isolated incidence are forced. -/')
    W('theorem MomentSystem.endpoints {%s : Real}' % allv)
    W('    (h : MomentSystem %s) :' % allv)
    W('    q%d = %s ∧ r%d = %s := by' % (ii, pk, tt, qk))
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  refine ⟨?_, ?_⟩ <;> linarith')
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
    for r, (z, m) in enumerate(used):
        W('    (h%d : offSum c d ef %s = 0)' % (r, zname[z]))
    W('    : False := by')
    for r, (z, m) in enumerate(used):
        W('  rw [ex_%s] at h%d' % (zname[z], r))
    W('  have key : star (c y%d) * d z%d = 0 := by' % (ii, tt))
    W('    linear_combination ' + ' + '.join(
        '(%s : ℂ) * h%d' % (m, r) for r, (z, m) in enumerate(used)))
    W('  obtain ⟨hp, hq⟩ := hm.endpoints')
    W('  rcases mul_eq_zero.mp key with hh | hh')
    W('  · rw [show c y%d = 0 from by simpa using congrArg star hh] at hp' % ii)
    W('    simp at hp')
    W('  · rw [hh] at hq')
    W('    simp at hq')
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % oid)
    return NL.join(L) + NL


if __name__ == '__main__':
    for oid in sys.argv[1:]:
        src = emit(int(oid), CERTS[oid])
        p = 'Orbit%s.lean' % oid
        io.open(p, 'w', encoding='utf-8').write(src)
        print('%s : %d lines' % (p, src.count(NL)))
