"""Generate `SixQubit/Orbit5.lean` from the verified orbit-5 data.

Everything that is a sum over the fibers -- the incidence sets, the Walsh
expansions of the off-diagonal and diagonal rows, the moment system, and the
rational combinations that isolate each entry of the marginal on the free pair
-- is emitted here rather than typed by hand.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from gen5orbit import (Y, Z, EFLIP, AFLIP, two_flip, off_row, diag_row)  # noqa: E402

L = []
w = L.append

TAILNAME = ['u', 'a1', 'a2', 'a3', 'a4']
TOPNAME = ['b1', 'b2', 'b3', 'b4', 'v']
VEC = ['uu', 'aa1', 'aa2', 'aa3', 'aa4']
TVEC = ['bb1', 'bb2', 'bb3', 'bb4', 'vv']

# dressing masks used
W0 = '000000'
AW = ['000000', '100000', '010000', '110000']    # dressings inside A
AWNAME = ['w0', 'w1', 'w2', 'w3']
AWBITS = [0, 2, 1, 3]                            # alpha-bit pattern of each dressing


def bsdef(name, s, comment=True):
    body = ' '.join('true ' if ch == '1' else 'false' for ch in s).rstrip()
    pad = ' ' * max(1, 30 - len('bs ' + body))
    line = 'def %s : SS.BitString 6 := bs %s' % (name, body)
    if comment:
        line += '  -- ' + s
    return line


def sgn_lit(s):
    return 'true' if s else 'false'


def signmul_args(signs):
    out = []
    if any(x < 0 for x in signs):
        out.append('SixQubit.signMul_true')
    if any(x > 0 for x in signs):
        out.append('SixQubit.signMul_false')
    return out


def signed(terms):
    """render a list of (sign, string) as a Lean sum"""
    out = ''
    for k, (s, t) in enumerate(terms):
        if k == 0:
            out += ('-' + t) if s < 0 else t
        else:
            out += (' - ' if s < 0 else ' + ') + t
    return out


def wrap(prefix, body, cont, sep=' + ', tail=''):
    parts = body.split(sep)
    line = prefix + parts[0]
    for p in parts[1:]:
        piece = sep.strip() + ' ' + p
        if len(line) + len(piece) + 1 > 104:
            w(line)
            line = cont + piece
        else:
            line = line + ' ' + piece
    w(line + tail)


def peel(n):
    return ('rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (n - 1))
            + ', Finset.sum_singleton]')


# --------------------------------------------------------------------- header
w('import Mathlib')
w('')
w('import SS.FullKL')
w('import SixQubit.Common')
w('import SixQubit.Trace5')
w('import SixQubit.Flip5')
w('')
w('set_option maxHeartbeats 2000000')
w('')
w('/-!')
w('# Six-qubit moment orbit 5: the free-pair frame reduction')
w('')
w('Orbit 5 of `six_qubit_sslp.tex`: q = 3, angle vector a = (0, 0, 1, 1, 1, 1),')
w('residues 0 and 1.  Qubits 0 and 1 carry angle zero, so the amplitudes group')
w('into vectors of `ℂ⁴`.  Writing `V = {1,2,3,4}` for the four active')
w('coordinates, the active tails of the two fibers are')
w('')
w('```')
w('T0 = {0000, 0111, 1011, 1101, 1110},   T1 = {1000, 0100, 0010, 0001, 1111},')
w('```')
w('')
w('so a candidate pair is')
w('')
w('```')
w('|0_L> = u (x) 0000 + Σᵢ aᵢ (x) ê_i ,   |1_L> = Σᵢ bᵢ (x) e_i + v (x) 1111 .')
w('```')
w('')
w('This module certifies, from the moment polytope and from the weight-at-most-two')
w('Knill--Laflamme rows only:')
w('')
w('* the ten squared norms `‖u‖² = ‖v‖² = 1/3`, `‖aᵢ‖² = ‖bᵢ‖² = 1/6`;')
w('* the anchor orthogonalities `u† bᵢ = 0` and `aᵢ† v = 0`;')
w('* the two-flip relations `aᵢ† bⱼ + aⱼ† bᵢ = 0` for `i ≠ j`;')
w('* equality of the two reduced density matrices on the free pair;')
w('')
w('and then, via `SixQubit.Trace5.cs_tight`, the *frame reduction*')
w('')
w('```')
w('u† aᵢ = 0   (1 ≤ i ≤ 4)   and   Σᵢ aᵢ aᵢ† = Σᵢ bᵢ bᵢ† .')
w('```')
w('')
w('Finally the *dressed* one-flip rows -- the weight-two errors `Z_A Xᵢ`, `X_A Xᵢ`')
w('and `Y_A Xᵢ` for either zero-angle qubit `A` -- feed the two-qubit flip-kernel')
w('dichotomy `SixQubit.Flip5.core`, which closes the orbit: either the Bell branch,')
w('where the twelve cross orthogonalities `aᵢ† bⱼ = 0` reach')
w('`SixQubit.Trace5.bell_contradiction`, or the line branch, where all ten vectors')
w('collapse onto one line of `u^⊥` and the two-flip relations become the odd')
w('triangle of `SixQubit.Triangle`.  The headline is `no_go_of_moments`.')
w('')
w('Everything combinatorial is decided by the Lean kernel; `native_decide` is not')
w('used.')
w('-/')
w('')
w('namespace SixQubit.Orbit5')
w('')
w('open scoped BigOperators')
w('open scoped ComplexConjugate')
w('')
w('noncomputable section')
w('')
w('/-! ## The two fibers -/')
w('')
w('def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]')
w('')
for i, s in enumerate(Y):
    w(bsdef('y%d' % i, s))
w('')
for i, s in enumerate(Z):
    w(bsdef('z%d' % i, s))
w('')
w('def S0 : Finset (SS.BitString 6) := {' + ', '.join('y%d' % i for i in range(20)) + '}')
w('def S1 : Finset (SS.BitString 6) := {' + ', '.join('z%d' % i for i in range(20)) + '}')
w('')
w('def av : Fin 6 -> ZMod 3 := ![0, 0, 1, 1, 1, 1]')
w('')
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
w('/-! ## Flip masks and dressings -/')
w('')
for i, e in enumerate(EFLIP):
    w(bsdef('f%d' % (i + 1), e))
PAIR = []
for i in range(4):
    for j in range(i + 1, 4):
        PAIR.append((i, j))
for (i, j) in PAIR:
    w(bsdef('g%d%d' % (i + 1, j + 1), two_flip(i, j)))
for nm, e in [('p1', AFLIP['A1']), ('p2', AFLIP['A2']), ('p3', AFLIP['A3'])]:
    w(bsdef(nm, e))
for nm, s in zip(AWNAME, AW):
    w(bsdef(nm, s))
w('')

# ---------------------------------------------------------- off-diagonal layer
w('/-! ## The off-diagonal layer -/')
w('')
w('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
w('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
w('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
w('')

OFFMASKS = [('f%d' % (i + 1), e) for i, e in enumerate(EFLIP)]
OFFMASKS += [('g%d%d' % (i + 1, j + 1), two_flip(i, j)) for (i, j) in PAIR]

# rows: (mask name, mask string, dressing name, dressing string)
ROWS = []
for i, e in enumerate(EFLIP):
    ROWS.append(('f%d' % (i + 1), e, 'w0', W0))
    j = (i + 1) % 4
    ROWS.append(('f%d' % (i + 1), e, 'f%d' % (j + 1), EFLIP[j]))
for (i, j) in PAIR:
    ROWS.append(('g%d%d' % (i + 1, j + 1), two_flip(i, j), 'w0', W0))

for (mn, e) in OFFMASKS:
    inc = off_row(e, W0)
    tops = [t for (_, _, t) in inc]
    w('theorem inc_%s :' % mn)
    w('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
      % (mn, ', '.join('z%d' % t for t in tops)))
    for (s, b, t) in inc:
        w('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide' % (mn, t, t, mn, b))
w('')

for (mn, e, dn, dz) in ROWS:
    inc = off_row(e, dz)
    tops = [t for (_, _, t) in inc]
    for (s, b, t) in inc:
        w('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
          % (mn, dn, t, dn, t, sgn_lit(s < 0)))
    w('theorem ex_%s_%s (c d : SS.BitString 6 -> ℂ) :' % (mn, dn))
    body = signed([(s, 'star (c y%d) * d z%d' % (b, t)) for (s, b, t) in inc])
    wrap('    offSum c d %s %s = ' % (mn, dn), body, '      ', sep=' + ', tail=' := by')
    w('  unfold offSum')
    w('  rw [inc_%s]' % mn)
    w('  ' + peel(len(inc)))
    w('  rw [' + ', '.join('flip_%s_%d' % (mn, t) for t in tops) + ']')
    w('  simp only [' + ', '.join(['sg_%s_%s_%d' % (mn, dn, t) for t in tops]
      + signmul_args([s for (s, _, _) in inc])) + ']')
    w('  try ring')
w('')

# ------------------------------------------------------------- diagonal layer
w('/-! ## The diagonal layer on the free pair -/')
w('')
w('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
w('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
w('      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)')
w('')
w('def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
w('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
w('      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)')
w('')

PMASKS = [('p1', AFLIP['A1']), ('p2', AFLIP['A2']), ('p3', AFLIP['A3'])]
for (mn, e) in PMASKS:
    db = diag_row(e, W0, False)
    dt = diag_row(e, W0, True)
    w('theorem dincB_%s : S0.filter (fun x => SS.bxor x %s ∈ S0) = {%s} := by decide'
      % (mn, mn, ', '.join('y%d' % i for (_, _, i) in db)))
    w('theorem dincT_%s : S1.filter (fun y => SS.bxor y %s ∈ S1) = {%s} := by decide'
      % (mn, mn, ', '.join('z%d' % i for (_, _, i) in dt)))
    for (_, p, i) in db:
        w('theorem dfB_%s_%d : SS.bxor y%d %s = y%d := by decide' % (mn, i, i, mn, p))
    for (_, p, i) in dt:
        w('theorem dfT_%s_%d : SS.bxor z%d %s = z%d := by decide' % (mn, i, i, mn, p))
w('')

for (mn, e) in PMASKS:
    for (dn, dz) in zip(AWNAME, AW):
        db = diag_row(e, dz, False)
        dt = diag_row(e, dz, True)
        for (s, p, i) in db:
            w('theorem dsB_%s_%s_%d : SS.bdot %s y%d = %s := by decide'
              % (mn, dn, i, dn, i, sgn_lit(s < 0)))
        w('theorem dexB_%s_%s (c : SS.BitString 6 -> ℂ) :' % (mn, dn))
        body = signed([(s, 'star (c y%d) * c y%d' % (p, i)) for (s, p, i) in db])
        wrap('    diagBot c %s %s = ' % (mn, dn), body, '      ', tail=' := by')
        w('  unfold diagBot')
        w('  rw [dincB_%s]' % mn)
        w('  ' + peel(len(db)))
        w('  rw [' + ', '.join('dfB_%s_%d' % (mn, i) for (_, _, i) in db) + ']')
        w('  simp only [' + ', '.join(['dsB_%s_%s_%d' % (mn, dn, i) for (_, _, i) in db]
          + signmul_args([s for (s, _, _) in db])) + ']')
        w('  try ring')
        for (s, p, i) in dt:
            w('theorem dsT_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (mn, dn, i, dn, i, sgn_lit(s < 0)))
        w('theorem dexT_%s_%s (dd : SS.BitString 6 -> ℂ) :' % (mn, dn))
        body = signed([(s, 'star (dd z%d) * dd z%d' % (p, i)) for (s, p, i) in dt])
        wrap('    diagTop dd %s %s = ' % (mn, dn), body, '      ', tail=' := by')
        w('  unfold diagTop')
        w('  rw [dincT_%s]' % mn)
        w('  ' + peel(len(dt)))
        w('  rw [' + ', '.join('dfT_%s_%d' % (mn, i) for (_, _, i) in dt) + ']')
        w('  simp only [' + ', '.join(['dsT_%s_%s_%d' % (mn, dn, i) for (_, _, i) in dt]
          + signmul_args([s for (s, _, _) in dt])) + ']')
        w('  try ring')
w('')

# --------------------------------------------------------------- moment system
w('/-! ## The moment system -/')
QV = ['q%d' % i for i in range(20)]
RV = ['r%d' % i for i in range(20)]
ALLV = QV + RV
MROWS = []
MROWS.append(('n0', ' + '.join(QV) + ' = 1'))
MROWS.append(('n1', ' + '.join(RV) + ' = 1'))
for i in range(6):
    lhs = ' + '.join(QV[k] for k, x in enumerate(Y) if x[i] == '1')
    rhs = ' + '.join(RV[k] for k, y in enumerate(Z) if y[i] == '1')
    MROWS.append(('m%d' % (i + 1), '%s = %s' % (lhs, rhs)))
for i in range(6):
    for j in range(i + 1, 6):
        lhs = ' + '.join(QV[k] for k, x in enumerate(Y) if x[i] == '1' and x[j] == '1')
        rhs = ' + '.join(RV[k] for k, y in enumerate(Z) if y[i] == '1' and y[j] == '1')
        lhs = lhs or '0'
        rhs = rhs or '0'
        MROWS.append(('m%d%d' % (i + 1, j + 1), '%s = %s' % (lhs, rhs)))
NAMES = [nm for nm, _ in MROWS]
NONNEG = [('n%s' % v, '0 ≤ %s' % v) for v in ALLV]
w('')
w('/-- The two normalizations, the six one-coordinate and the fifteen')
w('two-coordinate moment equalities, and the nonnegativity of every')
w('probability. -/')
wrap('structure MomentSystem (', ' '.join(ALLV), '    ', sep=' ',
     tail=' : Real) : Prop where')
for nm, eq in MROWS:
    wrap('  %s : ' % nm, eq, '      ')
w('')
for nm, eq in NONNEG:
    w('  %s : %s' % (nm, eq))
w('')
OBTAIN = '⟨' + ', '.join(NAMES + [nm for nm, _ in NONNEG]) + '⟩'
SIG = ' '.join(ALLV)
w('/-- The ten squared norms are pinned by the moment polytope. -/')
wrap('theorem MomentSystem.norms {', SIG, '    ', sep=' ', tail=' : Real}')
wrap('    (h : MomentSystem ', SIG, '      ', sep=' ', tail=') :')
NORMTARGETS = []
for t in range(5):
    NORMTARGETS.append('%s = %s' % (' + '.join(QV[4 * t + a] for a in range(4)),
                                    '1/3' if t == 0 else '1/6'))
for t in range(5):
    NORMTARGETS.append('%s = %s' % (' + '.join(RV[4 * t + a] for a in range(4)),
                                    '1/3' if t == 4 else '1/6'))
wrap('    ', ' ∧ '.join(NORMTARGETS), '      ', sep=' ∧ ', tail=' := by')
wrap('  obtain ', OBTAIN, '    ', sep=', ', tail=' := h')
w('  refine ⟨' + ', '.join(['?_'] * len(NORMTARGETS)) + '⟩ <;> linarith')
w('')
w('/-- The four diagonal entries of the reduced density matrix on the free pair')
w('agree; these are the moment equalities for `I`, `Z₁`, `Z₂` and `Z₁Z₂`. -/')
wrap('theorem MomentSystem.marginal {', SIG, '    ', sep=' ', tail=' : Real}')
wrap('    (h : MomentSystem ', SIG, '      ', sep=' ', tail=') :')
MARGT = []
for a in range(4):
    MARGT.append('%s = %s' % (' + '.join(QV[4 * t + a] for t in range(5)),
                              ' + '.join(RV[4 * t + a] for t in range(5))))
wrap('    ', ' ∧ '.join(MARGT), '      ', sep=' ∧ ', tail=' := by')
wrap('  obtain ', OBTAIN, '    ', sep=', ', tail=' := h')
w('  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith')
w('')

# ------------------------------------------------------------------- vectors
w('/-! ## The ten vectors of `ℂ⁴` -/')
w('')
for t in range(5):
    w('def %s (c : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![%s]'
      % (VEC[t], ', '.join('c y%d' % (4 * t + a) for a in range(4))))
for t in range(5):
    w('def %s (d : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![%s]'
      % (TVEC[t], ', '.join('d z%d' % (4 * t + a) for a in range(4))))
w('')
for t in range(5):
    for a in range(4):
        w('@[simp] theorem %s_%d (c : SS.BitString 6 -> ℂ) : %s c %d = c y%d := rfl'
          % (VEC[t], a, VEC[t], a, 4 * t + a))
for t in range(5):
    for a in range(4):
        w('@[simp] theorem %s_%d (d : SS.BitString 6 -> ℂ) : %s d %d = d z%d := rfl'
          % (TVEC[t], a, TVEC[t], a, 4 * t + a))
w('')

import io  # noqa: E402
OUT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    '..', '..', 'build_zh', 'orbit5_part1.lean'))
io.open(OUT, 'w', encoding='utf-8', newline='\n').write('\n'.join(L) + '\n')
print('part 1: %d lines -> %s' % (len(L), OUT))
