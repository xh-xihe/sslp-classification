"""Part three of `SixQubit/Orbit5.lean`: the dressed weight-two flip rows that
carry the two-qubit flip-kernel dichotomy, and the headline no-go.

Emits the extra off-diagonal layer (the rows `Z_A X_i`, `X_A X_i`, `Y_A X_i` for
`A` either zero-angle qubit) and the theorem `no_go_of_moments`, whose only
hypotheses are `offSum ... = 0`, `diagBot ... = diagTop ...` and `MomentSystem`.
Then reassembles the whole module.
"""
import io
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'core')))

import gen5lean as G                                             # noqa: E402
import gen5lean2                                                 # noqa: E402
from gen5orbit import EFLIP, off_row, diag_row                    # noqa: E402
from scan import xor                                             # noqa: E402

W0 = '000000'
P1 = '100000'
P2 = '010000'
AWNAME = G.AWNAME
AWBITS = G.AWBITS
VEC, TVEC = G.VEC, G.TVEC

LB = []
wb = LB.append
L3 = []
w3 = L3.append


def wrap(out, prefix, body, cont, sep=' + ', tail=''):
    parts = body.split(sep)
    line = prefix + parts[0]
    for p in parts[1:]:
        piece = sep.strip() + ' ' + p
        if len(line) + len(piece) + 1 > 104:
            out.append(line)
            line = cont + piece
        else:
            line = line + ' ' + piece
    out.append(line + tail)


def comps(v):
    return ', '.join('%s_%d' % (v, a) for a in range(4))


# =========================================================== the dressed rows
NEWMASK = [('k%d' % (i + 1), xor(e, P1)) for i, e in enumerate(EFLIP)]
NEWMASK += [('l%d' % (i + 1), xor(e, P2)) for i, e in enumerate(EFLIP)]

NEWROWS = []
for i, e in enumerate(EFLIP):
    NEWROWS.append(('f%d' % (i + 1), e, 'p1', P1))
    NEWROWS.append(('f%d' % (i + 1), e, 'p2', P2))
    NEWROWS.append(('k%d' % (i + 1), xor(e, P1), 'w0', W0))
    NEWROWS.append(('k%d' % (i + 1), xor(e, P1), 'p1', P1))
    NEWROWS.append(('l%d' % (i + 1), xor(e, P2), 'w0', W0))
    NEWROWS.append(('l%d' % (i + 1), xor(e, P2), 'p2', P2))

wb('/-! ## The dressed one-flip layer')
wb('')
wb('For a single zero-angle qubit `A` and an active coordinate `i` the errors')
wb('`Z_A X_i`, `X_A X_i` and `Y_A X_i` all have weight two, so their off-diagonal')
wb('rows are available.  Together with the undressed row they carry all four')
wb('entries of each of the two one-qubit partial traces of `|u><b_i| + |a_i><u|`.')
wb('-/')
wb('')
for nm, s in NEWMASK:
    wb(G.bsdef(nm, s))
wb('')
for (mn, e) in NEWMASK:
    inc = off_row(e, W0)
    tops = [t for (_, _, t) in inc]
    wb('theorem inc_%s :' % mn)
    wb('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
       % (mn, ', '.join('z%d' % t for t in tops)))
    for (s, b, t) in inc:
        wb('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide' % (mn, t, t, mn, b))
wb('')
for (mn, e, dn, dz) in NEWROWS:
    inc = off_row(e, dz)
    tops = [t for (_, _, t) in inc]
    for (s, b, t) in inc:
        wb('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
           % (mn, dn, t, dn, t, G.sgn_lit(s < 0)))
    wb('theorem ex_%s_%s (c d : SS.BitString 6 -> ℂ) :' % (mn, dn))
    body = G.signed([(s, 'star (c y%d) * d z%d' % (b, t)) for (s, b, t) in inc])
    wrap(LB, '    offSum c d %s %s = ' % (mn, dn), body, '      ', sep=' + ', tail=' := by')
    wb('  unfold offSum')
    wb('  rw [inc_%s]' % mn)
    wb('  ' + G.peel(len(inc)))
    wb('  rw [' + ', '.join('flip_%s_%d' % (mn, t) for t in tops) + ']')
    wb('  simp only [' + ', '.join(['sg_%s_%s_%d' % (mn, dn, t) for t in tops]
       + G.signmul_args([s for (s, _, _) in inc])) + ']')
    wb('  try ring')
wb('')

# ================================================================ the endgame
ROWNAME = {}
for i in range(1, 5):
    ROWNAME[(i, 0)] = 'ho%da' % i
    ROWNAME[(i, 1)] = 'hz%d1' % i
    ROWNAME[(i, 2)] = 'hz%d2' % i
    ROWNAME[(i, 3)] = 'hk%d0' % i
    ROWNAME[(i, 4)] = 'hk%d1' % i
    ROWNAME[(i, 5)] = 'hl%d0' % i
    ROWNAME[(i, 6)] = 'hl%d2' % i
ROWEX = {0: ('f%d', 'w0'), 1: ('f%d', 'p1'), 2: ('f%d', 'p2'), 3: ('k%d', 'w0'),
         4: ('k%d', 'p1'), 5: ('l%d', 'w0'), 6: ('l%d', 'p2')}
PAIR = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]


def entryM(i, r, rp):
    return (' + '.join(
        ['star (uu c %d) * bb%d d %d' % (2 * rp + s, i, 2 * r + s) for s in range(2)]
        + ['star (aa%d c %d) * vv d %d' % (i, 2 * rp + s, 2 * r + s) for s in range(2)]))


def entryN(i, s, spp):
    return (' + '.join(
        ['star (uu c %d) * bb%d d %d' % (2 * r + spp, i, 2 * r + s) for r in range(2)]
        + ['star (aa%d c %d) * vv d %d' % (i, 2 * r + spp, 2 * r + s) for r in range(2)]))


MCOMB = {(0, 0): (0, 1, 1), (1, 1): (0, 1, -1), (0, 1): (3, 4, 1), (1, 0): (3, 4, -1)}
NCOMB = {(0, 0): (0, 2, 1), (1, 1): (0, 2, -1), (0, 1): (5, 6, 1), (1, 0): (5, 6, -1)}

w3('/-! ## The headline no-go -/')
w3('')
w3('/-- **Orbit 5 admits no exact completion.**  The hypotheses are exactly the')
w3('moment polytope, twenty-eight off-diagonal Knill--Laflamme rows of weight at')
w3('most two, and the twelve diagonal rows supported on the free pair.  No')
w3('algebraic normalisation is assumed: the Schmidt gauge of the paper is replaced')
w3('by the scalar invariant `Flip5.dsc` and the anchor rephasing is discharged by')
w3('`Flip5.anchor_scale`. -/')
w3('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
qs = ' '.join('(Complex.normSq (c y%d))' % i for i in range(20))
rs = ' '.join('(Complex.normSq (d z%d))' % i for i in range(20))
wrap(L3, '    (hm : MomentSystem ', qs + ' ' + rs, '      ', sep=' ', tail=')')
for i in range(4):
    j = (i + 1) % 4
    w3('    (ho%da : offSum c d f%d w0 = 0)' % (i + 1, i + 1))
    w3('    (ho%db : offSum c d f%d f%d = 0)' % (i + 1, i + 1, j + 1))
for i in range(1, 5):
    w3('    (hz%d1 : offSum c d f%d p1 = 0)' % (i, i))
    w3('    (hz%d2 : offSum c d f%d p2 = 0)' % (i, i))
    w3('    (hk%d0 : offSum c d k%d w0 = 0)' % (i, i))
    w3('    (hk%d1 : offSum c d k%d p1 = 0)' % (i, i))
    w3('    (hl%d0 : offSum c d l%d w0 = 0)' % (i, i))
    w3('    (hl%d2 : offSum c d l%d p2 = 0)' % (i, i))
for (i, j) in PAIR:
    w3('    (ht%d%d : offSum c d g%d%d w0 = 0)' % (i, j, i, j))
for pi, pn in enumerate(['p1', 'p2', 'p3']):
    for wi, wn in enumerate(AWNAME):
        w3('    (hd%d%d : diagBot c %s %s = diagTop d %s %s)'
           % (pi + 1, wi + 1, pn, wn, pn, wn))
w3('    : False := by')
w3('  obtain ⟨nu, na1, na2, na3, na4, nb1, nb2, nb3, nb4, nv⟩ := hm.norms')
w3('  obtain ⟨mg0, mg1, mg2, mg3⟩ := hm.marginal')
for t in range(5):
    w3('  have hn%s : Trace5.nsq (%s c) = %s := by'
       % (VEC[t], VEC[t], '1/3' if t == 0 else '1/6'))
    w3('    simp only [Trace5.nsq, %s]' % comps(VEC[t]))
    w3('    linarith')
for t in range(5):
    w3('  have hn%s : Trace5.nsq (%s d) = %s := by'
       % (TVEC[t], TVEC[t], '1/3' if t == 4 else '1/6'))
    w3('    simp only [Trace5.nsq, %s]' % comps(TVEC[t]))
    w3('    linarith')
for (i, j) in PAIR:
    w3('  have x%d%d : Trace5.ip (aa%d c) (bb%d d) + Trace5.ip (aa%d c) (bb%d d) = 0 := by'
       % (i, j, i, j, j, i))
    w3('    linear_combination two_flip_%d%d c d ht%d%d' % (i, j, i, j))
for i in range(4):
    j = (i + 1) % 4
    w3('  rw [ex_f%d_f%d] at ho%db' % (i + 1, j + 1, i + 1))
for i in range(1, 5):
    for r in range(7):
        pat, dn = ROWEX[r]
        w3('  rw [ex_%s_%s] at %s' % (pat % i, dn, ROWNAME[(i, r)]))
for i in range(4):
    w3('  have hq%d : Trace5.ip (uu c) (%s d) = 0 := by' % (i + 1, TVEC[i]))
    w3('    simp only [Trace5.ip, %s, %s]' % (comps('uu'), comps(TVEC[i])))
    w3('    linear_combination (1/2 : ℂ) * ho%da + (1/2 : ℂ) * ho%db' % (i + 1, i + 1))
for pi, pn in enumerate(['p1', 'p2', 'p3']):
    for wi, wn in enumerate(AWNAME):
        w3('  rw [dexB_%s_%s, dexT_%s_%s] at hd%d%d' % (pn, wn, pn, wn, pi + 1, wi + 1))
CN = []
for k in range(4):
    for l in range(4):
        nm = 'fk%d%d' % (k, l)
        CN.append(nm)
        w3('  have %s : uu c %d * star (uu c %d)' % (nm, k, l))
        w3('      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) %d %d' % (k, l))
        w3('      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) %d %d' % (k, l))
        w3('        + vv d %d * star (vv d %d) := by' % (k, l))
        cs = ', '.join(['uu_%d' % k, 'uu_%d' % l]
                       + ['aa%d_%d' % (t, k) for t in range(1, 5)]
                       + ['aa%d_%d' % (t, l) for t in range(1, 5)])
        ds = ', '.join(['vv_%d' % k, 'vv_%d' % l]
                       + ['bb%d_%d' % (t, k) for t in range(1, 5)]
                       + ['bb%d_%d' % (t, l) for t in range(1, 5)])
        w3('    simp only [Trace5.fr, %s, %s]' % (cs, ds))
        if k == l:
            bl = ' + '.join('Complex.normSq (c y%d)' % (4 * t + k) for t in range(5))
            tl = ' + '.join('Complex.normSq (d z%d)' % (4 * t + k) for t in range(5))
            wrap(L3, '    have hc : ((', bl, '        ')
            wrap(L3, '        : Real) : ℂ) = ((', tl, '        ', tail=' : Real) : ℂ) := by')
            w3('      exact_mod_cast mg%d' % k)
            w3('    push_cast [← SixQubit.star_mul_self] at hc')
            w3('    linear_combination hc')
        else:
            pi = {2: 0, 1: 1, 3: 2}[k ^ l]
            terms = []
            for wi in range(4):
                sg = -1 if bin(AWBITS[wi] & k).count('1') % 2 else 1
                terms.append('(%s1/4 : ℂ) * hd%d%d'
                             % ('-' if sg < 0 else '', pi + 1, wi + 1))
            wrap(L3, '    linear_combination ', ' + '.join(terms), '      ')
w3('  have hf : ∀ k l : Fin 4, uu c k * star (uu c l)')
w3('      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) k l')
w3('      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) k l + vv d k * star (vv d l) := by')
w3('    intro k l')
w3('    fin_cases k <;> fin_cases l')
wrap(L3, '    exacts [', ', '.join(CN), '      ', sep=', ', tail=']')
def simpset(i, uidx, bidx):
    lst = ['uu_%d' % k for k in uidx] + ['aa%d_%d' % (i, k) for k in uidx]
    lst += ['bb%d_%d' % (i, k) for k in bidx] + ['vv_%d' % k for k in bidx]
    return ', '.join(lst)


for i in range(1, 5):
    for r in range(2):
        for rp in range(2):
            r0, r1, sg = MCOMB[(r, rp)]
            wrap(L3, '  have m%d%d%d : ' % (i, r, rp), entryM(i, r, rp), '      ',
                 tail=' = 0 := by')
            w3('    simp only [%s]'
               % simpset(i, [2 * rp + 0, 2 * rp + 1], [2 * r + 0, 2 * r + 1]))
            w3('    linear_combination (1/2 : ℂ) * %s %s (1/2 : ℂ) * %s'
               % (ROWNAME[(i, r0)], '+' if sg > 0 else '-', ROWNAME[(i, r1)]))
    for s in range(2):
        for spp in range(2):
            r0, r1, sg = NCOMB[(s, spp)]
            wrap(L3, '  have n%d%d%d : ' % (i, s, spp), entryN(i, s, spp), '      ',
                 tail=' = 0 := by')
            w3('    simp only [%s]' % simpset(i, [spp, 2 + spp], [s, 2 + s]))
            w3('    linear_combination (1/2 : ℂ) * %s %s (1/2 : ℂ) * %s'
               % (ROWNAME[(i, r0)], '+' if sg > 0 else '-', ROWNAME[(i, r1)]))
w3('  exact Flip5.core (uu c) (vv d) (aa1 c) (aa2 c) (aa3 c) (aa4 c) (bb1 d) (bb2 d) (bb3 d)')
w3('    (bb4 d) hnuu hnvv hnaa1 hnaa2 hnaa3 hnaa4 hnbb1 hnbb2 hnbb3 hnbb4 hq1 hq2 hq3 hq4 hf')
w3('    ' + ' '.join('x%d%d' % (i, j) for (i, j) in PAIR))
for i in range(1, 5):
    w3('    m%d00 m%d01 m%d10 m%d11 n%d00 n%d01 n%d10 n%d11'
       % (i, i, i, i, i, i, i, i))

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
io.open(os.path.join(ROOT, 'build_zh', 'orbit5_part1b.lean'), 'w', encoding='utf-8',
        newline='\n').write('\n'.join(LB) + '\n')
io.open(os.path.join(ROOT, 'build_zh', 'orbit5_part3.lean'), 'w', encoding='utf-8',
        newline='\n').write('\n'.join(L3) + '\n')

parts = []
for nm in ['orbit5_part1.lean', 'orbit5_part1b.lean', 'orbit5_part2.lean', 'orbit5_part3.lean']:
    parts.append(io.open(os.path.join(ROOT, 'build_zh', nm), encoding='utf-8').read().rstrip('\n'))
full = '\n\n'.join(parts) + '\n\nend\n\nend SixQubit.Orbit5\n'
io.open(os.path.join(ROOT, 'SixQubit', 'Orbit5.lean'), 'w', encoding='utf-8',
        newline='\n').write(full)
print('part 1b: %d lines; part 3: %d lines; Orbit5.lean: %d lines'
      % (len(LB), len(L3), full.count('\n')))
