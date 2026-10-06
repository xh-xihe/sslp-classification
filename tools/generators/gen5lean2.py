"""Part two of `SixQubit/Orbit5.lean`: the two-flip relations and the frame
reduction that feeds `SixQubit.Trace5.cs_tight`.
"""
import io
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import gen5lean as G                                    # noqa: E402
from gen5orbit import two_flip, off_row                 # noqa: E402

VEC, TVEC, AWNAME, AWBITS, PAIR, W0 = G.VEC, G.TVEC, G.AWNAME, G.AWBITS, G.PAIR, G.W0

L2 = []
w2 = L2.append


def wrap2(prefix, body, cont, sep=' + ', tail=''):
    parts = body.split(sep)
    line = prefix + parts[0]
    for p in parts[1:]:
        piece = sep.strip() + ' ' + p
        if len(line) + len(piece) + 1 > 104:
            w2(line)
            line = cont + piece
        else:
            line = line + ' ' + piece
    w2(line + tail)


def comps(vname):
    return ', '.join('%s_%d' % (vname, a) for a in range(4))


# ------------------------------------------------------------ two-flip rows
w2('/-! ## The two-flip relations -/')
w2('')
for (k, l) in PAIR:
    mn = 'g%d%d' % (k + 1, l + 1)
    inc = off_row(two_flip(k, l), W0)
    pairs = []
    for (s, b, t) in inc:
        bt, tt = b // 4, t // 4
        if (bt, tt) not in pairs:
            pairs.append((bt, tt))
    assert len(pairs) == 2, pairs
    (bt1, tt1), (bt2, tt2) = pairs
    nm = 'two_flip_%d%d' % (min(bt1, bt2), max(bt1, bt2))
    w2('/-- The weight-two flip `%s` isolates the reciprocal pair' % mn)
    w2('`a%d† b%d + a%d† b%d`. -/' % (bt1, tt1 + 1, bt2, tt2 + 1))
    w2('theorem %s (c d : SS.BitString 6 -> ℂ) (h : offSum c d %s w0 = 0) :' % (nm, mn))
    w2('    Trace5.ip (%s c) (%s d) + Trace5.ip (%s c) (%s d) = 0 := by'
       % (VEC[bt1], TVEC[tt1], VEC[bt2], TVEC[tt2]))
    w2('  rw [ex_%s_w0] at h' % mn)
    w2('  simp only [Trace5.ip, %s, %s, %s, %s]'
       % (comps(VEC[bt1]), comps(TVEC[tt1]), comps(VEC[bt2]), comps(TVEC[tt2])))
    w2('  linear_combination h')
w2('')

# --------------------------------------------------------- frame reduction
w2('/-! ## The frame reduction -/')
w2('')
w2('/-- **Orbit 5: the frame reduction.**  From the moment polytope, the eight')
w2('one-flip rows that separate the two anchors, and the twelve diagonal rows on')
w2('the free pair, the anchor `u` is orthogonal to all four bottom vectors and the')
w2('two frame operators coincide. -/')
w2('theorem frame_reduction (c d : SS.BitString 6 -> ℂ)')
qs = ' '.join('(Complex.normSq (c y%d))' % i for i in range(20))
rs = ' '.join('(Complex.normSq (d z%d))' % i for i in range(20))
wrap2('    (hm : MomentSystem ', qs + ' ' + rs, '      ', sep=' ', tail=')')
for i in range(4):
    j = (i + 1) % 4
    w2('    (ho%da : offSum c d f%d w0 = 0)' % (i + 1, i + 1))
    w2('    (ho%db : offSum c d f%d f%d = 0)' % (i + 1, i + 1, j + 1))
for pi, pn in enumerate(['p1', 'p2', 'p3']):
    for wi, wn in enumerate(AWNAME):
        w2('    (hd%d%d : diagBot c %s %s = diagTop d %s %s)'
           % (pi + 1, wi + 1, pn, wn, pn, wn))
w2('    : Trace5.ip (uu c) (aa1 c) = 0 ∧ Trace5.ip (uu c) (aa2 c) = 0 ∧')
w2('      Trace5.ip (uu c) (aa3 c) = 0 ∧ Trace5.ip (uu c) (aa4 c) = 0 ∧')
w2('      Trace5.ip (aa1 c) (vv d) = 0 ∧ Trace5.ip (aa2 c) (vv d) = 0 ∧')
w2('      Trace5.ip (aa3 c) (vv d) = 0 ∧ Trace5.ip (aa4 c) (vv d) = 0 ∧')
w2('      Trace5.ip (uu c) (bb1 d) = 0 ∧ Trace5.ip (uu c) (bb2 d) = 0 ∧')
w2('      Trace5.ip (uu c) (bb3 d) = 0 ∧ Trace5.ip (uu c) (bb4 d) = 0 ∧')
w2('      ∀ k l : Fin 4, Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) k l')
w2('        = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) k l := by')
w2('  obtain ⟨nu, na1, na2, na3, na4, nb1, nb2, nb3, nb4, nv⟩ := hm.norms')
w2('  obtain ⟨mg0, mg1, mg2, mg3⟩ := hm.marginal')
for t in range(5):
    w2('  have hn%s : Trace5.nsq (%s c) = %s := by'
       % (VEC[t], VEC[t], '1/3' if t == 0 else '1/6'))
    w2('    simp only [Trace5.nsq, %s]' % comps(VEC[t]))
    w2('    linarith')
for t in range(5):
    w2('  have hn%s : Trace5.nsq (%s d) = %s := by'
       % (TVEC[t], TVEC[t], '1/3' if t == 4 else '1/6'))
    w2('    simp only [Trace5.nsq, %s]' % comps(TVEC[t]))
    w2('    linarith')
for i in range(4):
    j = (i + 1) % 4
    w2('  rw [ex_f%d_w0] at ho%da' % (i + 1, i + 1))
    w2('  rw [ex_f%d_f%d] at ho%db' % (i + 1, j + 1, i + 1))
for i in range(4):
    w2('  have hq%d : Trace5.ip (uu c) (%s d) = 0 := by' % (i + 1, TVEC[i]))
    w2('    simp only [Trace5.ip, %s, %s]' % (comps('uu'), comps(TVEC[i])))
    w2('    linear_combination (1/2 : ℂ) * ho%da + (1/2 : ℂ) * ho%db' % (i + 1, i + 1))
for i in range(4):
    w2('  have hav%d : Trace5.ip (%s c) (vv d) = 0 := by' % (i + 1, VEC[i + 1]))
    w2('    simp only [Trace5.ip, %s, %s]' % (comps(VEC[i + 1]), comps('vv')))
    w2('    linear_combination (1/2 : ℂ) * ho%da - (1/2 : ℂ) * ho%db' % (i + 1, i + 1))
for pi, pn in enumerate(['p1', 'p2', 'p3']):
    for wi, wn in enumerate(AWNAME):
        w2('  rw [dexB_%s_%s, dexT_%s_%s] at hd%d%d' % (pn, wn, pn, wn, pi + 1, wi + 1))
CNAMES = []
for k in range(4):
    for l in range(4):
        nm = 'fk%d%d' % (k, l)
        CNAMES.append(nm)
        w2('  have %s : uu c %d * star (uu c %d)' % (nm, k, l))
        w2('      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) %d %d' % (k, l))
        w2('      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) %d %d' % (k, l))
        w2('        + vv d %d * star (vv d %d) := by' % (k, l))
        cs = ', '.join(['uu_%d' % k, 'uu_%d' % l]
                       + ['aa%d_%d' % (t, k) for t in range(1, 5)]
                       + ['aa%d_%d' % (t, l) for t in range(1, 5)])
        ds = ', '.join(['vv_%d' % k, 'vv_%d' % l]
                       + ['bb%d_%d' % (t, k) for t in range(1, 5)]
                       + ['bb%d_%d' % (t, l) for t in range(1, 5)])
        w2('    simp only [Trace5.fr, %s, %s]' % (cs, ds))
        if k == l:
            bl = ' + '.join('Complex.normSq (c y%d)' % (4 * t + k) for t in range(5))
            tl = ' + '.join('Complex.normSq (d z%d)' % (4 * t + k) for t in range(5))
            wrap2('    have hc : ((', bl, '        ')
            wrap2('        : Real) : ℂ) = ((', tl, '        ', tail=' : Real) : ℂ) := by')
            w2('      exact_mod_cast mg%d' % k)
            w2('    push_cast [← SixQubit.star_mul_self] at hc')
            w2('    linear_combination hc')
        else:
            pi = {2: 0, 1: 1, 3: 2}[k ^ l]
            terms = []
            for wi in range(4):
                sg = -1 if bin(AWBITS[wi] & k).count('1') % 2 else 1
                terms.append('(%s1/4 : ℂ) * hd%d%d'
                             % ('-' if sg < 0 else '', pi + 1, wi + 1))
            wrap2('    linear_combination ', ' + '.join(terms), '      ')
w2('  have hf : ∀ k l : Fin 4, uu c k * star (uu c l)')
w2('      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) k l')
w2('      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) k l + vv d k * star (vv d l) := by')
w2('    intro k l')
w2('    fin_cases k <;> fin_cases l')
wrap2('    exacts [', ', '.join(CNAMES), '      ', sep=', ', tail=']')
w2('  obtain ⟨t1, t2, t3, t4, tf⟩ := Trace5.cs_tight (uu c) (vv d) (aa1 c) (aa2 c) (aa3 c)')
w2('    (aa4 c) (bb1 d) (bb2 d) (bb3 d) (bb4 d) hnuu hnvv hq1 hq2 hq3 hq4 hf')
w2('  exact ⟨t1, t2, t3, t4, hav1, hav2, hav3, hav4, hq1, hq2, hq3, hq4, tf⟩')

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
OUT2 = os.path.join(ROOT, 'build_zh', 'orbit5_part2.lean')
io.open(OUT2, 'w', encoding='utf-8', newline='\n').write('\n'.join(L2) + '\n')

part1 = io.open(os.path.join(ROOT, 'build_zh', 'orbit5_part1.lean'), encoding='utf-8').read()
full = part1.rstrip('\n') + '\n\n' + '\n'.join(L2) + '\n\nend\n\nend SixQubit.Orbit5\n'
OUT = os.path.join(ROOT, 'SixQubit', 'Orbit5.lean')
io.open(OUT, 'w', encoding='utf-8', newline='\n').write(full)
print('part 2: %d lines; Orbit5.lean: %d lines' % (len(L2), full.count('\n')))
