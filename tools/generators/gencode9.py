"""Emit SixQubit/CodeOrder9.lean: the code-level wrapper for orbit 66.

Orbit 66 (`SixQubit/Order9.lean`) was the one module left without a wrapper.
Structurally it matches the other complement-indexed orbits - seven bottom
states, top fiber `S0.image SS.complement` - so this reuses the same bridge,
`SixQubit.CodeBridge`, and the same expansion pattern.

Everything is read out of `Order9.lean` itself rather than restated, so the
wrapper cannot drift from the theorem it feeds.
"""
import io
import os
import re
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
SRC = io.open(os.path.join(REPO, 'SixQubit', 'Order9.lean'), encoding='utf-8').read()
NL = chr(10)
S = r'\s+'
BITS = {'true': 1, 'false': 0}

ys = {}
pat = (r'def' + S + r'y(\d+)' + S + r':' + S + r'SS\.BitString' + S + r'6' + S +
       r':=' + S + r'bs' + S + (r'(\w+)' + S) * 5 + r'(\w+)')
for m in re.finditer(pat, SRC):
    ys[int(m.group(1))] = [BITS[m.group(i + 2)] for i in range(6)]
n = len(ys)
bot = [ys[i] for i in range(n)]
top = [[1 - b for b in v] for v in bot]
print('orbit 66: %d bottom states, top indexed by complement' % n)

# the moment rows the structure actually declares, in order
fields, cur = [], None
for ln in SRC.split(NL):
    mh = re.match(r'  (\w+)\s*:\s*(.*)$', ln)
    if mh and not ln.startswith('   '):
        cur = mh.group(1)
        fields.append(cur)
    elif ln.strip() == '' or not ln.startswith(' '):
        cur = None
moms = [f for f in fields if re.fullmatch(r'm\d+', f)]
print('moment rows declared: %s' % ' '.join(moms))

# the headline's off-diagonal hypotheses
k = SRC.find('theorem no_go_of_moments')
body = SRC[k:SRC.find(': False', k)]
off = re.findall(r'offSum' + S + r'c' + S + r'd' + S + r'(\S+?)' + S +
                 r'(\(fun _ => false\)|\S+?)' + S + r'=' + S + r'0', body)
print('off-diagonal hypotheses: %s' % off)

L = []
W = L.append
W('import Mathlib')
W('')
W('import SixQubit.CodeBridge')
W('import SixQubit.Order9')
W('')
W('/-!')
W('# Orbit 66: the no-go with no Knill--Laflamme hypothesis')
W('')
W('`SixQubit.Order9.no_go_of_moments` takes its Knill--Laflamme rows as')
W('hypotheses.  This module *derives* every one of them from the statement that')
W('`![c, d]` is a normalized two-dimensional code of distance three whose two')
W('logical states are supported on `S0` and `S1`.  The resulting `no_code` has no')
W('Knill--Laflamme hypothesis left.')
W('')
W('This was the last of the fifty-one orbits without a wrapper; it predates the')
W('current conventions, which is why it came last.')
W('')
W('Every Pauli instantiated below is checked to have weight at most two by')
W('`decide`, since `SS.HasDistance _ 3` supplies only weight `<= 2` rows.')
W('')
W('Generated mechanically by `tools/generators/gencode9.py`; no `sorry`, no')
W('`native_decide`.')
W('-/')
W('')
W('namespace SixQubit.Order9')
W('')
W('open scoped BigOperators')
W('open scoped ComplexConjugate')
W('')
W('noncomputable section')
W('')
W('/-! ## Expanding the generic sums over this orbit\'s two supports -/')
W('')
BL = ', '.join('y%d' % i for i in range(n))
TL = ', '.join('(SS.complement y%d)' % i for i in range(n))


def expand(name, lhs, terms, setexpr, setlit):
    W('theorem %s :' % name)
    W('    %s =' % lhs)
    W('      ' + ' + '.join(terms) + ' := by')
    W('  unfold ' + ('SixQubit.massOn' if 'massOn' in lhs else
                     ('SixQubit.occ2On' if 'occ2On' in lhs else 'SixQubit.occOn')))
    W('  rw [show %s' % setexpr)
    W('        = ({%s} : Finset (SS.BitString 6)) from by decide,' % setlit)
    for _ in range(len(terms) - 1):
        W('    Finset.sum_insert (by decide),')
    W('    Finset.sum_singleton]')
    if len(terms) > 2:
        W('  ring')
    W('')


expand('massB', 'SixQubit.massOn S0 c',
       ['Complex.normSq (c y%d)' % i for i in range(n)], 'S0', BL)
expand('massT', 'SixQubit.massOn S1 d',
       ['Complex.normSq (d (SS.complement y%d))' % i for i in range(n)], 'S1', TL)
for i in range(6):
    b = [k for k in range(n) if bot[k][i]]
    t = [k for k in range(n) if top[k][i]]
    expand('occB%d' % i, 'SixQubit.occOn S0 c %d' % i,
           ['Complex.normSq (c y%d)' % k for k in b] or ['0'],
           'S0.filter (fun x => x %d = true)' % i,
           ', '.join('y%d' % k for k in b))
    expand('occT%d' % i, 'SixQubit.occOn S1 d %d' % i,
           ['Complex.normSq (d (SS.complement y%d))' % k for k in t] or ['0'],
           'S1.filter (fun x => x %d = true)' % i,
           ', '.join('(SS.complement y%d)' % k for k in t))
pairs = list(combinations(range(6), 2))
for i, j in pairs:
    b = [k for k in range(n) if bot[k][i] and bot[k][j]]
    t = [k for k in range(n) if top[k][i] and top[k][j]]
    expand('occ2B%d%d' % (i, j), 'SixQubit.occ2On S0 c %d %d' % (i, j),
           ['Complex.normSq (c y%d)' % k for k in b] or ['0'],
           'S0.filter (fun x => x %d = true ∧ x %d = true)' % (i, j),
           ', '.join('y%d' % k for k in b))
    expand('occ2T%d%d' % (i, j), 'SixQubit.occ2On S1 d %d %d' % (i, j),
           ['Complex.normSq (d (SS.complement y%d))' % k for k in t] or ['0'],
           'S1.filter (fun x => x %d = true ∧ x %d = true)' % (i, j),
           ', '.join('(SS.complement y%d)' % k for k in t))

io.open(os.path.join(REPO, 'SixQubit', 'CodeOrder9_part1.lean'), 'w',
        encoding='utf-8').write(NL.join(L) + NL)
print('part 1 (expansions): %d lines' % len(L))
print()
print('moment rows to wire: %s' % ' '.join(moms))
print('bottom bit incidences per coordinate: %s'
      % {i: [k for k in range(n) if bot[k][i]] for i in range(6)})
print('top bit incidences per coordinate:    %s'
      % {i: [k for k in range(n) if top[k][i]] for i in range(6)})

# ------------------------------------------------------------------ part two
M = []
V = M.append
V("/-! ## The moment system, derived from distance three -/")
V('')
V('/-- Every row of `MomentSystem` is a consequence of the honest')
V('Knill--Laflamme conditions: the normalizations come from the unit norms, and')
V('the one- and two-bit rows are the diagonal conditions for `Z_i` and `Z_i Z_j`')
V('after the character/occupation change of basis. -/')
V('theorem moments (c d : SS.BitString 6 -> \u2102)')
V('    (hc : \u2200 x, x \u2209 S0 \u2192 c x = 0) (hd : \u2200 y, y \u2209 S1 \u2192 d y = 0)')
V('    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)')
V('    (hdist : SS.HasDistance ![c, d] 3) :')
V('    MomentSystem')
V('      ' + ' '.join('(Complex.normSq (c y%d))' % i for i in range(n)))
V('      ' + ' '.join('(Complex.normSq (d (SS.complement y%d)))' % i for i in range(n))
  + ' := by')
V('  have hB : SixQubit.massOn S0 c = 1 := SixQubit.massOn_eq_one S0 c hc hnc')
V('  have hT : SixQubit.massOn S1 d = 1 := SixQubit.massOn_eq_one S1 d hd hnd')
V('  rw [massB] at hB')
V('  rw [massT] at hT')
names = ['hB', 'hT']
for mm in moms:
    digits = mm[1:]
    if len(digits) == 1:
        i = int(digits) - 1
        V('  have hs%d :=' % i)
        V('    SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist %d' % i)
        V('  rw [occB%d, occT%d] at hs%d' % (i, i, i))
        names.append('hs%d' % i)
    else:
        i, j = int(digits[0]) - 1, int(digits[1]) - 1
        V('  have hp%d%d :=' % (i, j))
        V('    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist %d %d' % (i, j))
        V('  rw [occ2B%d%d, occ2T%d%d] at hp%d%d' % (i, j, i, j, i, j))
        names.append('hp%d%d' % (i, j))
V('  exact \u27e8' + ', '.join(names) + '\u27e9')
V('')
V("/-! ## The wrapper -/")
V('')
V('/-- The two fibers are disjoint, so the two logical states are automatically')
V('orthogonal.  This is proved, never assumed. -/')
V('theorem orthogonal (c d : SS.BitString 6 -> \u2102)')
V('    (hc : \u2200 x, x \u2209 S0 \u2192 c x = 0) (hd : \u2200 y, y \u2209 S1 \u2192 d y = 0) :')
V('    SS.innerC c d = 0 :=')
V('  SixQubit.innerC_eq_zero_of_disjoint S0 S1 c d hc hd (by decide)')
V('')
V('/-- **No such code exists.**  Not one Knill--Laflamme row is assumed: `hdist`')
V('is the genuine distance-three condition, and every row that')
V('`no_go_of_moments` needs is derived from it. -/')
V('theorem no_code (c d : SS.BitString 6 -> \u2102)')
V('    (hc : \u2200 x, x \u2209 S0 \u2192 c x = 0) (hd : \u2200 y, y \u2209 S1 \u2192 d y = 0)')
V('    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)')
V('    (hdist : SS.HasDistance ![c, d] 3) : False :=')
V('  no_go_of_moments c d')
V('    (moments c d hc hd hnc hnd hdist)')
for e, z in off:
    V('    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist')
    V('      %s %s (by decide))' % (e, z))
V('')
V('end')
V('')
V('end SixQubit.Order9')

out = os.path.join(REPO, 'SixQubit', 'CodeOrder9.lean')
io.open(out, 'w', encoding='utf-8').write(NL.join(L) + NL + NL.join(M) + NL)
os.remove(os.path.join(REPO, 'SixQubit', 'CodeOrder9_part1.lean'))
print()
print('wrote %s : %d lines' % (out, len(L) + len(M)))
