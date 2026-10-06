"""Emit SixQubit/CodeOrbit36.lean: the code-level bridge for orbit 36.

Every orbit-36 result -- `orbit36_rigidity`, `orbit36_theorem`,
`orbit36_enumerator` -- takes its moment system and its twenty-two
Knill--Laflamme rows as *hypotheses*.  The fifty-one no-go modules do not: each
`CodeOrbit<n>.no_code` derives them from the single statement that `![c, d]` is
a normalized distance-three code supported on the two fibers.  Orbit 36 was the
one module in the development still missing that bridge, so its conclusions were
statements about amplitude pairs satisfying certain moment conditions rather
than about codes in the orbit.

This closes it, by the same route `gencode9.py` used for orbit 66, whose fiber
structure is identical (top fiber the complement of the bottom).  Two
differences:

  * orbit 36 names its top states `z0..z11` rather than `complement y_i`,
    and its `MomentSystem` is indexed that way, so the expansions use those
    names -- `z_i = complement y_i` is checked here before anything is written;
  * its `MomentSystem` carries nonnegativity fields `nq0..nq11`, `nr0..nr11`
    that orbit 66's does not, supplied by `Complex.normSq_nonneg`.

Everything is read out of `Orbit36.lean` and `Orbit36Final.lean` rather than
restated, so the wrapper cannot drift from the theorems it feeds.
"""
import io
import os
import re
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
NL = chr(10)
S = r'\s+'
BITS = {'true': 1, 'false': 0}

SRC = io.open(os.path.join(REPO, 'SixQubit', 'Orbit36.lean'), encoding='utf-8').read()
FIN = io.open(os.path.join(REPO, 'SixQubit', 'Orbit36Final.lean'), encoding='utf-8').read()

# ---------------------------------------------------------------- the states
pat = (r'def' + S + r'([yz])(\d+)' + S + r':' + S + r'SS\.BitString' + S + r'6' + S +
       r':=' + S + r'bs' + S + (r'(\w+)' + S) * 5 + r'(\w+)')
st = {}
for m in re.finditer(pat, SRC):
    st[(m.group(1), int(m.group(2)))] = [BITS[m.group(i + 3)] for i in range(6)]
n = len([k for k in st if k[0] == 'y'])
assert n == len([k for k in st if k[0] == 'z']), 'unequal fibers'
bot = [st[('y', i)] for i in range(n)]
top = [st[('z', i)] for i in range(n)]
assert all(top[i] == [1 - b for b in bot[i]] for i in range(n)), \
    'z_i is not the complement of y_i'
print('orbit 36: %d + %d states, complement-paired' % (n, n))

# ------------------------------------------------------- the moment structure
fields, cur = [], None
for ln in SRC.split(NL):
    mh = re.match(r'  (\w+)\s*:\s*(.*)$', ln)
    if mh and not ln.startswith('   '):
        cur = mh.group(1)
        fields.append(cur)
    elif ln.strip() == '' or not ln.startswith(' '):
        cur = None
moms = [f for f in fields if re.fullmatch(r'm\d+', f)]
nqs = [f for f in fields if re.fullmatch(r'nq\d+', f)]
nrs = [f for f in fields if re.fullmatch(r'nr\d+', f)]
print('moment rows: %d ; nonnegativity fields: %d + %d' % (len(moms), len(nqs), len(nrs)))

# ------------------------------------------- the headline's KL row hypotheses
k = FIN.find('theorem orbit36_rigidity')
body = FIN[k:FIN.find(NL + '    : ', k)]
off = re.findall(r'offSum' + S + r'c' + S + r'd' + S + r'(\S+?)' + S + r'(\S+?)' + S +
                 r'=' + S + r'0', body)
print('KL rows in the headline: %d' % len(off))
assert len(off) == 22, 'expected 22 rows, found %d' % len(off)

# ------------------------------------------------------------------ emission
L = []
W = L.append
W('import Mathlib')
W('')
W('import SixQubit.CodeBridge')
W('import SixQubit.Orbit36')
W('import SixQubit.Orbit36Final')
W('')
W('/-!')
W('# Orbit 36 at the level of codes')
W('')
W('`Orbit36Final.orbit36_rigidity` and its companions take the moment system and')
W('twenty-two Knill--Laflamme rows as hypotheses.  This module *derives* every one')
W('of them from the statement that `![c, d]` is a normalized two-dimensional code')
W('of distance three supported on the two fibers of orbit 36, which is what the')
W('fifty-one no-go wrappers already did for their orbits.')
W('')
W('The difference matters for what the rigidity theorem is about.  Before this,')
W('it spoke of amplitude pairs satisfying certain moment conditions; after it, of')
W('every exact code in the orbit.')
W('')
W('Every Pauli instantiated below is checked to have weight at most two by')
W('`decide`, since `SS.HasDistance _ 3` supplies only weight `<= 2` rows.')
W('')
W('Generated mechanically by `tools/generators/gencode36.py`; no `sorry`, no')
W('`native_decide`.')
W('-/')
W('')
W('namespace SixQubit.Orbit36')
W('')
W('open scoped BigOperators')
W('open scoped ComplexConjugate')
W('-- the lifted conclusion names `AEnum` unqualified, as `Orbit36Final` does')
W('open SixQubit.Orbit36Phase (AEnum)')
W('')
W('noncomputable section')
W('')
W("/-! ## Expanding the generic sums over this orbit's two supports -/")
W('')
BL = ', '.join('y%d' % i for i in range(n))
TL = ', '.join('z%d' % i for i in range(n))


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
       ['Complex.normSq (d z%d)' % i for i in range(n)], 'S1', TL)
for i in range(6):
    b = [k for k in range(n) if bot[k][i]]
    t = [k for k in range(n) if top[k][i]]
    expand('occB%d' % i, 'SixQubit.occOn S0 c %d' % i,
           ['Complex.normSq (c y%d)' % k for k in b] or ['0'],
           'S0.filter (fun x => x %d = true)' % i,
           ', '.join('y%d' % k for k in b))
    expand('occT%d' % i, 'SixQubit.occOn S1 d %d' % i,
           ['Complex.normSq (d z%d)' % k for k in t] or ['0'],
           'S1.filter (fun x => x %d = true)' % i,
           ', '.join('z%d' % k for k in t))
for i, j in combinations(range(6), 2):
    b = [k for k in range(n) if bot[k][i] and bot[k][j]]
    t = [k for k in range(n) if top[k][i] and top[k][j]]
    expand('occ2B%d%d' % (i, j), 'SixQubit.occ2On S0 c %d %d' % (i, j),
           ['Complex.normSq (c y%d)' % k for k in b] or ['0'],
           'S0.filter (fun x => x %d = true ∧ x %d = true)' % (i, j),
           ', '.join('y%d' % k for k in b))
    expand('occ2T%d%d' % (i, j), 'SixQubit.occ2On S1 d %d %d' % (i, j),
           ['Complex.normSq (d z%d)' % k for k in t] or ['0'],
           'S1.filter (fun x => x %d = true ∧ x %d = true)' % (i, j),
           ', '.join('z%d' % k for k in t))

# --------------------------------------------------------------- the moments
M = []
V = M.append
V('/-! ## The moment system, derived from distance three -/')
V('')
V('/-- Every row of `MomentSystem` is a consequence of the honest')
V('Knill--Laflamme conditions: the normalizations come from the unit norms, the')
V('one- and two-bit rows are the diagonal conditions for `Z_i` and `Z_i Z_j`')
V('after the occupation change of basis, and the nonnegativity rows hold because')
V('every entry is a squared modulus. -/')
V('theorem moments (c d : SS.BitString 6 → ℂ)')
V('    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)')
V('    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)')
V('    (hdist : SS.HasDistance ![c, d] 3) :')
V('    MomentSystem')
V('      ' + ' '.join('(Complex.normSq (c y%d))' % i for i in range(n)))
V('      ' + ' '.join('(Complex.normSq (d z%d))' % i for i in range(n)) + ' := by')
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
        V('    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist %d %d'
          % (i, j))
        V('  rw [occ2B%d%d, occ2T%d%d] at hp%d%d' % (i, j, i, j, i, j))
        names.append('hp%d%d' % (i, j))
names += ['(Complex.normSq_nonneg _)'] * (len(nqs) + len(nrs))
V('  exact ⟨' + ', '.join(names) + '⟩')
V('')
V('/-! ## The bridge -/')
V('')
V('/-- The twenty-two Knill--Laflamme rows the rigidity theorem needs, each')
V('derived from `hdist` rather than assumed. -/')
V('theorem klRows (c d : SS.BitString 6 → ℂ)')
V('    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)')
V('    (hdist : SS.HasDistance ![c, d] 3) :')
for idx, (e, z) in enumerate(off):
    V('    %s offSum c d %s %s = 0' % ('    ' if idx else '', e, z)
      + (' ∧' if idx < len(off) - 1 else ' :='))
V('  ⟨' + ', '.join(
    'SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist %s %s (by decide)'
    % (e, z) for e, z in off) + '⟩')
V('')

# ------------------------------------------- the wrapper, at the level of codes
# The conclusion is lifted verbatim out of `orbit36_rigidity` rather than
# restated, so the wrapper cannot claim more or less than the theorem it feeds.
kc = FIN.find('theorem orbit36_rigidity')
c0 = FIN.find(NL + '    : ', kc)
c1 = FIN.find(':= by', c0)
assert c0 > 0 and c1 > c0, 'cannot locate the conclusion of orbit36_rigidity'
conclusion = FIN[c0 + len(NL) + 6:c1].rstrip()
print('conclusion lifted: %d characters' % len(conclusion))

V('/-- **Orbit 36 is rigid, at the level of codes.**')
V('')
V('Not one moment row and not one Knill--Laflamme row is assumed.  `hdist` is the')
V('genuine distance-three condition, and everything')
V('`Orbit36Final.orbit36_rigidity` needs is derived from it above.  So this says')
V('what the manuscript says: every exact code in orbit 36 has the stated')
V('magnitudes, is local-monomial equivalent to the canonical pair, and has the')
V('stated weight enumerator. -/')
V('theorem rigid_code (c d : SS.BitString 6 → ℂ)')
V('    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)')
V('    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)')
V('    (hdist : SS.HasDistance ![c, d] 3) :')
V('    ' + conclusion + ' := by')
V('  obtain ⟨' + ', '.join('r%d' % i for i in range(len(off))) + '⟩ :=')
V('    klRows c d hc hd hdist')
V('  exact Orbit36Final.orbit36_rigidity c d hc hd')
V('    (moments c d hc hd hnc hnd hdist)')
V('    ' + ' '.join('r%d' % i for i in range(len(off))))
V('')
V('end')
V('')
V('end SixQubit.Orbit36')

out = os.path.join(REPO, 'SixQubit', 'CodeOrbit36.lean')
body_txt = NL.join(L) + NL + NL.join(M) + NL
if '--check' not in sys.argv:
    fh = io.open(out, 'w', encoding='utf-8', newline=NL)
    fh.write(body_txt)
    fh.close()
    print('wrote %s : %d lines' % (out, body_txt.count(NL)))
else:
    print('check only; would write %d lines' % body_txt.count(NL))
