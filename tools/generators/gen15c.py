"""Orbit 25, final wiring: the missing hub link, the bottom relations, the
coherence identities, the diagonal expansions, and the contradiction.
"""
import io
import sys

import sympy as sp

sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from orbit import fiber
from scan import bits, xor, dot, dressings
from relations import analyse

NL = chr(10)
AVEC, QQ, DELTA = [0, 1, 1, 1, 1, 1], 4, 1
E1 = '100000'
S0, S1 = fiber(AVEC, QQ, 0), fiber(AVEC, QQ, DELTA)
n0, n1 = len(S0), len(S1)
comp = lambda s: ''.join('1' if c == '0' else '0' for c in s)
hat = [S1.index(comp(x)) for x in S0]
rel = analyse(AVEC, QQ, DELTA)
OFF = sorted({e for i, j, k, l, sg, e in rel['direct'] + rel['derived']})
LNK = sorted({e for i, j, k, l, sg, e in rel['links']})
MASKS = sorted(set(OFF) | set(LNK) | {E1})
mid = {m: n for n, m in enumerate(MASKS)}
INC = {m: [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
       for m in MASKS}
ZS = {m: dressings(m) for m in MASKS}
zall = sorted({z for m in MASKS for z in ZS[m]})
zname = {z: ('w%d' % zall.index(z)) for z in zall}

HUB = {}
for i, j, k, l, sg, e in rel['links']:
    if i == 0 and k != 0:
        HUB[k] = sg
    elif k == 0 and i != 0:
        HUB[i] = sg
# the 6-9 link, used to reach point 6
L69 = None
for i, j, k, l, sg, e in rel['links']:
    if {i, k} == {6, 9}:
        L69 = (i, j, k, l, sg, e)
assert L69
# the cross relations
CROSS = {}
for i, j, k, l, sg, e in rel['direct'] + rel['derived']:
    if i == 0 and k in range(1, 6) and l == 6:
        CROSS[k] = (j, sg, e)
assert set(CROSS) == set(range(1, 6))

L = []
W = L.append
W('/-! ## Reaching the sixth point -/')
W('')
i6, j6, k6, l6, s69, e69 = L69
# P(i6, hat j6) + s69 P(k6, hat l6) = 0, with j6, l6 BOTTOM indices
W('/-- Point y6 is not linked to the hub directly.  One transitivity step through')
W('y9 supplies it; the multiplier is the product at y9, nonzero because both its')
W('probabilities are positive. -/')
W('theorem hb6 (c d : SS.BitString 6 -> ℂ)')
W('    (h9 : star (c y0) * d z%d - star (c y9) * d z%d = 0)' % (hat[9], hat[0]))
W('    (h69 : star (c y%d) * d z%d %s star (c y%d) * d z%d = 0)'
  % (i6, hat[j6], '+' if s69 == 1 else '-', k6, hat[l6]))
W('    (hm : star (c y9) * d z%d ≠ 0)' % hat[9])
W('    : star (c y0) * d z%d + star (c y6) * d z%d = 0 := by' % (hat[6], hat[0]))
W('  have key : (star (c y0) * d z%d + star (c y6) * d z%d) *' % (hat[6], hat[0]))
W('      (star (c y9) * d z%d) = 0 := by' % hat[9])
W('    linear_combination (d z%d * star (c y9)) * h9' % hat[6])
W('      + (star (c y9) * d z%d) * h69' % hat[0])
W('  rcases mul_eq_zero.mp key with h | h')
W('  · exact h')
W('  · exact absurd h hm')
W('')
W('/-! ## The bottom relations -/')
W('')
for k in sorted(CROSS):
    j, sg, e = CROSS[k]
    W('/-- Cross relation %d, pushed onto the bottom fiber. -/' % k)
    W('theorem bot%d (c d : SS.BitString 6 -> ℂ)' % k)
    W('    (hx : star (c y0) * d z%d %s star (c y%d) * d z%d = 0)'
      % (hat[j], '+' if sg == 1 else '-', k, hat[6]))
    W('    (ha : star (c y0) * d z%d - star (c y%d) * d z%d = 0)' % (hat[j], j, hat[0]))
    W('    (hb : star (c y0) * d z%d + star (c y6) * d z%d = 0)' % (hat[6], hat[0]))
    W('    (hv : d z%d ≠ 0)' % hat[0])
    W('    : star (c y0) * star (c y%d) - star (c y%d) * star (c y6) = 0 := by' % (j, k))
    W('  have key : (star (c y0) * star (c y%d) - star (c y%d) * star (c y6)) *' % (j, k))
    W('      d z%d = 0 := by' % hat[0])
    W('    linear_combination (star (c y0)) * hx - (star (c y0)) * ha')
    W('      - (star (c y%d)) * hb' % k)
    W('  rcases mul_eq_zero.mp key with h | h')
    W('  · exact h')
    W('  · exact absurd h hv')
    W('')
W('/-! ## The coherence identities -/')
W('')
W('/-- From `u_0 u_w = u_x u_6` to `q_0 D = q_x A`, stated with `star z * z` so')
W('that `ring` sees the products directly. -/')
W('theorem drel (c : SS.BitString 6 -> ℂ) (x w : SS.BitString 6)')
W('    (hb : star (c y0) * star (c w) - star (c x) * star (c y6) = 0)')
W('    : (star (c y0) * c y0) * (star (c x) * c w)')
W('      = (star (c x) * c x) * (star (c y0) * c y6) := by')
W('  have hc : c y0 * c w - c x * c y6 = 0 := by')
W('    simpa using congrArg star hb')
W('  linear_combination (star (c y0) * star (c x)) * hc')
W('')
W('/-- From two hub links to `q_0 E = - r * D`. -/')
W('theorem erel (c d : SS.BitString 6 -> ℂ) (x w : SS.BitString 6)')
W('    (ya yb : SS.BitString 6)')
W('    (ha : star (c y0) * d ya - star (c x) * d z%d = 0)' % hat[0])
W('    (hb : star (c y0) * d yb + star (c w) * d z%d = 0)' % hat[0])
W('    : (star (c y0) * c y0) * (star (d ya) * d yb)')
W('      = -((star (c w) * c x) * (star (d z%d) * d z%d)) := by' % (hat[0], hat[0]))
W('  have hac : c y0 * star (d ya) - c x * star (d z%d) = 0 := by' % hat[0])
W('    simpa using congrArg star ha')
W('  linear_combination (star (c y0) * d yb) * hac')
W('    + (c x * star (d z%d)) * hb' % hat[0])
W('')
W('/-- `star z * z` is the squared modulus. -/')
W('theorem sq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by')
W('  rw [Complex.normSq_eq_conj_mul_self]; rfl')
W('')
io.open('gen15c_body.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('final wiring part 1: %d lines' % len(L))
print('L69 =', L69)
print('CROSS =', {k: CROSS[k] for k in sorted(CROSS)})
print('HUB signs =', {k: HUB[k] for k in sorted(HUB)})
print('hat[0]=%d hat[6]=%d hat[9]=%d' % (hat[0], hat[6], hat[9]))
