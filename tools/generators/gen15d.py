"""Orbit 25, the closing argument: diagonal expansions and the contradiction."""
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
ZS = {m: dressings(m) for m in MASKS}
zall = sorted({z for m in MASKS for z in ZS[m]})
zname = {z: ('w%d' % zall.index(z)) for z in zall}
nE = mid[E1]
W0, WX = zname['000000'], zname[E1]

L = []
W = L.append
W('/-! ## The diagonal expansions -/')
W('')
for z, nm in (('000000', W0), (E1, WX)):
    body = ' '.join('%s star (c y%d) * c y%d'
                    % ('-' if dot(z, S0[i]) else '+', S0.index(xor(S0[i], E1)), i)
                    for i in range(n0)).lstrip('+ ')
    W('theorem dbot_%s (c : SS.BitString 6 -> ℂ) :' % nm)
    W('    diagBot c ef%d %s = %s := by' % (nE, nm, body))
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
                    % ('-' if dot(z, S1[j]) else '+', S1.index(xor(S1[j], E1)), j)
                    for j in range(n1)).lstrip('+ ')
    W('theorem dtop_%s (d : SS.BitString 6 -> ℂ) :' % nm)
    W('    diagTop d ef%d %s = %s := by' % (nE, nm, body))
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
W('/-! ## The anchor coherence at k = 5 -/')
W('')
W('/-- The last coherence needs only the single link at y6. -/')
W('theorem erel5 (c d : SS.BitString 6 -> ℂ)')
W('    (hb : star (c y0) * d z%d + star (c y6) * d z%d = 0)' % (hat[6], hat[0]))
W('    : (star (c y0) * c y0) * (star (d z%d) * d z%d)' % (hat[6], hat[0]))
W('      = -((star (c y0) * c y6) * (star (d z%d) * d z%d)) := by' % (hat[0], hat[0]))
W('  have hbc : c y0 * star (d z%d) + c y6 * star (d z%d) = 0 := by'
  % (hat[6], hat[0]))
W('    simpa using congrArg star hb')
W('  linear_combination (star (c y0) * d z%d) * hbc' % hat[0])
W('')
io.open('gen15d_body.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('diagonal expansions + erel5: %d lines' % len(L))
print('bottom sign pattern at %s:' % E1,
      [1 if not dot(E1, S0[i]) else -1 for i in range(n0)])
print('top sign pattern    at %s:' % E1,
      [1 if not dot(E1, S1[j]) else -1 for j in range(n1)])
print('bottom pairing:', [(S0.index(xor(S0[i], E1)), i) for i in range(n0)])
print('top pairing   :', [(S1.index(xor(S1[j], E1)), j) for j in range(n1)])
