"""Kernel-only Lean certificate for orbit 25 -- the diagonal layer.

Every earlier orbit was closed with off-diagonal Knill-Laflamme conditions
alone. Orbit 25 cannot be: its phase ratios are globally consistent, but all
twenty-five cross relations carry sign +1, so no odd cycle exists. What closes it
is the DIAGONAL condition, which this file introduces.

For a Pauli X^e Z^z of weight at most two, distance three forces

    <0_L| X^e Z^z |0_L>  =  <1_L| X^e Z^z |1_L>,

that is

    sum over x in S0 with x xor e in S0 of (-1)^{z.x} conj(c_{x xor e}) c_x
  = sum over y in S1 with y xor e in S1 of (-1)^{z.y} conj(d_{y xor e}) d_y.

For orbit 25 the bottom fiber is closed under flipping qubit one, so the mask
X_1 has twelve diagonal incidences on each side, pairing up into six coherences
per fiber. Writing A for the anchor coherence conj(c_0) c_6:

  * the off-diagonal relations give c_0 c_{6+k} = c_k c_6, hence
    q_0 D_k = q_k A, and with the probabilities pinned by the quadratic closure
    (3/16 and 1/16) this makes sum_k D_k = (8/3) A;
  * the phase-ratio links express each top coherence through a bottom one with
    an overall minus sign, so sum_k E_k = -|lambda|^2 (8/3) A.

The two admissible dressings of X_1 that survive then read
`K + conj K = -(K + conj K)` and `K - conj K = -(K - conj K)` with K = sum_k D_k,
so K = 0, so A = 0 -- against |A|^2 = q_0 q_6 = 9/256.
"""
import io
import sys
from itertools import combinations

import numpy as np
import sympy as sp

sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from orbit import fiber, ind
from scan import bits, xor, dot, dressings
from cert import build
from relations import analyse, DSU

NL = chr(10)
AVEC, QQ, DELTA = [0, 1, 1, 1, 1, 1], 4, 1
E1 = '100000'

S0, S1 = fiber(AVEC, QQ, 0), fiber(AVEC, QQ, DELTA)
n0, n1 = len(S0), len(S1)
comp = lambda s: ''.join('1' if c == '0' else '0' for c in s)
hat = [S1.index(comp(x)) for x in S0]
Q, R, V, Am, bv, enames = build(S0, S1)
fields = list(enames) + ['nq%d' % k for k in range(n0)] + ['nr%d' % k for k in range(n1)]

rel = analyse(AVEC, QQ, DELTA)
rho = DSU(n0)
for i, j, k, l, sg, e in rel['links']:
    rho.union(i, k, -sg)
SGN = [rho.find(t)[1] for t in range(n0)]

# diagonal incidences of X_1
DB = [(S0.index(xor(x, E1)), i) for i, x in enumerate(S0) if xor(x, E1) in S0]
DT = [(S1.index(xor(y, E1)), j) for j, y in enumerate(S1) if xor(y, E1) in S1]
PB = sorted({tuple(sorted(p)) for p in DB})
PT = sorted({tuple(sorted(p)) for p in DT})
assert len(PB) == 6 and len(PT) == 6

# the masks this file needs: the off-diagonal ones carrying the c-relations,
# the link masks, and X_1 itself
OFF = sorted({e for i, j, k, l, sg, e in rel['direct'] + rel['derived']})
LNK = sorted({e for i, j, k, l, sg, e in rel['links']})
MASKS = sorted(set(OFF) | set(LNK) | {E1})
mid = {m: n for n, m in enumerate(MASKS)}
INC = {m: [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
       for m in MASKS}
ZS = {m: dressings(m) for m in MASKS}
zall = sorted({z for m in MASKS for z in ZS[m]})
zname = {z: ('w%d' % zall.index(z)) for z in zall}


def blit(s):
    return ' '.join('true ' if c == '1' else 'false' for c in s)


L = []
W = L.append
W('import Mathlib')
W('')
W('import SS.FullKL')
W('import SixQubit.Common')
W('')
W('/-!')
W('# Six-qubit no-go for moment orbit 25: the diagonal layer')
W('')
W('Orbit 25 of `six_qubit_sslp_v7.tex`: q = %d, angle vector' % QQ)
W('a = (%s), residues 0 and %d, closed in Section 15.' % (', '.join(map(str, AVEC)), DELTA))
W('')
W('Every earlier orbit was closed with off-diagonal Knill-Laflamme conditions')
W('alone.  This one cannot be: its phase ratios are globally consistent, but all')
W('twenty-five cross relations carry sign `+1`, so no odd cycle exists.  What')
W('closes it is the DIAGONAL condition, introduced here:')
W('')
W('    <0_L| X^e Z^z |0_L>  =  <1_L| X^e Z^z |1_L>.')
W('')
W('The bottom fiber is closed under flipping qubit one, so `X_1` has twelve')
W('diagonal incidences on each side, pairing into six coherences per fiber.  With')
W('`A` the anchor coherence `conj(c_0) c_6`, the off-diagonal relations give')
W('`q_0 D_k = q_k A`, and the probabilities are pinned to `3/16` and `1/16`, so')
W('`sum_k D_k = (8/3) A`; the phase-ratio links carry each top coherence back to a')
W('bottom one with an overall minus sign.  The two surviving dressings of `X_1`')
W('then force `A = 0`, against `normSq A = q_0 q_6 = 9/256`.')
W('')
W('Everything computational is decided by the Lean kernel; `native_decide` is')
W('not used.')
W('-/')
W('')
W('namespace SixQubit.Orbit25')
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
for m in MASKS:
    W('def ef%d : SS.BitString 6 := bs %s  -- mask %s' % (mid[m], blit(m), m))
for z in zall:
    W('def %s : SS.BitString 6 := bs %s  -- dressing %s' % (zname[z], blit(z), z))
W('')
for m in MASKS:
    nn = mid[m]
    ii = INC[m]
    if not ii:                  # a purely diagonal mask has no cross incidences
        continue
    W('theorem incidence%d :' % nn)
    W('    S1.filter (fun y => SS.bxor y ef%d ∈ S0) = {%s} := by decide'
      % (nn, ', '.join('z%d' % t for _, t in ii)))
    for i, t in ii:
        W('theorem fl%d_%d : SS.bxor z%d ef%d = y%d := by decide' % (nn, t, t, nn, i))
    for z in ZS[m]:
        for i, t in ii:
            W('theorem sg%d_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (nn, zname[z], t, zname[z], t, 'true' if dot(z, S1[t]) else 'false'))
W('')
W('/-! ## The diagonal matrix elements -/')
W('')
W('/-- `<0_L| X^e Z^z |0_L>` with the global prefactor omitted. -/')
W('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
W('      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)')
W('')
W('/-- `<1_L| X^e Z^z |1_L>`. -/')
W('def diagTop (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
W('      SixQubit.signMul (SS.bdot z y) (star (d (SS.bxor y e)) * d y)')
W('')
W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
W('')
n1m = mid[E1]
W('theorem diagB_inc :')
W('    S0.filter (fun x => SS.bxor x ef%d ∈ S0) = {%s} := by decide'
  % (n1m, ', '.join('y%d' % i for i in range(n0))))
W('theorem diagT_inc :')
W('    S1.filter (fun y => SS.bxor y ef%d ∈ S1) = {%s} := by decide'
  % (n1m, ', '.join('z%d' % j for j in range(n1))))
for i, x in enumerate(S0):
    W('theorem dfb%d : SS.bxor y%d ef%d = y%d := by decide'
      % (i, i, n1m, S0.index(xor(x, E1))))
for j, y in enumerate(S1):
    W('theorem dft%d : SS.bxor z%d ef%d = z%d := by decide'
      % (j, j, n1m, S1.index(xor(y, E1))))
for z in ['000000', E1]:
    for i, x in enumerate(S0):
        W('theorem dsb%s_%d : SS.bdot %s y%d = %s := by decide'
          % (zname[z], i, zname[z], i, 'true' if dot(z, x) else 'false'))
    for j, y in enumerate(S1):
        W('theorem dst%s_%d : SS.bdot %s z%d = %s := by decide'
          % (zname[z], j, zname[z], j, 'true' if dot(z, y) else 'false'))
W('')
io.open('Orbit25_wip.lean', 'w', encoding='utf-8').write(
    NL.join(L) + NL + 'end' + NL + NL + 'end SixQubit.Orbit25' + NL)
print('orbit 25 diagonal layer: %d lines, %d masks' % (len(L), len(MASKS)))
print('bottom coherence pairs:', PB)
print('top coherence pairs   :', PT)
print('rho signs:', SGN)
