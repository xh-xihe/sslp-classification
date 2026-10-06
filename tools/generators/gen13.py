"""Orbit 13: a free qubit, complete block orthogonality, and equal block frames.

Blocks are 2x2 complete bipartite pieces of the incidence structure on which
every C^2 inner product <c_x , d_y> is isolable.  For each block the moment
system supplies the two diagonal frame entries and the X_1 / Y_1 diagonal
conditions supply the off-diagonal one; `SixQubit.Frame.block_zero` then kills
the block.
"""
import io
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
sys.path.insert(0, '.')
from orbit import fiber

NL = chr(10)
BOOL = {'0': 'false', '1': 'true '}
bits = lambda s: [int(c) for c in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]
bsline = lambda nm, s: 'def %s : SS.BitString 6 := bs %s  -- %s' % (
    nm, ' '.join(BOOL[c] for c in s), s)
J = 0                                   # free qubit index
E1 = '100000'


def build(q, a, d):
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    n0, n1 = len(S0), len(S1)
    tail = lambda s: s[:J] + s[J + 1:]
    # bottom / top index by (free bit, tail)
    bidx = {(x[J], tail(x)): r for r, x in enumerate(S0)}
    tidx = {(y[J], tail(y)): r for r, y in enumerate(S1)}
    btails = sorted({tail(x) for x in S0})
    ttails = sorted({tail(y) for y in S1})

    # isolable C^2 inner products
    iso = {}
    for e in ALL:
        if not 1 <= len(supp(e)) <= 2 or e[J] == '1':
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        if not inc:
            continue
        Z = dress(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        grp = {}
        for k, (i2, t2) in enumerate(inc):
            grp.setdefault((tail(S0[i2]), tail(S1[t2])), []).append(k)
        for key, ks in grp.items():
            if len(ks) != 2:
                continue
            tgt = sp.Matrix([1 if r in ks else 0 for r in range(len(inc))])
            try:
                mu = W.T.gauss_jordan_solve(tgt)[0]
            except ValueError:
                continue
            mu = mu.subs({s: 0 for s in mu.free_symbols})
            used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z)) if mu[r] != 0]
            if key not in iso or len(used) < len(iso[key][2]):
                iso[key] = (e, inc, used)
    # 2x2 complete bipartite blocks
    blocks = []
    seen = set()
    for x1, x2 in combinations(btails, 2):
        if x1 in seen or x2 in seen:
            continue
        cand = [y for y in ttails if (x1, y) in iso and (x2, y) in iso]
        for y1, y2 in combinations(cand, 2):
            blocks.append((x1, x2, y1, y2))
            seen |= {x1, x2}
            break
    return (S0, S1, bidx, tidx, btails, ttails, iso, blocks)


def emit(oid, q, a, d):
    S0, S1, bidx, tidx, btails, ttails, iso, blocks = build(q, a, d)
    n0, n1 = len(S0), len(S1)
    if len(blocks) * 2 != len(btails):
        return None, 'blocks cover %d of %d bottom tails' % (len(blocks) * 2, len(btails))
    zall = sorted({z for v in iso.values() for z, _ in v[2]})
    masks = sorted({v[0] for v in iso.values()})
    # dressings for the diagonal layer on the free qubit
    dz = [z for z in dress(E1)]
    zname = {z: 'w%d' % r for r, z in enumerate(sorted(set(zall) | set(dz)))}
    mname = {m: 'ef%d' % r for r, m in enumerate(masks)}
    qs = ' '.join('q%d' % r for r in range(n0))
    rs = ' '.join('r%d' % r for r in range(n1))
    allv = qs + ' ' + rs
    idx = [(i,) for i in range(6)] + list(combinations(range(6), 2))
    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('import SixQubit.Frame')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit %d' % oid)
    W('')
    W('Orbit %d of `six_qubit_sslp.tex`: q = %d, angle vector' % (oid, q))
    W('a = (%s), residues 0 and %d.' % (', '.join(map(str, a)), d))
    W('')
    W('Qubit 1 has angle zero, so the amplitudes group into vectors in `ℂ²`.')
    W('The support splits into %d blocks of two bottom and two top tails, and' % len(blocks))
    W('every one of the four inner products inside a block is isolated by the')
    W('weight-at-most-two rows.  The diagonal conditions make the two block')
    W('frames equal, so `SixQubit.Frame.block_zero` kills each block and the')
    W('normalization fails.')
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
    W('def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]')
    W('')
    for r, x in enumerate(S0):
        W(bsline('y%d' % r, x))
    W('')
    for r, y in enumerate(S1):
        W(bsline('z%d' % r, y))
    W('')
    W('def S0 : Finset (SS.BitString 6) := {%s}' % ', '.join('y%d' % r for r in range(n0)))
    W('def S1 : Finset (SS.BitString 6) := {%s}' % ', '.join('z%d' % r for r in range(n1)))
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
    W('/-! ## Masks and dressings -/')
    W('')
    for m in masks:
        W(bsline(mname[m], m))
    W(bsline('efZ', E1))
    for z in sorted(zname, key=lambda z: zname[z]):
        W(bsline(zname[z], z))
    W('')
    W('/-! ## The off-diagonal layer -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    emitted = set()
    for m in masks:
        inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        W('theorem incidence_%s :' % mname[m])
        W('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
          % (mname[m], ', '.join('z%d' % t for _, t in inc)))
        for i2, t2 in inc:
            W('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide'
              % (mname[m], t2, t2, mname[m], i2))
        used_z = {z for k, v in iso.items() if v[0] == m for z, _ in v[2]}
        for z in sorted(used_z):
            for _, t2 in inc:
                W('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
                  % (mname[m], zname[z], t2, zname[z], t2,
                     'true' if dot(z, S1[t2]) else 'false'))
            body = ' '.join('%s star (c y%d) * d z%d'
                            % ('-' if dot(z, S1[t2]) else '+', i2, t2)
                            for i2, t2 in inc).lstrip('+ ')
            W('theorem ex_%s_%s (c d : SS.BitString 6 -> ℂ) :' % (mname[m], zname[z]))
            W('    offSum c d %s %s = %s := by' % (mname[m], zname[z], body))
            W('  unfold offSum')
            W('  rw [incidence_%s]' % mname[m])
            W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(inc) - 1))
              + (', ' if len(inc) > 1 else '') + 'Finset.sum_singleton]')
            W('  rw [' + ', '.join('flip_%s_%d' % (mname[m], t2) for _, t2 in inc) + ']')
            lem = ['sg_%s_%s_%d' % (mname[m], zname[z], t2) for _, t2 in inc]
            if any(dot(z, S1[t2]) for _, t2 in inc):
                lem.append('SixQubit.signMul_true')
            if any(not dot(z, S1[t2]) for _, t2 in inc):
                lem.append('SixQubit.signMul_false')
            W('  simp only [' + ', '.join(lem) + ']')
            W('  try ring')
            emitted.add((m, z))
        W('')
    W('/-! ## The diagonal layer on the free qubit -/')
    W('')
    W('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)')
    W('')
    W('def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
    W('      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)')
    W('')
    dinc0 = [(r, S0.index(xor(x, E1))) for r, x in enumerate(S0)]
    dinc1 = [(r, S1.index(xor(y, E1))) for r, y in enumerate(S1)]
    W('theorem dincB : S0.filter (fun x => SS.bxor x efZ ∈ S0) = S0 := by decide')
    W('theorem dincT : S1.filter (fun y => SS.bxor y efZ ∈ S1) = S1 := by decide')
    for r in range(n0):
        W('theorem dflipB_%d : SS.bxor y%d efZ = y%d := by decide'
          % (r, r, dinc0[r][1]))
    for r in range(n1):
        W('theorem dflipT_%d : SS.bxor z%d efZ = z%d := by decide'
          % (r, r, dinc1[r][1]))
    W('')
    DZ = sorted(set(dz))
    for z in DZ:
        for r in range(n0):
            W('theorem dsB_%s_%d : SS.bdot %s y%d = %s := by decide'
              % (zname[z], r, zname[z], r, 'true' if dot(z, S0[r]) else 'false'))
        for r in range(n1):
            W('theorem dsT_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (zname[z], r, zname[z], r, 'true' if dot(z, S1[r]) else 'false'))
        bodyB = ' '.join('%s star (c y%d) * c y%d'
                         % ('-' if dot(z, S0[r]) else '+', dinc0[r][1], r)
                         for r in range(n0)).lstrip('+ ')
        bodyT = ' '.join('%s star (dd z%d) * dd z%d'
                         % ('-' if dot(z, S1[r]) else '+', dinc1[r][1], r)
                         for r in range(n1)).lstrip('+ ')
        W('theorem dexB_%s (c : SS.BitString 6 -> ℂ) :' % zname[z])
        W('    diagBot c efZ %s = %s := by' % (zname[z], bodyB))
        W('  unfold diagBot')
        W('  rw [dincB]')
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (n0 - 1))
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('dflipB_%d' % r for r in range(n0)) + ']')
        lem = ['dsB_%s_%d' % (zname[z], r) for r in range(n0)]
        if any(dot(z, S0[r]) for r in range(n0)):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S0[r]) for r in range(n0)):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('theorem dexT_%s (dd : SS.BitString 6 -> ℂ) :' % zname[z])
        W('    diagTop dd efZ %s = %s := by' % (zname[z], bodyT))
        W('  unfold diagTop')
        W('  rw [dincT]')
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (n1 - 1))
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('dflipT_%d' % r for r in range(n1)) + ']')
        lem = ['dsT_%s_%d' % (zname[z], r) for r in range(n1)]
        if any(dot(z, S1[r]) for r in range(n1)):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S1[r]) for r in range(n1)):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
    W('/-! ## The moment system -/')
    W('')
    W('structure MomentSystem (%s : Real) : Prop where' % allv)
    W('  n0 : %s = 1' % ' + '.join('q%d' % r for r in range(n0)))
    W('  n1 : %s = 1' % ' + '.join('r%d' % r for r in range(n1)))
    for T in idx:
        lhs = [r for r in range(n0) if all(S0[r][j] == '1' for j in T)]
        rr = [r for r in range(n1) if all(S1[r][j] == '1' for j in T)]
        W('  m%s : %s = %s' % (''.join(str(j + 1) for j in T),
                               ' + '.join('q%d' % r for r in lhs) or '0',
                               ' + '.join('r%d' % r for r in rr) or '0'))
    W('')
    for r in range(n0):
        W('  nq%d : 0 ≤ q%d' % (r, r))
    for r in range(n1):
        W('  nr%d : 0 ≤ r%d' % (r, r))
    W('')
    fields = (['n0', 'n1'] + ['m%s' % ''.join(str(j + 1) for j in T) for T in idx]
              + ['nq%d' % r for r in range(n0)] + ['nr%d' % r for r in range(n1)])
    return L, (S0, S1, bidx, tidx, iso, blocks, zname, mname, DZ, fields,
               allv, n0, n1, dinc0, dinc1, emitted)
