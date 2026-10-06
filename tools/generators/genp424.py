"""Emit SixQubit/Orbit24.lean -- the un-sliced parity-four orbit.

Orbit 24 has no zero-angle qubit.  Its C^2 comes from the repetition pair
(qubit 1, qubit 6), which the residue forces to agree; under the repetition
isometry Z_1, X_1X_6 and Y_1X_6 -- all of weight at most two -- represent the
full one-qubit operator algebra, so the two frame operators agree globally.
They do NOT agree on a slice: slicing the off-diagonal frame entry would need
X_1X_6Z_i, of weight three.  So the sliced inequality of orbits 14/15 is
unavailable and the full four-cube version is used instead.

On the full cube the inequality is exactly tight, so instead of an immediate
contradiction it forces the whole equality case: every mass equals 1/8, the
off-diagonal frame entry vanishes, and every distance-three wedge vanishes.
Two Plucker steps and one Lagrange identity then close it.
"""
import io
import os
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
sys.path.insert(0, '.')
from orbit import fiber

NL = chr(10)
BOOL = {'0': 'false', '1': 'true '}
ALL = [format(k, '06b') for k in range(64)]
EVEN = [format(k, '04b') for k in range(16) if bin(k).count('1') % 2 == 0]
ODD = [format(k, '04b') for k in range(16) if bin(k).count('1') % 2 == 1]
NS = 'Complex.normSq'
PF = 'SixQubit.ParityFour'

bits = lambda s: [int(c) for c in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(len(s)))
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]
unit = lambda i: ''.join('1' if j == i else '0' for j in range(6))
hd = lambda s, t: sum(1 for i in range(len(s)) if s[i] != t[i])
bsline = lambda nm, s: 'def %s : SS.BitString 6 := bs %s  -- %s' % (
    nm, ' '.join(BOOL[c] for c in s), s)

O = dict(q=4, a=[1, 2, 2, 2, 2, 3], d=2, F=0, eff=[1, 2, 3, 4], emask='100001')
OID = 24


def build():
    S0, S1 = fiber(O['a'], O['q'], 0), fiber(O['a'], O['q'], O['d'])

    def find(S, r, z):
        m = [x for x in S if x[O['F']] == r and all(x[O['eff'][k]] == z[k] for k in range(4))]
        assert len(m) == 1, ('indexing is not a bijection', r, z, m)
        return m[0]

    ys = [find(S0, r, z) for r in '01' for z in EVEN]
    zs = [find(S1, r, w) for r in '01' for w in ODD]
    assert sorted(ys) == sorted(S0) and sorted(zs) == sorted(S1)
    # the structural claim of the paper: qubits 1 and 6 are tied on both fibers
    assert all(x[0] == x[5] for x in S0 + S1), 'repetition pair not forced'
    return ys, zs


def offcerts(ys, zs):
    certs, used = {}, {}
    for k in range(4):
        e = unit(O['eff'][k])
        Z = dress(e)
        M = sp.Matrix([[(-1) ** dot(z, zs[t]) for t in range(16)] for z in Z])
        for oi in range(8):
            tgt = sp.Matrix([1 if t in (oi, oi + 8) else 0 for t in range(16)])
            sol, par = M.T.gauss_jordan_solve(tgt)
            sol = sol.subs({v: 0 for v in par})
            assert (M.T * sol - tgt).is_zero_matrix, 'isolation failed'
            certs[(k, oi)] = [(Z[i], sp.Rational(sol[i])) for i in range(len(Z)) if sol[i] != 0]
            used.setdefault(k, set()).update(z for z, _ in certs[(k, oi)])
    return certs, {k: sorted(v) for k, v in used.items()}


def momrows(ys, zs):
    R = [([1] * 16 + [0] * 16, 1), ([0] * 16 + [1] * 16, 1)]
    lab = ['n0', 'n1']
    idx = [(i,) for i in range(6)] + list(combinations(range(6), 2))
    for T in idx:
        R.append(([1 if all(x[j] == '1' for j in T) else 0 for x in ys]
                  + [-1 if all(y[j] == '1' for j in T) else 0 for y in zs], 0))
        lab.append('m' + ''.join(str(j + 1) for j in T))
    return R, lab


def derivable(R, tgt, rhs):
    A = sp.Matrix([r[0] + [r[1]] for r in R]).T
    b = sp.Matrix(list(tgt) + [rhs])
    try:
        x, par = A.gauss_jordan_solve(b)
    except ValueError:
        return False
    return (A * x.subs({v: 0 for v in par}) - b).is_zero_matrix


def check(R):
    # global frame diagonals
    for half in (0, 8):
        v = [0] * 32
        for e in range(8):
            v[half + e] = 1
        for t in range(8):
            v[16 + half + t] = -1
        assert derivable(R, v, 0), 'global frame diagonal not derivable'
    # neighbour sums, both parities
    for i in range(8):
        v = [0] * 32
        for j in range(8):
            if hd(EVEN[i], ODD[j]) == 1:
                v[16 + j] += 1
                v[16 + 8 + j] += 1
        v[i] += -2
        v[8 + i] += -2
        assert derivable(R, v, sp.Rational(1, 4)), 'even neighbour sum not derivable'
    for j in range(8):
        v = [0] * 32
        for i in range(8):
            if hd(EVEN[i], ODD[j]) == 1:
                v[i] += 1
                v[8 + i] += 1
        v[16 + j] += -2
        v[16 + 8 + j] += -2
        assert derivable(R, v, sp.Rational(1, 4)), 'odd neighbour sum not derivable'


def main():
    ys, zs = build()
    R, lab = momrows(ys, zs)
    check(R)
    certs, used = offcerts(ys, zs)
    fmask = O['emask']
    fdress = [ALL[0], unit(O['F'])]
    zname = {}
    for r, z in enumerate(sorted(set(z for v in used.values() for z in v) | set(fdress))):
        zname[z] = 'w%d' % r
    mname = {k: 'ef%d' % k for k in range(4)}
    nbr = {i: [j for j in range(8) if hd(EVEN[i], ODD[j]) == 1] for i in range(8)}
    non = {i: [j for j in range(8) if hd(EVEN[i], ODD[j]) == 3] for i in range(8)}
    p = lambda i: '(%s (c y%d) + %s (c y%d))' % (NS, i, NS, 8 + i)
    qq = lambda j: '(%s (d z%d) + %s (d z%d))' % (NS, j, NS, 8 + j)
    wd = lambda i, j: 'c y%d * d z%d - c y%d * d z%d' % (i, 8 + j, 8 + i, j)
    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('import SixQubit.Frame')
    W('import SixQubit.ParityFour')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit %d' % OID)
    W('')
    W('Orbit %d of `six_qubit_sslp.tex`: q = %d, angle vector' % (OID, O['q']))
    W('a = (%s), residues 0 and %d.' % (', '.join(map(str, O['a'])), O['d']))
    W('')
    W('The residue forces x1 = x6 =: r on both fibers, so the amplitudes group')
    W('into vectors in `ℂ²` indexed by the effective repetition bit, with')
    W('(x2, x3, x4, x5) the four effective parity bits: even on the bottom fiber,')
    W('odd on the top one.  On the repetition qubit `Z₁`, `X₁X₆` and `Y₁X₆` -- all')
    W('of weight at most two -- represent the full one-qubit operator algebra, so')
    W('the two frame operators agree.  They do not agree slice by slice: dressing')
    W('`X₁X₆` with a `Z` on a middle qubit costs weight three.  The full four-cube')
    W('inequality of `SixQubit.ParityFour` is therefore used, and it is exactly')
    W('tight; the equality case pins every mass to 1/8, kills the off-diagonal')
    W('frame entry, and makes every distance-three pair parallel.  Two Plücker')
    W('steps and one Lagrange identity finish it.')
    W('')
    W('Everything computational is decided by the Lean kernel; `native_decide`')
    W('is not used.')
    W('-/')
    W('')
    W('namespace SixQubit.Orbit%d' % OID)
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
    for r, x in enumerate(ys):
        W(bsline('y%d' % r, x))
    W('')
    for r, y in enumerate(zs):
        W(bsline('z%d' % r, y))
    W('')
    W('def S0 : Finset (SS.BitString 6) := {%s}' % ', '.join('y%d' % r for r in range(16)))
    W('def S1 : Finset (SS.BitString 6) := {%s}' % ', '.join('z%d' % r for r in range(16)))
    W('')
    W('def av : Fin 6 -> ZMod %d := ![%s]' % (O['q'], ', '.join(map(str, O['a']))))
    W('')
    W('theorem S0_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = 0) = S0 := by')
    W('  decide')
    W('')
    W('theorem S1_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = %d) = S1 := by' % O['d'])
    W('  decide')
    W('')
    W('/-! ## Masks and dressings -/')
    W('')
    for k in range(4):
        W(bsline(mname[k], unit(O['eff'][k])))
    W(bsline('efF', fmask))
    for z in sorted(zname, key=lambda z: int(zname[z][1:])):
        W(bsline(zname[z], z))
    W('')
    W('/-! ## The off-diagonal layer -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    flip = {}
    for k in range(4):
        e = unit(O['eff'][k])
        flip[k] = [ys.index(xor(zs[t], e)) for t in range(16)]
        W('theorem incidence_%s :' % mname[k])
        W('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
          % (mname[k], ', '.join('z%d' % t for t in range(16))))
        for t in range(16):
            W('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide'
              % (mname[k], t, t, mname[k], flip[k][t]))
        for z in used[k]:
            for t in range(16):
                W('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
                  % (mname[k], zname[z], t, zname[z], t,
                     'true' if dot(z, zs[t]) else 'false'))
            body = ' '.join('%s star (c y%d) * d z%d'
                            % ('-' if dot(z, zs[t]) else '+', flip[k][t], t)
                            for t in range(16)).lstrip('+ ')
            W('theorem ex_%s_%s (c d : SS.BitString 6 -> ℂ) :' % (mname[k], zname[z]))
            W('    offSum c d %s %s = %s := by' % (mname[k], zname[z], body))
            W('  unfold offSum')
            W('  rw [incidence_%s]' % mname[k])
            W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * 15)
              + ', Finset.sum_singleton]')
            W('  rw [' + ', '.join('flip_%s_%d' % (mname[k], t) for t in range(16)) + ']')
            lem = ['sg_%s_%s_%d' % (mname[k], zname[z], t) for t in range(16)]
            if any(dot(z, zs[t]) for t in range(16)):
                lem.append('SixQubit.signMul_true')
            if any(not dot(z, zs[t]) for t in range(16)):
                lem.append('SixQubit.signMul_false')
            W('  simp only [' + ', '.join(lem) + ']')
            W('  try ring')
        W('')
    W('/-! ## The diagonal layer on the repetition qubit -/')
    W('')
    W('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)')
    W('')
    W('def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
    W('      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)')
    W('')
    dB = [ys.index(xor(x, fmask)) for x in ys]
    dT = [zs.index(xor(y, fmask)) for y in zs]
    W('theorem dincB : S0.filter (fun x => SS.bxor x efF ∈ S0) = {%s} := by decide'
      % ', '.join('y%d' % r for r in range(16)))
    W('theorem dincT : S1.filter (fun y => SS.bxor y efF ∈ S1) = {%s} := by decide'
      % ', '.join('z%d' % r for r in range(16)))
    for r in range(16):
        W('theorem dflipB_%d : SS.bxor y%d efF = y%d := by decide' % (r, r, dB[r]))
    for r in range(16):
        W('theorem dflipT_%d : SS.bxor z%d efF = z%d := by decide' % (r, r, dT[r]))
    W('')
    for z in fdress:
        for r in range(16):
            W('theorem dsB_%s_%d : SS.bdot %s y%d = %s := by decide'
              % (zname[z], r, zname[z], r, 'true' if dot(z, ys[r]) else 'false'))
        for r in range(16):
            W('theorem dsT_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (zname[z], r, zname[z], r, 'true' if dot(z, zs[r]) else 'false'))
        for tag, dn, sgn, sym, arr in (('B', 'diagBot', ys, 'c', 'y'),
                                       ('T', 'diagTop', zs, 'dd', 'z')):
            fl = dB if tag == 'B' else dT
            body = ' '.join('%s star (%s %s%d) * %s %s%d'
                            % ('-' if dot(z, sgn[r]) else '+', sym, arr, fl[r], sym, arr, r)
                            for r in range(16)).lstrip('+ ')
            W('theorem dex%s_%s (%s : SS.BitString 6 -> ℂ) :' % (tag, zname[z], sym))
            W('    %s %s efF %s = %s := by' % (dn, sym, zname[z], body))
            W('  unfold %s' % dn)
            W('  rw [dinc%s]' % tag)
            W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * 15)
              + ', Finset.sum_singleton]')
            W('  rw [' + ', '.join('dflip%s_%d' % (tag, r) for r in range(16)) + ']')
            lem = ['ds%s_%s_%d' % (tag, zname[z], r) for r in range(16)]
            if any(dot(z, sgn[r]) for r in range(16)):
                lem.append('SixQubit.signMul_true')
            if any(not dot(z, sgn[r]) for r in range(16)):
                lem.append('SixQubit.signMul_false')
            W('  simp only [' + ', '.join(lem) + ']')
            W('  try ring')
        W('')
    W('/-! ## The moment system -/')
    W('')
    qs = ' '.join('q%d' % r for r in range(16))
    rs = ' '.join('r%d' % r for r in range(16))
    allv = qs + ' ' + rs
    W('/-- The two normalizations, the twenty-one moment equalities, and the')
    W('nonnegativity of every probability. -/')
    W('structure MomentSystem (%s : Real) : Prop where' % allv)
    for (vec, rhs), nm in zip(R, lab):
        lhs = ' + '.join(('q%d' % j if j < 16 else 'r%d' % (j - 16))
                         for j in range(32) if vec[j] == 1) or '0'
        rr = ' + '.join(('q%d' % j if j < 16 else 'r%d' % (j - 16))
                        for j in range(32) if vec[j] == -1) or '0'
        W('  %s : %s = %s' % (nm, lhs, '1' if rhs == 1 else rr))
    W('')
    for r in range(16):
        W('  nq%d : 0 ≤ q%d' % (r, r))
    for r in range(16):
        W('  nr%d : 0 ≤ r%d' % (r, r))
    W('')
    fields = list(lab) + ['nq%d' % r for r in range(16)] + ['nr%d' % r for r in range(16)]
    dest = '⟨' + ', '.join(fields) + '⟩'
    parts = ['(%s = %s)' % (' + '.join('q%d' % e for e in range(8)),
                            ' + '.join('r%d' % t for t in range(8))),
             '(%s = %s)' % (' + '.join('q%d' % (8 + e) for e in range(8)),
                            ' + '.join('r%d' % (8 + t) for t in range(8)))]
    for i in range(8):
        parts.append('(%s = 1 / 4 + 2 * (q%d + q%d))'
                     % (' + '.join('r%d + r%d' % (j, 8 + j) for j in nbr[i]), i, 8 + i))
    for j in range(8):
        parts.append('(%s = 1 / 4 + 2 * (r%d + r%d))'
                     % (' + '.join('q%d + q%d' % (i, 8 + i)
                                   for i in range(8) if hd(EVEN[i], ODD[j]) == 1), j, 8 + j))
    parts.append('(%s = 1)' % ' + '.join('q%d' % r for r in range(16)))
    W('/-- Everything the cube argument needs from the moment polytope: the two')
    W('frame diagonals and the sixteen neighbour-sum identities. -/')
    W('theorem MomentSystem.cubeData {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    W('    ' + (NL + '      ∧ ').join(parts))
    W('    := by')
    W('  obtain %s := h' % dest)
    W('  refine ⟨%s⟩ <;> linarith' % ', '.join(['?_'] * len(parts)))
    W('')
    W('/-! ## The no-go -/')
    W('')
    hyps = []
    for k in range(4):
        for z in used[k]:
            hyps.append('    (ho_%s_%s : offSum c d %s %s = 0)'
                        % (mname[k], zname[z], mname[k], zname[z]))
    for z in fdress:
        hyps.append('    (hd_%s : diagBot c efF %s = diagTop d efF %s)'
                    % (zname[z], zname[z], zname[z]))
    W('set_option maxHeartbeats 4000000 in')
    W('/-- **Orbit %d is impossible.** -/' % OID)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            %s' % ' '.join('(%s (c y%d))' % (NS, r) for r in range(16)))
    W('            %s)' % ' '.join('(%s (d z%d))' % (NS, r) for r in range(16)))
    for h in hyps:
        W(h)
    W('    : False := by')
    for k in range(4):
        for z in used[k]:
            W('  rw [ex_%s_%s] at ho_%s_%s' % (mname[k], zname[z], mname[k], zname[z]))
    for z in fdress:
        W('  rw [dexB_%s, dexT_%s] at hd_%s' % (zname[z], zname[z], zname[z]))
    W('  obtain ⟨%s⟩ := hm.cubeData' % ', '.join('cd%d' % i for i in range(len(parts))))
    # edge orthogonalities
    for i in range(8):
        for j in nbr[i]:
            k = [kk for kk in range(4) if EVEN[i][kk] != ODD[j][kk]][0]
            W('  have g%d_%d : star (c y%d) * d z%d + star (c y%d) * d z%d = 0 := by'
              % (i, j, i, j, 8 + i, 8 + j))
            W('    linear_combination %s'
              % ' + '.join('(%s : ℂ) * ho_%s_%s' % (str(cf), mname[k], zname[z])
                           for z, cf in certs[(k, j)]))
    # frame off-diagonal
    W('  have fB : %s' % ' + '.join('c y%d * star (c y%d)' % (i, 8 + i) for i in range(8)))
    W('      = %s := by' % ' + '.join('d z%d * star (d z%d)' % (j, 8 + j) for j in range(8)))
    W('    linear_combination (1/2 : ℂ) * hd_%s + (1/2 : ℂ) * hd_%s'
      % (zname[fdress[0]], zname[fdress[1]]))
    W('  have tot := %s.total8 cd0 cd1 fB' % PF)
    for i in range(8):
        for j in nbr[i]:
            W('  have e%d_%d := %s.wedge_of_orth g%d_%d' % (i, j, PF, i, j))
    for i in range(8):
        W('  have rr%d : %s' % (i, ' + '.join('%s (%s)' % (NS, wd(i, j)) for j in nbr[i])))
        W('      = %s * (1 / 4 + 2 * %s) := by' % (p(i), p(i)))
        W('    rw [%s, ← cd%d]' % (', '.join('e%d_%d' % (i, j) for j in nbr[i]), 2 + i))
        W('    ring')
    W('  have hb : (0:Real) ≤ %s (%s) := Complex.normSq_nonneg _'
      % (NS, ' + '.join('c y%d * star (c y%d)' % (i, 8 + i) for i in range(8))))
    for i in range(8):
        for j in non[i]:
            W('  have nn%d_%d : (0:Real) ≤ %s (%s) := Complex.normSq_nonneg _'
              % (i, j, NS, wd(i, j)))
    for i in range(8):
        W('  have sq%d : (0:Real) ≤ (%s - 1/8) * (%s - 1/8) := mul_self_nonneg _'
          % (i, p(i), p(i)))
    A8 = ' + '.join('%s (c y%d)' % (NS, i) for i in range(8))
    C8 = ' + '.join('%s (c y%d)' % (NS, 8 + i) for i in range(8))
    W('  have hnorm : (%s) + (%s) = 1 := by linarith [cd%d]' % (A8, C8, len(parts) - 1))
    W('  have hACsq : ((%s) + (%s)) * ((%s) + (%s)) = 1 := by' % (A8, C8, A8, C8))
    W('    rw [hnorm]; norm_num')
    W('  have master : 2 * (%s)'
      % ' + '.join('(%s - 1/8) * (%s - 1/8)' % (p(i), p(i)) for i in range(8)))
    W('      + (%s)' % ' + '.join('%s (%s)' % (NS, wd(i, j))
                                  for i in range(8) for j in non[i]))
    W('      + 2 * %s (%s) ≤ 0 := by'
      % (NS, ' + '.join('c y%d * star (c y%d)' % (i, 8 + i) for i in range(8))))
    W('    linarith [tot, %s, hnorm, hACsq,' % ', '.join('rr%d' % i for i in range(8)))
    W('      sq_nonneg ((%s) - (%s))]' % (A8, C8))
    for i in range(8):
        W('  have p%d : %s = 1/8 := by' % (i, p(i)))
        W('    have h := %s.sq_nonpos (x := %s - 1/8) (by linarith)' % (PF, p(i)))
        W('    linarith')
    # the two top masses that the endgame needs
    for j in (3, 7):
        W('  have qq%d : %s = 1/8 := by linarith [cd%d]' % (j, qq(j), 10 + j))
    # the three distance-three wedges the endgame needs
    for (i, j) in ((0, 3), (6, 3), (0, 7)):
        W('  have z%d_%d : %s = 0 := by' % (i, j, wd(i, j)))
        W('    have h : %s (%s) = 0 := le_antisymm (by linarith) (Complex.normSq_nonneg _)'
          % (NS, wd(i, j)))
        W('    exact Complex.normSq_eq_zero.mp h')
    W('  have qc3 : d z3 * star (d z3) + d z11 * star (d z11) = ((1:ℂ)/8) := by')
    W('    rw [SixQubit.Frame.self_mul_star, SixQubit.Frame.self_mul_star]')
    W('    have := congrArg (fun x : Real => (x : ℂ)) qq3')
    W('    push_cast at this ⊢')
    W('    linear_combination this')
    W('  have pc0 : c y0 * star (c y0) + c y8 * star (c y8) = ((1:ℂ)/8) := by')
    W('    rw [SixQubit.Frame.self_mul_star, SixQubit.Frame.self_mul_star]')
    W('    have := congrArg (fun x : Real => (x : ℂ)) p0')
    W('    push_cast at this ⊢')
    W('    linear_combination this')
    W('  have par : c y0 * c y14 - c y8 * c y6 = 0 := by')
    W('    have hp := %s.plucker (a0 := d z3) (a1 := d z11)' % PF)
    W('      (b0 := c y0) (b1 := c y8) (c0 := c y6) (c1 := c y14)')
    W('      (by linear_combination -z0_3) (by linear_combination -z6_3)')
    W('    rw [qc3] at hp')
    W('    linear_combination (8:ℂ) * hp')
    W('  have fin : c y6 * d z15 - c y14 * d z7 = 0 := by')
    W('    have hp := %s.plucker (a0 := c y0) (a1 := c y8)' % PF)
    W('      (b0 := c y6) (b1 := c y14) (c0 := d z7) (c1 := d z15)')
    W('      (by linear_combination par) (by linear_combination z0_7)')
    W('    rw [pc0] at hp')
    W('    linear_combination (8:ℂ) * hp')
    W('  have hL := %s.lagrange (c y6) (c y14) (d z7) (d z15)' % PF)
    W('  rw [fin, g6_7, Complex.normSq_zero, p6, qq7] at hL')
    W('  norm_num at hL')
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % OID)
    out = os.path.join('SixQubit', 'Orbit%d.lean' % OID)
    with io.open(out, 'w', encoding='utf-8', newline='\n') as f:
        f.write(NL.join(L) + NL)
    print('wrote %s  (%d lines)' % (out, len(L) + 1))
    print('EVEN idx 0 = %s, 6 = %s ; ODD idx 3 = %s, 7 = %s'
          % (EVEN[0], EVEN[6], ODD[3], ODD[7]))
    print('d(E0,O3)=%d d(E6,O3)=%d d(E0,O7)=%d d(E6,O7)=%d'
          % (hd(EVEN[0], ODD[3]), hd(EVEN[6], ODD[3]),
             hd(EVEN[0], ODD[7]), hd(EVEN[6], ODD[7])))


main()
