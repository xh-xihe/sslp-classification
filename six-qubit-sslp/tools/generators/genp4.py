"""Emit SixQubit/Orbit15.lean and SixQubit/Orbit14.lean -- the sliced parity-four orbits.

Both orbits carry a free qubit (a zero-angle qubit) so the amplitudes group into
vectors in C^2 indexed by four effective parity bits.  One effective coordinate
has a weight-one physical Z character that can dress the free-qubit operators,
so the frame equality survives restriction to either of its two three-cube
slices.  On such a slice `SixQubit.ParityFour.slice_zero` forces zero mass, and
the two slices exhaust the fiber.

Every certificate below is solved for in exact rational arithmetic and checked
by reconstruction before a single line of Lean is written.
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

bits = lambda s: [int(c) for c in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(len(s)))
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]
unit = lambda i: ''.join('1' if j == i else '0' for j in range(6))
bsline = lambda nm, s: 'def %s : SS.BitString 6 := bs %s  -- %s' % (
    nm, ' '.join(BOOL[c] for c in s), s)

ORB = {
    15: dict(q=4, a=[0, 1, 2, 2, 2, 2], d=2, F=0, eff=[2, 3, 4, 5], sl=0,
             emask=unit(0), free='zero-angle qubit 1',
             note='Qubit 2 is frozen to 0 on both fibers and qubits 3,4,5,6 carry '
                  'the four effective parity bits.'),
    14: dict(q=4, a=[0, 1, 1, 2, 2, 2], d=2, F=0, eff=[1, 3, 4, 5], sl=0,
             emask=unit(0), free='zero-angle qubit 1',
             note='The residue forces x2 = x3 =: r on both fibers, and '
                  '(r, x4, x5, x6) are the four effective parity bits; the '
                  'character of r is the physical Z on qubit 2.'),
}


def build(o):
    """Index both fibers by (free bit, effective four-bit string)."""
    S0, S1 = fiber(o['a'], o['q'], 0), fiber(o['a'], o['q'], o['d'])

    def find(S, r, z):
        m = [x for x in S if x[o['F']] == r and all(x[o['eff'][k]] == z[k] for k in range(4))]
        assert len(m) == 1, ('indexing is not a bijection', r, z, m)
        return m[0]

    ys = [find(S0, r, z) for r in '01' for z in EVEN]
    zs = [find(S1, r, w) for r in '01' for w in ODD]
    assert sorted(ys) == sorted(S0) and sorted(zs) == sorted(S1)
    return ys, zs


def slices(o):
    """(bottom EVEN-indices, top ODD-indices) for the two slices, paired so that
    bottom i is the NON-neighbour of top i."""
    sl, dirs = o['sl'], [k for k in range(4) if k != o['sl']]
    out = []
    for s in '01':
        bot = [e for e in range(8) if EVEN[e][sl] == s]
        tops = []
        for e in bot:
            w = list(EVEN[e])
            for k in dirs:
                w[k] = '01'[w[k] == '0']
            tops.append(ODD.index(''.join(w)))
        out.append((bot, tops, dirs))
    return out


def offcerts(o, ys, zs):
    """For every direction and every edge, the exact rational dressing combination
    that isolates the single C^2 inner product."""
    certs, used = {}, {}
    for k in range(4):
        if k == o['sl']:
            continue
        e = unit(o['eff'][k])
        Z = dress(e)
        M = sp.Matrix([[(-1) ** dot(z, zs[t]) for t in range(16)] for z in Z])
        for oi in range(8):
            tgt = sp.Matrix([1 if t in (oi, oi + 8) else 0 for t in range(16)])
            sol, par = M.T.gauss_jordan_solve(tgt)
            sol = sol.subs({v: 0 for v in par})
            assert (M.T * sol - tgt).is_zero_matrix, 'isolation failed'
            mu = [(Z[i], sp.Rational(sol[i])) for i in range(len(Z)) if sol[i] != 0]
            certs[(k, oi)] = mu
            used.setdefault(k, set()).update(z for z, _ in mu)
    return certs, {k: sorted(v) for k, v in used.items()}


def momrows(ys, zs):
    R = [([1] * 16 + [0] * 16, 1), ([0] * 16 + [1] * 16, 1)]
    lab = ['n0', 'n1']
    ind = lambda s, i: 1 if s[i] == '1' else 0
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
    x = x.subs({v: 0 for v in par})
    return (A * x - b).is_zero_matrix


def check_moments(o, ys, zs):
    R, lab = momrows(ys, zs)
    for bot, tops, dirs in slices(o):
        for half in (0, 8):
            v = [0] * 32
            for e in bot:
                v[half + e] += 1
            for t in tops:
                v[16 + half + t] += -1
            assert derivable(R, v, 0), 'slice frame diagonal not derivable'
        for i in range(4):
            v = [0] * 32
            for j in range(4):
                if j != i:
                    v[16 + tops[j]] += 1
                    v[16 + 8 + tops[j]] += 1
            for i2 in range(4):
                v[bot[i2]] += sp.Rational(-1, 2)
                v[8 + bot[i2]] += sp.Rational(-1, 2)
            v[bot[i]] += -1
            v[8 + bot[i]] += -1
            assert derivable(R, v, 0), 'neighbour-sum identity not derivable'
    return R, lab


def emit(oid):
    o = ORB[oid]
    ys, zs = build(o)
    R, lab = check_moments(o, ys, zs)
    certs, used = offcerts(o, ys, zs)
    dirs = [k for k in range(4) if k != o['sl']]
    fmask = o['emask']
    fdress = [ALL[0], fmask, unit(o['eff'][o['sl']]), xor(fmask, unit(o['eff'][o['sl']]))]
    zname, mname = {}, {}
    allz = sorted(set(z for v in used.values() for z in v) | set(fdress))
    for r, z in enumerate(allz):
        zname[z] = 'w%d' % r
    for k in dirs:
        mname[k] = 'ef%d' % k
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
    W('# Six-qubit no-go for moment orbit %d' % oid)
    W('')
    W('Orbit %d of `six_qubit_sslp.tex`: q = %d, angle vector' % (oid, o['q']))
    W('a = (%s), residues 0 and %d.' % (', '.join(map(str, o['a'])), o['d']))
    W('')
    W(o['note'])
    W('Amplitudes are collected over the %s into vectors in `ℂ²`, so' % o['free'])
    W('the fibers are indexed by `(free bit, effective four-bit string)`; the')
    W('bottom fiber carries the even strings and the top fiber the odd ones.')
    W('')
    W('Effective coordinate %d has a weight-one physical `Z` character, which may')
    W('dress the free-qubit operators without leaving weight two.  Both of its')
    W('three-cube slices therefore inherit the full frame equality, and')
    W('`SixQubit.ParityFour.slice_zero` gives each slice zero mass.  The two')
    W('slices exhaust the fiber, contradicting normalization.')
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
    W('def av : Fin 6 -> ZMod %d := ![%s]' % (o['q'], ', '.join(map(str, o['a']))))
    W('')
    W('theorem S0_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = 0) = S0 := by')
    W('  decide')
    W('')
    W('theorem S1_eq_fiber :')
    W('    (Finset.univ : Finset (SS.BitString 6)).filter')
    W('      (fun x => SS.weight av x = %d) = S1 := by' % o['d'])
    W('  decide')
    W('')
    W('/-! ## Masks and dressings -/')
    W('')
    for k in dirs:
        W(bsline(mname[k], unit(o['eff'][k])))
    W(bsline('efF', fmask))
    for z in allz:
        W(bsline(zname[z], z))
    W('')
    W('/-! ## The off-diagonal layer -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    flipmap = {}
    for k in dirs:
        e = unit(o['eff'][k])
        flipmap[k] = [ys.index(xor(zs[t], e)) for t in range(16)]
        W('theorem incidence_%s :' % mname[k])
        W('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
          % (mname[k], ', '.join('z%d' % t for t in range(16))))
        for t in range(16):
            W('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide'
              % (mname[k], t, t, mname[k], flipmap[k][t]))
        for z in used[k]:
            for t in range(16):
                W('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
                  % (mname[k], zname[z], t, zname[z], t,
                     'true' if dot(z, zs[t]) else 'false'))
            body = ' '.join('%s star (c y%d) * d z%d'
                            % ('-' if dot(z, zs[t]) else '+', flipmap[k][t], t)
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
        bodyB = ' '.join('%s star (c y%d) * c y%d' % ('-' if dot(z, ys[r]) else '+', dB[r], r)
                         for r in range(16)).lstrip('+ ')
        bodyT = ' '.join('%s star (dd z%d) * dd z%d' % ('-' if dot(z, zs[r]) else '+', dT[r], r)
                         for r in range(16)).lstrip('+ ')
        for tag, dn, body, sgn, syms, arr in (
                ('B', 'diagBot', bodyB, ys, 'c', 'y'), ('T', 'diagTop', bodyT, zs, 'dd', 'z')):
            W('theorem dex%s_%s (%s : SS.BitString 6 -> ℂ) :' % (tag, zname[z], syms))
            W('    %s %s efF %s = %s := by' % (dn, syms, zname[z], body))
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
        if rhs == 1:
            W('  %s : %s = 1' % (nm, lhs))
        else:
            W('  %s : %s = %s' % (nm, lhs, rr))
    W('')
    for r in range(16):
        W('  nq%d : 0 ≤ q%d' % (r, r))
    for r in range(16):
        W('  nr%d : 0 ≤ r%d' % (r, r))
    W('')
    fields = list(lab) + ['nq%d' % r for r in range(16)] + ['nr%d' % r for r in range(16)]
    dest = '⟨' + ', '.join(fields) + '⟩'
    # derived linear facts
    sls = slices(o)
    parts = []
    for si, (bot, tops, _) in enumerate(sls):
        parts.append('(%s = %s)'
                     % (' + '.join('q%d' % e for e in bot),
                        ' + '.join('r%d' % t for t in tops)))
        parts.append('(%s = %s)'
                     % (' + '.join('q%d' % (8 + e) for e in bot),
                        ' + '.join('r%d' % (8 + t) for t in tops)))
        for i in range(4):
            P = ' + '.join('q%d + q%d' % (bot[j], 8 + bot[j]) for j in range(4))
            parts.append('(%s = (%s) / 2 + (q%d + q%d))'
                         % (' + '.join('r%d + r%d' % (tops[j], 8 + tops[j])
                                       for j in range(4) if j != i),
                            P, bot[i], 8 + bot[i]))
    W('/-- Everything the slice argument needs from the moment polytope: the two')
    W('slice frame diagonals and the four neighbour-sum identities, per slice. -/')
    W('theorem MomentSystem.sliceData {%s : Real} (h : MomentSystem %s) :'
      % (allv, allv))
    W('    ' + (NL + '      ∧ ').join(parts))
    W('    := by')
    W('  obtain %s := h' % dest)
    W('  refine ⟨%s⟩ <;> linarith' % ', '.join(['?_'] * len(parts)))
    W('')
    W('/-! ## The no-go -/')
    hyps, hnames = [], []
    for k in dirs:
        for z in used[k]:
            hnames.append('ho_%s_%s' % (mname[k], zname[z]))
            hyps.append('    (%s : offSum c d %s %s = 0)' % (hnames[-1], mname[k], zname[z]))
    dnames = []
    for z in fdress:
        dnames.append('hd_%s' % zname[z])
        hyps.append('    (%s : diagBot c efF %s = diagTop d efF %s)'
                    % (dnames[-1], zname[z], zname[z]))
    W('')
    W('/-- **Orbit %d is impossible.** -/' % oid)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            %s' % ' '.join('(%s (c y%d))' % (NS, r) for r in range(16)))
    W('            %s)' % ' '.join('(%s (d z%d))' % (NS, r) for r in range(16)))
    for h in hyps:
        W(h)
    W('    : False := by')
    for k in dirs:
        for z in used[k]:
            W('  rw [ex_%s_%s] at ho_%s_%s' % (mname[k], zname[z], mname[k], zname[z]))
    for z in fdress:
        W('  rw [dexB_%s, dexT_%s] at hd_%s' % (zname[z], zname[z], zname[z]))
    W('  obtain ⟨%s⟩ := hm.sliceData' % ', '.join('sd%d' % i for i in range(len(parts))))
    # edge orthogonalities
    for si, (bot, tops, dr) in enumerate(sls):
        for i in range(4):
            for j in range(4):
                if i == j:
                    continue
                e, t = bot[i], tops[j]
                k = [kk for kk in dr if EVEN[e][kk] != ODD[t][kk]]
                assert len(k) == 1, 'not a single-coordinate edge'
                k = k[0]
                mu = certs[(k, t)]
                W('  have s%do%d%d : star (c y%d) * d z%d + star (c y%d) * d z%d = 0 := by'
                  % (si, i + 1, j + 1, e, t, 8 + e, 8 + t))
                W('    linear_combination %s'
                  % ' + '.join('(%s : ℂ) * ho_%s_%s' % (str(cf), mname[k], zname[z])
                               for z, cf in mu))
        # frame off-diagonal entry
        s = '01'.index(EVEN[bot[0]][o['sl']])
        cf = [sp.Rational(1, 4), sp.Rational(1, 4),
              sp.Rational((-1) ** s, 4), sp.Rational((-1) ** s, 4)]
        W('  have s%dfB : %s' % (si, ' + '.join('c y%d * star (c y%d)' % (e, 8 + e)
                                                for e in bot)))
        W('      = %s := by' % ' + '.join('d z%d * star (d z%d)' % (t, 8 + t) for t in tops))
        W('    linear_combination %s'
          % ' + '.join('(%s : ℂ) * hd_%s' % (str(cf[m]), zname[fdress[m]]) for m in range(4)))
        W('  have s%dz : %s = 0 :='
          % (si, ' + '.join('%s (c y%d) + %s (c y%d)' % (NS, e, NS, 8 + e) for e in bot)))
        args = ['s%do%d%d' % (si, i + 1, j + 1) for i in range(4) for j in range(4) if i != j]
        base = si * 6
        args += ['sd%d' % base, 'sd%d' % (base + 1), 's%dfB' % si]
        args += ['sd%d' % (base + 2 + i) for i in range(4)]
        W('    SixQubit.ParityFour.slice_zero %s' % ' '.join(args))
    W('  obtain %s := hm' % dest)
    W('  linarith [%s]' % ', '.join('s%dz' % si for si in range(len(sls))))
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % oid)
    out = os.path.join('SixQubit', 'Orbit%d.lean' % oid)
    with io.open(out, 'w', encoding='utf-8', newline='\n') as f:
        f.write(NL.join(L) + NL)
    print('wrote %s  (%d lines)' % (out, len(L) + 1))


for oid in (15, 14):
    emit(oid)
