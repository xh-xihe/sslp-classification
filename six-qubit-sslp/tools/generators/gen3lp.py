"""Odd-triangle generator on LP-bounded vertices.

`gen3.py` demanded that the three triangle vertices be *forced constants* of
the moment polytope (with one vertex allowed to be a positive shell sum).  On
several fibers the polytope is positive-dimensional and no useful vertex is a
forced constant, yet each of the three probabilities is still bounded away
from zero over the whole polytope.  This generator uses the exact LP lower
bound instead, which `linarith` reproves from the `MomentSystem` fields.

q, a and the residue delta = q/m always come from `tools/manifest.json`.

    python tools/run.py generators/gen3lp.py 65
"""
import io
import json
import os
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from orbit import fiber
from lpbound import lower_bounds

NL = chr(10)
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    '..', '..'))
MAN = json.loads(io.open(os.path.join(REPO, 'tools', 'manifest.json'),
                         encoding='utf-8').read())
BOOL = {'0': 'false', '1': 'true '}
bits = lambda s: [int(c) for c in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
comp = lambda s: ''.join('01'[1 - int(c)] for c in s)
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]
bsline = lambda nm, s: 'def %s : SS.BitString 6 := bs %s  -- %s' % (
    nm, ' '.join(BOOL[c] for c in s), s)
IDX = [(i,) for i in range(6)] + list(combinations(range(6), 2))


def reciprocal(S0, S1):
    """For every unordered pair {i,j} of bottom indices, the cheapest rational
    combination of admissible dressings isolating the reciprocal sum."""
    n0 = len(S0)
    top = {r: S1.index(comp(S0[r])) for r in range(n0)}
    rec = {}
    for e in ALL:
        if not 1 <= len(supp(e)) <= 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        if not inc:
            continue
        Z = dress(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        for k1, k2 in combinations(range(len(inc)), 2):
            i1, t1 = inc[k1]
            i2, t2 = inc[k2]
            if not (top[i1] == t2 and top[i2] == t1):
                continue
            tgt = sp.Matrix([1 if r in (k1, k2) else 0 for r in range(len(inc))])
            try:
                mu = W.T.gauss_jordan_solve(tgt)[0]
            except ValueError:
                continue
            mu = mu.subs({s: 0 for s in mu.free_symbols})
            used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z)) if mu[r] != 0]
            key = (min(i1, i2), max(i1, i2))
            if key not in rec or len(used) < len(rec[key][2]):
                rec[key] = (e, inc, used, i1, t1, i2, t2)
    return rec, top


def choose(rec, lo, n0):
    """Cheapest triangle all of whose vertices have a positive LP lower bound."""
    G = {k: set() for k in range(n0)}
    for (i, j) in rec:
        G[i].add(j)
        G[j].add(i)
    best = None
    for A, B, C in combinations(range(n0), 3):
        if not (B in G[A] and C in G[A] and C in G[B]):
            continue
        if not (lo[A] > 0 and lo[B] > 0 and lo[C] > 0):
            continue
        cost = sum(len(rec[p][2]) for p in [(A, B), (A, C), (B, C)])
        if best is None or cost < best[0]:
            best = (cost, A, B, C)
    return best


def emit(oid):
    E = MAN[str(oid)]
    q, a, d = E['q'], E['a'], E['d']
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    n0, n1 = len(S0), len(S1)
    assert (n0, n1) == (E['n0'], E['n1']), 'fiber size disagrees with the manifest'
    assert sorted(comp(x) for x in S0) == sorted(S1), 'fibers not complementary'
    lo = lower_bounds(S0, S1)
    rec, top = reciprocal(S0, S1)
    got = choose(rec, lo, n0)
    if got is None:
        return None
    _, A, B, C = got
    tri = [A, B, C]
    pairs = [(A, B), (A, C), (B, C)]
    zall = sorted({z for p in pairs for z, _ in rec[p][2]})
    masks = sorted({rec[p][0] for p in pairs})
    zname = {z: 'w%d' % r for r, z in enumerate(zall)}
    mname = {m: 'ef%d' % r for r, m in enumerate(masks)}
    allv = (' '.join('q%d' % r for r in range(n0)) + ' '
            + ' '.join('r%d' % r for r in range(n1)))
    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('import SixQubit.Triangle')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit %d' % oid)
    W('')
    W('Orbit %d of `six_qubit_sslp.tex`: q = %d, angle vector' % (oid, q))
    W('a = (%s).  The projective order is m = %d, so the residue that has to be'
      % (', '.join(map(str, a)), E['m']))
    W('excluded is delta = q/m = %d: `S0` is the residue-0 fiber and `S1` the' % d)
    W('residue-%d fiber, and the two are complementary.' % d)
    W('')
    W('The moment polytope is positive dimensional here, so the probabilities')
    W('are not individually pinned.  What the exact linear program does give is')
    W('a uniform positive lower bound on three of them,')
    W('  q%d >= %s,   q%d >= %s,   q%d >= %s,'
      % (A, lo[A], B, lo[B], C, lo[C]))
    W('valid at every point of the polytope; `linarith` reproves each bound from')
    W('the moment rows and nonnegativity.  Each of the three pairs carries a')
    W('reciprocal flip relation, so')
    W('`SixQubit.Triangle.contradiction_of_normSq` closes the odd triangle')
    W('without any division.')
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
    for r, x in enumerate(S0):
        W(bsline('y%d' % r, x))
    W('')
    for r, y in enumerate(S1):
        W(bsline('z%d' % r, y))
    W('')
    W('def S0 : Finset (SS.BitString 6) := {%s}'
      % ', '.join('y%d' % r for r in range(n0)))
    W('def S1 : Finset (SS.BitString 6) := {%s}'
      % ', '.join('z%d' % r for r in range(n1)))
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
    W('/-! ## Flip masks, incidences and signs -/')
    W('')
    for m in masks:
        W(bsline(mname[m], m))
    for z in zall:
        W(bsline(zname[z], z))
    W('')
    for m in masks:
        inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        W('theorem incidence_%s :' % mname[m])
        W('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
          % (mname[m], ', '.join('z%d' % t for _, t in inc)))
        for i2, t2 in inc:
            W('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide'
              % (mname[m], t2, t2, mname[m], i2))
        for z in zall:
            if z not in {zz for p in pairs if rec[p][0] == m for zz, _ in rec[p][2]}:
                continue
            for _, t2 in inc:
                W('theorem sg_%s_%s_%d : SS.bdot %s z%d = %s := by decide'
                  % (mname[m], zname[z], t2, zname[z], t2,
                     'true' if dot(z, S1[t2]) else 'false'))
        W('')
    W('/-! ## The moment system -/')
    W('')
    W('/-- The two normalizations, the twenty-one moment equalities, and the')
    W('nonnegativity of every probability. -/')
    W('structure MomentSystem (%s : Real) : Prop where' % allv)
    W('  n0 : %s = 1' % ' + '.join('q%d' % r for r in range(n0)))
    W('  n1 : %s = 1' % ' + '.join('r%d' % r for r in range(n1)))
    for T in IDX:
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
    fields = (['n0', 'n1'] + ['m%s' % ''.join(str(j + 1) for j in T) for T in IDX]
              + ['nq%d' % r for r in range(n0)] + ['nr%d' % r for r in range(n1)])
    W('/-- Each triangle vertex is bounded away from zero over the whole moment')
    W('polytope, and the top probability at the complementary string matches. -/')
    W('theorem MomentSystem.facts {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    parts = ['(%s : Real) <= q%d' % (lo[k], k) for k in tri] \
        + ['q%d = r%d' % (k, top[k]) for k in tri]
    W('    ' + ' /\\ '.join(parts) + ' := by')
    W('  obtain <' + ', '.join(fields) + '> := h')
    W('  refine <' + ', '.join('?_' for _ in parts) + '> <;> linarith')
    W('')
    W('/-- The three triangle probabilities, bounded below by the linear program. -/')
    W('theorem MomentSystem.endpoints {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    W('    ' + ' /\\ '.join('(%s : Real) <= q%d' % (lo[k], k) for k in tri) + ' := by')
    W('  obtain <' + ', '.join(['e%d' % k for k in tri] + ['_', '_', '_'])
      + '> := h.facts')
    W('  exact ⟨' + ', '.join('e%d' % k for k in tri) + '⟩')
    W('')
    W('/-- Hence all three are strictly positive. -/')
    W('theorem MomentSystem.endpoints_pos {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    W('    ' + ' /\\ '.join('0 < q%d' % k for k in tri) + ' := by')
    W('  obtain <' + ', '.join('e%d' % k for k in tri) + '> := h.endpoints')
    W('  refine <?_, ?_, ?_> <;> linarith')
    W('')
    W('/-! ## The reciprocal relations -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    exdone = set()
    for p in pairs:
        m, inc, used, i1, t1, i2, t2 = rec[p]
        for z, _ in used:
            if (m, z) in exdone:
                continue
            exdone.add((m, z))
            body = ' '.join('%s star (c y%d) * d z%d'
                            % ('-' if dot(z, S1[t]) else '+', i, t)
                            for i, t in inc).lstrip('+ ')
            W('theorem ex_%s_%s (c d : SS.BitString 6 -> ℂ) :' % (mname[m], zname[z]))
            W('    offSum c d %s %s = %s := by' % (mname[m], zname[z], body))
            W('  unfold offSum')
            W('  rw [incidence_%s]' % mname[m])
            W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(inc) - 1))
              + (', ' if len(inc) > 1 else '') + 'Finset.sum_singleton]')
            W('  rw [' + ', '.join('flip_%s_%d' % (mname[m], t) for _, t in inc) + ']')
            lem = ['sg_%s_%s_%d' % (mname[m], zname[z], t) for _, t in inc]
            if any(dot(z, S1[t]) for _, t in inc):
                lem.append('SixQubit.signMul_true')
            if any(not dot(z, S1[t]) for _, t in inc):
                lem.append('SixQubit.signMul_false')
            W('  simp only [' + ', '.join(lem) + ']')
            W('  try ring')
            W('')
    W('/-! ## The no-go -/')
    W('')
    hypz = sorted({(rec[p][0], z) for p in pairs for z, _ in rec[p][2]})
    hsig = ''.join(' h%d' % r for r in range(len(hypz)))
    W('/-- The odd triangle eliminates to a single product, with no division and')
    W('no nonvanishing side condition on the way in. -/')
    W('theorem target_zero (c d : SS.BitString 6 -> ℂ)')
    for r, (m, z) in enumerate(hypz):
        W('    (h%d : offSum c d %s %s = 0) :' % (r, mname[m], zname[z])
          if r == len(hypz) - 1 else
          '    (h%d : offSum c d %s %s = 0)' % (r, mname[m], zname[z]))
    W('    star (c y%d) * d z%d * d z%d = 0 := by' % (C, top[A], top[B]))
    for r, (m, z) in enumerate(hypz):
        W('  rw [ex_%s_%s] at h%d' % (mname[m], zname[z], r))
    for (x, y) in pairs:
        m, inc, used, i1, t1, i2, t2 = rec[(x, y)]
        W('  have relo_%d_%d : star (c y%d) * d z%d + star (c y%d) * d z%d = 0 := by'
          % (x, y, x, top[y], y, top[x]))
        W('    linear_combination ' + ' + '.join(
            '(%s : ℂ) * h%d' % (mu, hypz.index((m, z))) for z, mu in used))
    W('  exact SixQubit.Triangle.prod_eq_zero relo_%d_%d relo_%d_%d relo_%d_%d'
      % (A, B, A, C, B, C))
    W('')
    W('/-- **Orbit %d is impossible.** -/' % oid)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
    for r, (m, z) in enumerate(hypz):
        W('    (h%d : offSum c d %s %s = 0)' % (r, mname[m], zname[z]))
    W('    : False := by')
    W('  have key := target_zero c d' + hsig)
    W('  obtain <' + ', '.join(['_b%d' % k for k in tri]
                               + [('mt%d' if k in (A, B) else '_mt%d') % k
                                  for k in tri]) + '> := hm.facts')
    W('  obtain <' + ', '.join('pos%d' % k for k in tri) + '> := hm.endpoints_pos')
    for k in (A, B):
        W('  have post%d : 0 < Complex.normSq (d z%d) := by rw [<- mt%d]; exact pos%d'
          % (k, top[k], k, k))
    W('  rcases mul_eq_zero.mp key with hx | hx')
    W('  · rcases mul_eq_zero.mp hx with hy | hy')
    W('    · have hk : c y%d = 0 := by simpa using congrArg star hy' % C)
    W('      rw [hk, Complex.normSq_zero] at pos%d' % C)
    W('      norm_num at pos%d' % C)
    W('    · rw [hy, Complex.normSq_zero] at post%d' % A)
    W('      norm_num at post%d' % A)
    W('  · rw [hx, Complex.normSq_zero] at post%d' % B)
    W('    norm_num at post%d' % B)
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % oid)
    src = NL.join(L) + NL
    return (src.replace(' /\\ ', ' ∧ ').replace('obtain <', 'obtain ⟨')
            .replace('refine <', 'refine ⟨').replace('> := h', '⟩ := h')
            .replace('> <;> linarith', '⟩ <;> linarith')
            .replace('<= q', '≤ q').replace('rw [<- mt', 'rw [← mt'))


if __name__ == '__main__':
    for o in sys.argv[1:]:
        src = emit(int(o))
        if src is None:
            print('orbit %s : no LP-bounded triangle' % o)
            continue
        p = os.path.join(REPO, 'SixQubit', 'Orbit%s.lean' % o)
        io.open(p, 'w', encoding='utf-8').write(src)
        print('%s : %d lines' % (p, src.count(NL)))
