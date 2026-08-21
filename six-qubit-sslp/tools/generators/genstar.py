"""Star + pair-triangle generator.

Some orbits carry no isolable monomial and no odd triangle of reciprocal
relations, yet still close by the following two-stage mechanism (the one the
paper uses for orbit 55).

  * One bottom index `K` has a probability the moment polytope bounds away
    from zero, and it is joined to a set `L` of leaves by two-incidence flip
    masks.  Each such mask gives a *reciprocal* relation

        star(c_i) * d_{K'} + star(c_K) * d_{i'} = 0 ,      i in L,

    where `x'` denotes the complementary top string.

  * Three further masks each carry a four-edge relation supported on two
    reciprocal pairs inside `L`.  Multiplying such a relation by `star(c_K)`
    and substituting the six-star relations collapses it, with no division, to

        (X_a X_b + s X_c X_d) * d_{K'} = 0 ,      X_i := star(c_i),

    and `d_{K'}` is nonzero because the polytope bounds its probability below.

If the three binomials line up as `a f + b e`, `c f + d e`, `a d + b c` then
`SixQubit.Triangle.pair_contradiction` finishes, provided `X_b, X_c, X_e` are
nonzero.  That last point is decided by the two magnitude consequences of the
binomials together with five exact LP lower bounds on sums of probabilities;
the generator checks all five are strictly positive before emitting anything.

q, a and the residue delta = q/m always come from `tools/manifest.json`.

    python tools/run.py generators/genstar.py 55
"""
import io
import json
import os
import sys
from fractions import Fraction as F
from itertools import combinations, permutations

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from orbit import fiber
from lpbound import lower_bounds, functional_bound

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


def solve(W, tgt):
    try:
        mu = W.T.gauss_jordan_solve(sp.Matrix(tgt))[0]
    except ValueError:
        return None
    return mu.subs({s: 0 for s in mu.free_symbols})


def structure(S0, S1):
    """Two-incidence reciprocal relations and four-edge relations."""
    n0 = len(S0)
    top = {r: S1.index(comp(S0[r])) for r in range(n0)}
    star, quad = {}, []
    for e in ALL:
        if not 1 <= len(supp(e)) <= 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        if not inc:
            continue
        Z = dress(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        rp = []
        for k1, k2 in combinations(range(len(inc)), 2):
            i1, t1 = inc[k1]
            i2, t2 = inc[k2]
            if top[i1] == t2 and top[i2] == t1:
                rp.append((k1, k2, i1, i2))
        for (k1, k2, i1, i2) in rp:
            tgt = [0] * len(inc)
            tgt[k1] = tgt[k2] = 1
            mu = solve(W, tgt)
            if mu is None:
                continue
            used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z)) if mu[r] != 0]
            key = (min(i1, i2), max(i1, i2))
            if key not in star or len(used) < len(star[key][2]):
                star[key] = (e, inc, used)
        for (k1, k2, i1, i2), (k3, k4, i3, i4) in combinations(rp, 2):
            for s in (1, -1):
                tgt = [0] * len(inc)
                tgt[k1] = tgt[k2] = 1
                tgt[k3] = tgt[k4] = s
                mu = solve(W, tgt)
                if mu is None:
                    continue
                used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z)) if mu[r] != 0]
                quad.append((e, inc, used, (i1, i2), (i3, i4), s))
    return star, quad, top


def pick(S0, S1, star, quad, top, lo):
    """Choose the star centre and the pair-triangle.

    A four-edge relation with sign +1 on two reciprocal pairs {p,q}, {u,v}
    collapses to the binomial  X_p X_q + X_u X_v = 0 .  `pair_contradiction`
    wants three binomials of the shape

        a f + b e ,     c f + d e ,     a d + b c ,

    so six distinct leaves are searched for directly.
    """
    n0 = len(S0)
    nb = {k: set() for k in range(n0)}
    for (i, j) in star:
        nb[i].add(j)
        nb[j].add(i)
    key = lambda P, Q: frozenset([frozenset(P), frozenset(Q)])
    for K in sorted(range(n0), key=lambda k: -len(nb[k])):
        if lo[n0 + top[K]] <= 0:
            continue
        L = sorted(nb[K])
        bino = {}
        for e, inc, used, P, Q, s in quad:
            if s != 1 or not set(P) | set(Q) <= set(L):
                continue
            k = key(P, Q)
            if k not in bino or len(used) < len(bino[k][2]):
                bino[k] = (e, inc, used, P, Q, s)
        for a, b, c, d, ee, f in permutations(L, 6):
            k1, k2, k3 = key((a, f), (b, ee)), key((c, f), (d, ee)), key((a, d), (b, c))
            if len({k1, k2, k3}) != 3:
                continue
            if not (k1 in bino and k2 in bino and k3 in bino):
                continue
            cert = certificates(S0, S1, a, b, c, d, ee, f)
            if cert is None:
                continue
            return K, (a, b, c, d, ee, f), (bino[k1], bino[k2], bino[k3]), cert
    return None


def certificates(S0, S1, a, b, c, d, e, f):
    """The five LP lower bounds the positivity chain needs, all > 0."""
    n0, n1 = len(S0), len(S1)
    def vec(ks):
        v = [F(0)] * (n0 + n1)
        for k in ks:
            v[k] = F(1)
        return v
    out = []
    for ks in [(a, b), (c, d), (e, f), (a, c, e), (b, d, f)]:
        val = functional_bound(S0, S1, vec(ks))
        if val <= 0:
            return None
        out.append((ks, val))
    return out


def emit(oid):
    E = MAN[str(oid)]
    q, a, d = E['q'], E['a'], E['d']
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    n0, n1 = len(S0), len(S1)
    assert (n0, n1) == (E['n0'], E['n1']), 'fiber size disagrees with the manifest'
    assert sorted(comp(x) for x in S0) == sorted(S1), 'fibers not complementary'
    lo = lower_bounds(S0, S1)
    star, quad, top = structure(S0, S1)
    got = pick(S0, S1, star, quad, top, lo)
    if got is None:
        return None
    K, (A, B, C, D, EE, FF), hs, cert = got
    leaves = sorted({A, B, C, D, EE, FF})
    kbound = lo[n0 + top[K]]

    masks, dressings = [], []
    for i in leaves:
        m, inc, used = star[(min(i, K), max(i, K))]
        masks.append(m)
        dressings += [z for z, _ in used]
    for h in hs:
        masks.append(h[0])
        dressings += [z for z, _ in h[2]]
    masks = sorted(set(masks))
    zall = sorted(set(dressings))
    mname = {m: 'ef%d' % r for r, m in enumerate(masks)}
    zname = {z: 'w%d' % r for r, z in enumerate(zall)}
    allv = (' '.join('q%d' % r for r in range(n0)) + ' '
            + ' '.join('r%d' % r for r in range(n1)))
    X = lambda i: 'star (c y%d)' % i

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
    W('a = (%s).  The projective order is m = %d, so the residue that has to'
      % (', '.join(map(str, a)), E['m']))
    W('be excluded is delta = q/m = %d: `S0` is the residue-0 fiber, `S1` the' % d)
    W('residue-%d fiber, and the two are complementary.' % d)
    W('')
    W('The moment polytope is positive dimensional and no monomial is isolable,')
    W('so the argument runs in two stages.')
    W('')
    W('* Index %d is joined to %s by two-incidence flip masks; each gives a'
      % (K, ', '.join(str(i) for i in leaves)))
    W('  reciprocal relation pairing that leaf with the centre.')
    W('* Three further masks carry a four-edge relation supported on two')
    W('  reciprocal pairs of leaves.  Multiplying by `star (c y%d)` and' % K)
    W('  substituting the star relations collapses each one, without dividing,')
    W('  to a binomial times `d z%d`, and `d z%d` is nonzero because the moment'
      % (top[K], top[K]))
    W('  polytope forces `%s <= r%d`.' % (kbound, top[K]))
    W('')
    W('The three binomials are the hypotheses of')
    W('`SixQubit.Triangle.pair_contradiction`; the two magnitude consequences')
    W('and five exact LP bounds rule out every boundary escape in which one of')
    W('the three amplitudes it needs would vanish.')
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
    need = {}
    for i in leaves:
        m, inc, used = star[(min(i, K), max(i, K))]
        need.setdefault(m, set()).update(z for z, _ in used)
    for h in hs:
        need.setdefault(h[0], set()).update(z for z, _ in h[2])
    for m in masks:
        inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        W('theorem incidence_%s :' % mname[m])
        W('    S1.filter (fun y => SS.bxor y %s ∈ S0) = {%s} := by decide'
          % (mname[m], ', '.join('z%d' % t for _, t in inc)))
        for i2, t2 in inc:
            W('theorem flip_%s_%d : SS.bxor z%d %s = y%d := by decide'
              % (mname[m], t2, t2, mname[m], i2))
        for z in sorted(need[m]):
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
    W('/-- The exact linear program bounds the six sums below away from zero,')
    W('uniformly over the moment polytope. -/')
    W('theorem MomentSystem.facts {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    parts = ['(%s : Real) ≤ r%d' % (kbound, top[K])]
    parts += ['(%s : Real) ≤ %s' % (val, ' + '.join('q%d' % k for k in ks))
              for ks, val in cert]
    W('    ' + ' ∧ '.join(parts) + ' := by')
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  refine ⟨' + ', '.join('?_' for _ in parts) + '⟩ <;> linarith')
    W('')
    W('/-- The five pair and triple sums the boundary analysis needs, each bounded')
    W('below by the exact linear program. -/')
    W('theorem MomentSystem.endpoints {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    W('    ' + ' ∧ '.join('(%s : Real) ≤ %s' % (val, ' + '.join('q%d' % k for k in ks))
                          for ks, val in cert) + ' := by')
    W('  obtain ⟨_, c1, c2, c3, c4, c5⟩ := h.facts')
    W('  exact ⟨c1, c2, c3, c4, c5⟩')
    W('')
    W('/-- The top probability at the complement of the star centre is positive,')
    W('which is what makes the collapsed binomials cancellable. -/')
    W('theorem MomentSystem.endpoints_pos {%s : Real} (h : MomentSystem %s) :'
      % (allv, allv))
    W('    0 < r%d := by' % top[K])
    W('  obtain ⟨bK, _, _, _, _, _⟩ := h.facts')
    W('  linarith')
    W('')
    W('/-! ## The boundary analysis -/')
    W('')
    W('/-- With the two magnitude relations and the five polytope bounds, none of')
    W('the three amplitudes the pair triangle needs can vanish. -/')
    W('theorem positivity {qa qb qc qd qe qf : Real}')
    W('    (ha : 0 ≤ qa) (hb : 0 ≤ qb) (hc : 0 ≤ qc) (_hd : 0 ≤ qd)')
    W('    (he : 0 ≤ qe) (_hf : 0 ≤ qf)')
    W('    (L1 : (%s : Real) ≤ qa + qb)' % cert[0][1])
    W('    (L2 : (%s : Real) ≤ qc + qd)' % cert[1][1])
    W('    (L3 : (%s : Real) ≤ qe + qf)' % cert[2][1])
    W('    (L4 : (%s : Real) ≤ qa + qc + qe)' % cert[3][1])
    W('    (L5 : (%s : Real) ≤ qb + qd + qf)' % cert[4][1])
    W('    (mag1 : qa * qf = qb * qe)')
    W('    (mag2 : qa * qd = qb * qc) :')
    W('    0 < qb ∧ 0 < qc ∧ 0 < qe := by')
    W('  have hA : 0 < qa := by')
    W('    by_contra hcon')
    W('    push_neg at hcon')
    W('    have h0 : qa = 0 := le_antisymm hcon ha')
    W('    have hbp : 0 < qb := by linarith')
    W('    have h1 : qe = 0 := by')
    W('      have hz : qb * qe = 0 := by rw [← mag1, h0]; ring')
    W('      rcases mul_eq_zero.mp hz with hx | hx')
    W('      · linarith')
    W('      · exact hx')
    W('    have h2 : qc = 0 := by')
    W('      have hz : qb * qc = 0 := by rw [← mag2, h0]; ring')
    W('      rcases mul_eq_zero.mp hz with hx | hx')
    W('      · linarith')
    W('      · exact hx')
    W('    linarith')
    W('  refine ⟨?_, ?_, ?_⟩')
    W('  · by_contra hcon')
    W('    push_neg at hcon')
    W('    have h0 : qb = 0 := le_antisymm hcon hb')
    W('    have h1 : qf = 0 := by')
    W('      have hz : qa * qf = 0 := by rw [mag1, h0]; ring')
    W('      rcases mul_eq_zero.mp hz with hx | hx')
    W('      · linarith')
    W('      · exact hx')
    W('    have h2 : qd = 0 := by')
    W('      have hz : qa * qd = 0 := by rw [mag2, h0]; ring')
    W('      rcases mul_eq_zero.mp hz with hx | hx')
    W('      · linarith')
    W('      · exact hx')
    W('    linarith')
    W('  · by_contra hcon')
    W('    push_neg at hcon')
    W('    have h0 : qc = 0 := le_antisymm hcon hc')
    W('    have h1 : 0 < qd := by linarith')
    W('    have hz : qa * qd = 0 := by rw [mag2, h0]; ring')
    W('    rcases mul_eq_zero.mp hz with hx | hx')
    W('    · linarith')
    W('    · linarith')
    W('  · by_contra hcon')
    W('    push_neg at hcon')
    W('    have h0 : qe = 0 := le_antisymm hcon he')
    W('    have h1 : 0 < qf := by linarith')
    W('    have hz : qa * qf = 0 := by rw [mag1, h0]; ring')
    W('    rcases mul_eq_zero.mp hz with hx | hx')
    W('    · linarith')
    W('    · linarith')
    W('')
    W('/-! ## The Walsh expansions -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    exdone = []
    for m in masks:
        inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        for z in sorted(need[m]):
            exdone.append((m, z))
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
    W('/-! ## The collapsed binomials -/')
    W('')
    W('/-- Multiplying each four-edge relation by `star (c y%d)` and substituting' % K)
    W('the star relations collapses it to a binomial times `d z%d`. -/' % top[K])
    W('theorem target_zero (c d : SS.BitString 6 -> ℂ)')
    for r, (m, z) in enumerate(exdone):
        W('    (h%d : offSum c d %s %s = 0)%s'
          % (r, mname[m], zname[z], ' :' if r == len(exdone) - 1 else ''))
    tz = []
    for r, h in enumerate(hs):
        m, inc, used, (p1, p2), (u1, u2), s = h
        tz.append('(%s * %s %s %s * %s) * d z%d = 0'
                  % (X(p1), X(p2), '+' if s == 1 else '-', X(u1), X(u2), top[K]))
    W('    ' + (NL + '      ∧ ').join(tz) + ' := by')
    for r, (m, z) in enumerate(exdone):
        W('  rw [ex_%s_%s] at h%d' % (mname[m], zname[z], r))
    for i in leaves:
        m, inc, used = star[(min(i, K), max(i, K))]
        W('  have s%d : %s * d z%d + %s * d z%d = 0 := by'
          % (i, X(i), top[K], X(K), top[i]))
        W('    linear_combination ' + ' + '.join(
            '(%s : ℂ) * h%d' % (mu, exdone.index((m, z))) for z, mu in used))
    names = {}
    for r, h in enumerate(hs):
        m, inc, used, (p1, p2), (u1, u2), s = h
        W('  have R%d : %s * d z%d + %s * d z%d %s %s * d z%d %s %s * d z%d = 0 := by'
          % (r, X(p1), top[p2], X(p2), top[p1],
             '+' if s == 1 else '-', X(u1), top[u2],
             '+' if s == 1 else '-', X(u2), top[u1]))
        W('    linear_combination ' + ' + '.join(
            '(%s : ℂ) * h%d' % (mu, exdone.index((m, z))) for z, mu in used))
        W('  have g%d : (%s * %s %s %s * %s) * d z%d = 0 := by'
          % (r, X(p1), X(p2), '+' if s == 1 else '-', X(u1), X(u2), top[K]))
        W('    linear_combination (%s / 2 : ℂ) * s%d + (%s / 2 : ℂ) * s%d '
          '+ (%s%s / 2 : ℂ) * s%d + (%s%s / 2 : ℂ) * s%d - (%s / 2 : ℂ) * R%d'
          % (X(p1), p2, X(p2), p1,
             '' if s == 1 else '-', X(u1), u2, '' if s == 1 else '-', X(u2), u1,
             X(K), r))
        names[r] = (p1, p2, u1, u2, s)
    W('  exact ⟨g0, g1, g2⟩')
    W('')
    W('/-! ## The no-go -/')
    W('')
    W('/-- **Orbit %d is impossible.** -/' % oid)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
    for r, (m, z) in enumerate(exdone):
        W('    (h%d : offSum c d %s %s = 0)' % (r, mname[m], zname[z]))
    W('    : False := by')
    W('  obtain ⟨g0, g1, g2⟩ := target_zero c d'
      + ''.join(' h%d' % r for r in range(len(exdone))))
    W('  obtain ⟨bK, c1, c2, c3, c4, c5⟩ := hm.facts')
    W('  have hzK : d z%d ≠ 0 := by' % top[K])
    W('    intro hzero')
    W('    rw [hzero] at bK')
    W('    simp only [Complex.normSq_zero] at bK')
    W('    linarith')
    for r, (u, v, w, x) in enumerate([(A, FF, B, EE), (C, FF, D, EE), (A, D, B, C)]):
        W('  have b%d : %s * %s + %s * %s = 0 := by' % (r, X(u), X(v), X(w), X(x)))
        W('    rcases mul_eq_zero.mp g%d with hx | hx' % r)
        W('    · linear_combination hx')
        W('    · exact absurd hx hzK')
    W('  have mag1 : Complex.normSq (c y%d) * Complex.normSq (c y%d)' % (A, FF))
    W('      = Complex.normSq (c y%d) * Complex.normSq (c y%d) := by' % (B, EE))
    W('    have hx : %s * %s = -(%s * %s) := by linear_combination b0'
      % (X(A), X(FF), X(B), X(EE)))
    W('    have hy := congrArg Complex.normSq hx')
    W('    simpa [Complex.normSq_mul] using hy')
    W('  have mag2 : Complex.normSq (c y%d) * Complex.normSq (c y%d)' % (A, D))
    W('      = Complex.normSq (c y%d) * Complex.normSq (c y%d) := by' % (B, C))
    W('    have hx : %s * %s = -(%s * %s) := by linear_combination b2'
      % (X(A), X(D), X(B), X(C)))
    W('    have hy := congrArg Complex.normSq hx')
    W('    simpa [Complex.normSq_mul] using hy')
    W('  obtain ⟨pb, pc, pe⟩ := positivity (Complex.normSq_nonneg (c y%d))' % A)
    W('    (Complex.normSq_nonneg (c y%d)) (Complex.normSq_nonneg (c y%d))' % (B, C))
    W('    (Complex.normSq_nonneg (c y%d)) (Complex.normSq_nonneg (c y%d))' % (D, EE))
    W('    (Complex.normSq_nonneg (c y%d)) c1 c2 c3 c4 c5 mag1 mag2' % FF)
    for nm, k in (('nb', B), ('nc', C), ('ne', EE)):
        W('  have %s : %s ≠ 0 := by' % (nm, X(k)))
        W('    intro hzero')
        W('    have hk : c y%d = 0 := by simpa using congrArg star hzero' % k)
        W('    rw [hk] at p%s' % nm[1])
        W('    simp at p%s' % nm[1])
    W('  exact SixQubit.Triangle.pair_contradiction b0 b1 b2 nb nc ne')
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % oid)
    return NL.join(L) + NL


if __name__ == '__main__':
    for o in sys.argv[1:]:
        src = emit(int(o))
        if src is None:
            print('orbit %s : no star / pair-triangle certificate' % o)
            continue
        p = os.path.join(REPO, 'SixQubit', 'Orbit%s.lean' % o)
        io.open(p, 'w', encoding='utf-8').write(src)
        print('%s : %d lines' % (p, src.count(NL)))
