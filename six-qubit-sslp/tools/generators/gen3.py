"""Phase 3 generator: orbits closed by an odd triangle of reciprocal flip
relations, on complementary fibers.

One vertex of the triangle may be supplied by a disjunction "at least one of
this set is active", which the moment system provides as a positive shell sum.
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
comp = lambda s: ''.join('01'[1 - int(c)] for c in s)
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]
bsline = lambda nm, s: 'def %s : SS.BitString 6 := bs %s  -- %s' % (
    nm, ' '.join(BOOL[c] for c in s), s)


def analyse(q, a, d):
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    n0, n1 = len(S0), len(S1)
    assert sorted(comp(x) for x in S0) == sorted(S1), 'fibers not complementary'
    top = {r: S1.index(comp(S0[r])) for r in range(n0)}   # bottom idx -> top idx
    idx = [(i,) for i in range(6)] + list(combinations(range(6), 2))
    rows, rhs = [[1] * n0 + [0] * n1, [0] * n0 + [1] * n1], [1, 1]
    for T in idx:
        rows.append([1 if all(S0[r][j] == '1' for j in T) else 0 for r in range(n0)]
                    + [-1 if all(S1[r][j] == '1' for j in T) else 0 for r in range(n1)])
        rhs.append(0)
    v = sp.Matrix(sp.symbols('t0:%d' % (n0 + n1)))
    sol = sp.solve([sp.Eq(x, y) for x, y in
                    zip(sp.Matrix(rows) * v, sp.Matrix(rhs))], list(v), dict=True)[0]
    expr = [sp.expand(sol.get(v[k], v[k])) for k in range(n0 + n1)]

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
            tgt = sp.Matrix([1 if r == k1 else (1 if r == k2 else 0)
                             for r in range(len(inc))])
            try:
                mu = W.T.gauss_jordan_solve(tgt)[0]
            except ValueError:
                continue
            mu = mu.subs({s: 0 for s in mu.free_symbols})
            used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z)) if mu[r] != 0]
            key = (min(i1, i2), max(i1, i2))
            if key not in rec or len(used) < len(rec[key][2]):
                rec[key] = (e, inc, used, i1, t1, i2, t2)
    return S0, S1, top, expr, rec, idx


def pick(expr, rec, n0):
    """Two forced-positive anchors plus a disjunction set completing a triangle."""
    posc = [k for k in range(n0) if expr[k].is_number and expr[k] > 0]
    for a1, b1 in combinations(posc, 2):
        if (min(a1, b1), max(a1, b1)) not in rec:
            continue
        cand = [k for k in range(n0) if k not in (a1, b1)
                and (min(a1, k), max(a1, k)) in rec
                and (min(b1, k), max(b1, k)) in rec]
        if not cand:
            continue
        for r in range(1, min(4, len(cand)) + 1):
            for sub in combinations(cand, r):
                tot = sp.simplify(sum(expr[k] for k in sub))
                if tot.is_number and tot > 0:
                    return a1, b1, list(sub), tot
    return None


def emit(oid, q, a, d):
    S0, S1, top, expr, rec, idx = analyse(q, a, d)
    n0, n1 = len(S0), len(S1)
    got = pick(expr, rec, n0)
    if got is None:
        return None
    A, B, KS, tot = got
    pairs = [(min(A, B), max(A, B))]
    for k in KS:
        pairs += [(min(A, k), max(A, k)), (min(B, k), max(B, k))]
    pairs = sorted(set(pairs))
    zall = sorted({z for p in pairs for z, _ in rec[p][2]})
    masks = sorted({rec[p][0] for p in pairs})
    zname = {z: 'w%d' % r for r, z in enumerate(zall)}
    mname = {m: 'ef%d' % r for r, m in enumerate(masks)}
    qs = ' '.join('q%d' % r for r in range(n0))
    rs = ' '.join('r%d' % r for r in range(n1))
    allv = qs + ' ' + rs
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
    W('a = (%s), residues 0 and %d.  The two fibers are complementary.' % (', '.join(map(str, a)), d))
    W('')
    W('Indices %d and %d have probability forced positive, and the moment system' % (A, B))
    W('gives the shell mass %s on {%s}, so at least one of those is active too.'
      % (tot, ', '.join(map(str, KS))))
    W('Each of the three pairs carries a reciprocal flip relation, and')
    W('`SixQubit.Triangle.contradiction_of_normSq` closes the resulting odd')
    W('triangle without any division.')
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
    need = sorted(set([A, B] + KS))
    W('/-- The anchors are pinned, the top matches the bottom, and the shell mass')
    W('on the disjunction set is positive. -/')
    W('theorem MomentSystem.facts {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
    parts = ['q%d = %s' % (A, expr[A]), 'q%d = %s' % (B, expr[B])]
    for k in need:
        parts.append('q%d = r%d' % (k, top[k]))
    parts.append('%s = %s' % (' + '.join('q%d' % k for k in KS), tot))
    W('    ' + ' ∧ '.join(parts) + ' := by')
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  refine ⟨' + ', '.join('?_' for _ in parts) + '⟩ <;> linarith')
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
    W('/-- **Orbit %d is impossible.** -/' % oid)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
    for r, (m, z) in enumerate(hypz):
        W('    (h%d : offSum c d %s %s = 0)' % (r, mname[m], zname[z]))
    W('    : False := by')
    for r, (m, z) in enumerate(hypz):
        W('  rw [ex_%s_%s] at h%d' % (mname[m], zname[z], r))
    need_or = [(A, B)] + [(A, k) for k in KS] + [(B, k) for k in KS]
    for (x, y) in need_or:
        m, inc, used, i1, t1, i2, t2 = rec[(min(x, y), max(x, y))]
        W('  have relo_%d_%d : star (c y%d) * d z%d + star (c y%d) * d z%d = 0 := by'
          % (x, y, x, top[y], y, top[x]))
        W('    linear_combination ' + ' + '.join(
            '(%s : ℂ) * h%d' % (mu, hypz.index((m, z))) for z, mu in used))
    W('  obtain ⟨' + ', '.join(['fA', 'fB']
                               + ['mt%d' % k for k in need]
                               + ['fs']) + '⟩ := hm.facts')
    for nm, k in (('fA', A), ('fB', B)):
        W('  have pos%d : 0 < Complex.normSq (c y%d) := by rw [%s]; norm_num' % (k, k, nm))
        W('  have post%d : 0 < Complex.normSq (d z%d) := by rw [← mt%d]; exact pos%d'
          % (k, top[k], k, k))
    W('  have alt : ' + ' ∨ '.join('0 < Complex.normSq (c y%d)' % k for k in KS) + ' := by')
    W('    by_contra hcon')
    W('    push_neg at hcon')
    W('    obtain ⟨' + ', '.join('a%d' % j for j in range(len(KS))) + '⟩ := hcon')
    for k in KS:
        W('    have nn%d := Complex.normSq_nonneg (c y%d)' % (k, k))
    W('    linarith')
    W('  rcases alt with ' + ' | '.join('hk%d' % k for k in KS))
    for k in KS:
        W('  · have postk : 0 < Complex.normSq (d z%d) := by rw [← mt%d]; exact hk%d'
          % (top[k], k, k))
        # triangle on (A, B, k): h1 = pair(A,B), h2 = pair(A,k), h3 = pair(B,k)
        W('    exact SixQubit.Triangle.contradiction_of_normSq relo_%d_%d relo_%d_%d '
          'relo_%d_%d hk%d post%d post%d' % (A, B, A, k, B, k, k, A, B))
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % oid)
    return NL.join(L) + NL


ORB = {50: (6, [1, 1, 1, 3, 4, 4], 2), 49: (6, [1, 1, 1, 3, 3, 5], 2),
       51: (6, [1, 1, 2, 3, 3, 4], 2), 17: (4, [1, 1, 1, 1, 1, 1], 2)}
if __name__ == '__main__':
    for o in sys.argv[1:]:
        o = int(o)
        src = emit(o, *ORB[o])
        if src is None:
            print('orbit %d : no triangle certificate' % o)
            continue
        io.open('Orbit%d.lean' % o, 'w', encoding='utf-8').write(src)
        print('Orbit%d.lean : %d lines' % (o, src.count(NL)))
