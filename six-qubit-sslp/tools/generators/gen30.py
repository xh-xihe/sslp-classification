"""Generator for orbit 30 at the manifest residue delta = q/m = 1.

The residue-0 fiber has sixteen strings and is parametrised by
`x(u) = (u, t(wt u))` for `u` in `F_2^4`, with `t(0) = t(4) = 00`,
`t(1) = 01`, `t(2) = 10`, `t(3) = 11`.  One string is the distinguished
`star = x(1111)`, five are the *points* `v_i`, and ten are the *edges*
`e_ij` of `K_5`; the residue-1 fiber is the complementary set.

Writing `u p = star (c y_p)`, `v q = d z_(top q)`, `a = u star`,
`s = v star`, the ten admissible flip masks reduce, by exact Walsh row
reduction, to

  * `R_i`   :  a * v(v_i) + u(v_i) * s = 0                     (weight two),
  * `D_ij`  :  u(v_j) * v(e_ij) = u(e_ij) * v(v_j)             (weight one),
  * `T_i`   :  sum_{j != i} u(v_j) * v(e_ij) = 0               (weight one),
  * `M_i`   :  the all-plus sum over the three perfect matchings of
               `V \\ {i}` of the two edge-edge monomials         (weight two).

Setting `k_ij = a * v(e_ij) + u(e_ij) * s`, these give `b_p * k_ij = 0` for
both endpoints of every edge, `s * (C b)_i = 0` hence `C b = 0`, and an
identity whose right-hand side is `2 s H_i`.  Together with the exact moment
data (`p_star = 1/8`, `deg_i = |b_i|^2 + 1/8`, total point mass `3/8`, total
edge mass `1/2`) that is exactly `SixQubit.K5.Sys`, which is contradictory.

    python tools/run.py generators/gen30.py
"""
import io
import json
import os
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from orbit import fiber

NL = chr(10)
OID = 30
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
VV = list(range(5))
EE = list(combinations(VV, 2))
key = lambda i, j: (min(i, j), max(i, j))
TT = {0: '00', 4: '00', 1: '01', 2: '10', 3: '11'}
BIT = {0: 0b0000, 1: 0b0001, 2: 0b0010, 3: 0b0100, 4: 0b1000}


def xstr(u):
    s = format(u, '04b')
    return s + TT[s.count('1')]


def haf(i):
    j, k, l, m = [v for v in VV if v != i]
    return [(key(j, k), key(l, m)), (key(j, l), key(k, m)), (key(j, m), key(k, l))]


def build():
    E = MAN[str(OID)]
    S0, S1 = fiber(E['a'], E['q'], 0), fiber(E['a'], E['q'], E['d'])
    assert (len(S0), len(S1)) == (E['n0'], E['n1'])
    top = {r: S1.index(comp(S0[r])) for r in range(len(S0))}
    star = S0.index(xstr(0b1111))
    vtx = {i: S0.index(xstr(BIT[i])) for i in VV}
    edge = {e: S0.index(xstr(0b1111 ^ BIT[e[0]] ^ BIT[e[1]])) for e in EE}

    mono = {}
    for m in ALL:
        if not 1 <= len(supp(m)) <= 2:
            continue
        inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        if not inc:
            continue
        mono[m] = [(p, S0.index(comp(S1[t])), t) for p, t in inc]

    # identify the masks
    F, G = {}, {}
    for m, mon in mono.items():
        pairs = {(p, q) for p, q, _ in mon}
        for i in VV:
            if (star, vtx[i]) in pairs and (vtx[i], star) in pairs:
                G[i] = m
            if all((vtx[j], edge[key(i, j)]) in pairs for j in VV if j != i):
                F[i] = m
    assert len(F) == 5 and len(G) == 5, (sorted(F), sorted(G))

    rel = {}

    def row(name, m, tgt):
        mon = mono[m]
        pos = {(p, q): r for r, (p, q, _) in enumerate(mon)}
        vec = [0] * len(mon)
        for (p, q), cf in tgt.items():
            vec[pos[(p, q)]] = cf
        Z = dress(m)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, _, t in mon] for z in Z])
        mu = W.T.gauss_jordan_solve(sp.Matrix(vec))[0]
        mu = mu.subs({s: 0 for s in mu.free_symbols})
        used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z)) if mu[r] != 0]
        rel[name] = (m, mon, used, tgt)

    for i in VV:
        for j in VV:
            if j == i:
                continue
            row('D%d_%d' % (i, j), F[i],
                {(vtx[j], edge[key(i, j)]): 1, (edge[key(i, j)], vtx[j]): -1})
        row('T%d' % i, F[i],
            {(vtx[j], edge[key(i, j)]): 1 for j in VV if j != i})
        row('R%d' % i, G[i], {(star, vtx[i]): 1, (vtx[i], star): 1})
        tgt = {}
        for t in haf(i):
            tgt[(edge[t[0]], edge[t[1]])] = 1
            tgt[(edge[t[1]], edge[t[0]])] = 1
        row('M%d' % i, G[i], tgt)
    return E, S0, S1, top, star, vtx, edge, rel


def emit():
    E, S0, S1, top, star, vtx, edge, rel = build()
    q, a, d = E['q'], E['a'], E['d']
    n0, n1 = len(S0), len(S1)
    names = sorted(rel)
    masks = sorted({rel[k][0] for k in names})
    need = {}
    for k in names:
        m, mon, used, tgt = rel[k]
        need.setdefault(m, set()).update(z for z, _ in used)
    zall = sorted({z for m in need for z in need[m]})
    mname = {m: 'ef%d' % r for r, m in enumerate(masks)}
    zname = {z: 'w%d' % r for r, z in enumerate(zall)}
    hyp = []
    for m in masks:
        for z in sorted(need[m]):
            hyp.append((m, z))
    allv = (' '.join('q%d' % r for r in range(n0)) + ' '
            + ' '.join('r%d' % r for r in range(n1)))
    U = lambda p: 'star (c y%d)' % p
    Vv = lambda p: 'd z%d' % top[p]
    A = U(star)
    S = Vv(star)
    B = lambda i: U(vtx[i])
    C = lambda e: U(edge[e])
    K = lambda e: '(%s * %s + %s * %s)' % (A, Vv(edge[e]), C(e), S)
    P = lambda p: 'Complex.normSq (c y%d)' % p

    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('import SixQubit.K5')
    W('')
    W('/-!')
    W('# Six-qubit no-go for moment orbit %d' % OID)
    W('')
    W('Orbit %d of `six_qubit_sslp.tex`: q = %d, angle vector' % (OID, q))
    W('a = (%s).  The projective order is m = %d, so the residue that has to'
      % (', '.join(map(str, a)), E['m']))
    W('be excluded is delta = q/m = %d: `S0` is the residue-0 fiber, `S1` the' % d)
    W('residue-%d fiber, and the two are complementary.' % d)
    W('')
    for line in __doc__.strip().split(NL)[1:-2]:
        W(line)
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
    inc_of = {}
    for m in masks:
        inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        inc_of[m] = inc
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
    facts = (['q%d = 1/8' % star, 'r%d = q%d' % (top[star], star)]
             + ['%s = q%d + 1/8'
                % (' + '.join('q%d' % edge[key(i, j)] for j in VV if j != i), vtx[i])
                for i in VV]
             + ['%s = 3/8' % ' + '.join('q%d' % vtx[i] for i in VV),
                '%s = 1/2' % ' + '.join('q%d' % edge[e] for e in EE)])
    W('/-- The exact moment normal form on the `K_5` labelling. -/')
    W('theorem MomentSystem.endpoints {%s : Real} (h : MomentSystem %s) :'
      % (allv, allv))
    W('    ' + (NL + '      ∧ ').join(facts) + ' := by')
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  refine ⟨' + ', '.join('?_' for _ in facts) + '⟩ <;> linarith')
    W('')
    W('/-- The distinguished string is always active. -/')
    W('theorem MomentSystem.endpoints_pos {%s : Real} (h : MomentSystem %s) :'
      % (allv, allv))
    W('    0 < r%d := by' % top[star])
    W('  obtain ⟨e1, e2, _, _, _, _, _, _, _⟩ := h.endpoints')
    W('  linarith')
    W('')
    W('/-! ## The Walsh expansions -/')
    W('')
    W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
    W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
    W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
    W('')
    for m in masks:
        inc = inc_of[m]
        for z in sorted(need[m]):
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
    W('/-! ## The reduced Walsh rows -/')
    W('')
    stmts = []
    for k in names:
        m, mon, used, tgt = rel[k]
        body = ' '.join('%s %s * %s' % ('+' if cf > 0 else '-', U(p), Vv(qq))
                        for (p, qq), cf in tgt.items()).lstrip('+ ')
        stmts.append((k, body))
    hsig = ''.join(' h%d' % r for r in range(len(hyp)))
    W('/-- Exact row reduction of the admissible dressings of the ten flip masks. -/')
    W('theorem rows (c d : SS.BitString 6 -> ℂ)')
    for r, (m, z) in enumerate(hyp):
        W('    (h%d : offSum c d %s %s = 0)%s'
          % (r, mname[m], zname[z], ' :' if r == len(hyp) - 1 else ''))
    W('    ' + (NL + '      ∧ ').join('%s = 0' % b for _, b in stmts) + ' := by')
    for r, (m, z) in enumerate(hyp):
        W('  rw [ex_%s_%s] at h%d' % (mname[m], zname[z], r))
    for k, body in stmts:
        m, mon, used, tgt = rel[k]
        W('  have %s : %s = 0 := by' % (k, body))
        W('    linear_combination ' + ' + '.join(
            '(%s : ℂ) * h%d' % (mu, hyp.index((m, z))) for z, mu in used))
    W('  exact ⟨' + ', '.join(k for k, _ in stmts) + '⟩')
    W('')
    W('/-! ## The K_5 data -/')
    W('')
    W('/-- The reciprocal relations at the distinguished string turn every edge')
    W('phase defect into an annihilator of both endpoint amplitudes; the')
    W('weight-one sums then say `C b = 0`. -/')
    W('theorem target_zero (c d : SS.BitString 6 -> ℂ) (hs : %s ≠ 0)' % S)
    for r, (m, z) in enumerate(hyp):
        W('    (h%d : offSum c d %s %s = 0)%s'
          % (r, mname[m], zname[z], ' :' if r == len(hyp) - 1 else ''))
    sts = [' + '.join('%s * %s' % (B(j), C(key(i, j))) for j in VV if j != i)
           for i in VV]
    W('    ' + (NL + '      ∧ ').join('%s = 0' % x for x in sts) + ' := by')
    W('  obtain ⟨' + ', '.join(names) + '⟩ := rows c d' + hsig)
    for e in EE:
        for p in e:
            o = e[0] if e[1] == p else e[1]
            W('  have kb%d%d_%d : %s * %s = 0 := by'
              % (e[0], e[1], p, B(p), K(e)))
            W('    linear_combination (%s : ℂ) * D%d_%d + (%s : ℂ) * R%d'
              % (A, o, p, C(e), p))
    for i in VV:
        W('  have sx%d : %s * (%s) = 0 := by' % (i, S, sts[i]))
        W('    linear_combination ' + ' + '.join(
            'kb%d%d_%d' % (key(i, j)[0], key(i, j)[1], j) for j in VV if j != i)
          + ' - (%s : ℂ) * T%d' % (A, i))
    W('  refine ⟨' + ', '.join('?_' for _ in VV) + '⟩')
    for i in VV:
        W('  · rcases mul_eq_zero.mp sx%d with y | y' % i)
        W('    · exact absurd y hs')
        W('    · exact y')
    W('')
    W('/-! ## The no-go -/')
    W('')
    W('/-- **Orbit %d is impossible.** -/' % OID)
    W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
    W('    (hm : MomentSystem')
    W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
    W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
    for r, (m, z) in enumerate(hyp):
        W('    (h%d : offSum c d %s %s = 0)' % (r, mname[m], zname[z]))
    W('    : False := by')
    W('  obtain ⟨f1, f2, g0, g1, g2, g3, g4, ftb, ftc⟩ := hm.endpoints')
    W('  have hpos : (0:Real) < Complex.normSq (%s) := by' % S)
    W('    have := hm.endpoints_pos')
    W('    linarith')
    W('  have hs : %s ≠ 0 := by' % S)
    W('    intro hz')
    W('    rw [hz, Complex.normSq_zero] at hpos')
    W('    norm_num at hpos')
    W('  obtain ⟨' + ', '.join('st%d' % i for i in VV) + '⟩ := target_zero c d hs'
      + hsig)
    W('  obtain ⟨' + ', '.join(names) + '⟩ := rows c d' + hsig)
    W('  have nss : ∀ w : ℂ, Complex.normSq (star w) = Complex.normSq w :=')
    W('    fun w => by simp')
    for e in EE:
        for p in e:
            o = e[0] if e[1] == p else e[1]
            W('  have kb%d%d_%d : %s * %s = 0 := by'
              % (e[0], e[1], p, B(p), K(e)))
            W('    linear_combination (%s : ℂ) * D%d_%d + (%s : ℂ) * R%d'
              % (A, o, p, C(e), p))
    for i in VV:
        terms = []
        for t in haf(i):
            terms.append('%s * %s' % (C(t[0]), K(t[1])))
            terms.append('%s * %s' % (C(t[1]), K(t[0])))
        hexp = ' + '.join('%s * %s' % (C(t[0]), C(t[1])) for t in haf(i))
        W('  have hf%d : %s' % (i, ' + '.join(terms)))
        W('      = 2 * %s * (%s) := by' % (S, hexp))
        W('    linear_combination (%s : ℂ) * M%d' % (A, i))
    for i in VV:
        W('  have dg%d : %s'
          % (i, ' + '.join('Complex.normSq (%s)' % C(key(i, j))
                           for j in VV if j != i)))
        W('      = Complex.normSq (%s) + 1/8 := by' % B(i))
        W('    simp only [nss]')
        W('    linarith')
    W('  have htb : %s = 3/8 := by'
      % ' + '.join('Complex.normSq (%s)' % B(i) for i in VV))
    W('    simp only [nss]')
    W('    linarith')
    W('  have htc : %s = 1/2 := by'
      % ' + '.join('Complex.normSq (%s)' % C(e) for e in EE))
    W('    simp only [nss]')
    W('    linarith')
    W('  exact SixQubit.K5.no_go')
    W('    ⟨hs, ' + ', '.join('st%d' % i for i in VV) + ',')
    W('     ' + ', '.join('kb%d%d_%d' % (e[0], e[1], p) for e in EE for p in e) + ',')
    W('     ' + ', '.join('hf%d' % i for i in VV) + ',')
    W('     ' + ', '.join('dg%d' % i for i in VV) + ', htb, htc⟩')
    W('')
    W('end')
    W('')
    W('end SixQubit.Orbit%d' % OID)
    return NL.join(L) + NL


if __name__ == '__main__':
    src = emit()
    p = os.path.join(REPO, 'SixQubit', 'Orbit%d.lean' % OID)
    io.open(p, 'w', encoding='utf-8').write(src)
    print('%s : %d lines' % (p, src.count(NL)))
