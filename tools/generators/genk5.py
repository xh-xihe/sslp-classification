"""Emit `SixQubit/K5.lean`: the abstract algebra behind orbit 30.

Orbit 30 reduces to a configuration on `K_5`.  One string is distinguished
(`star`), five are *points* carrying amplitudes `b_i`, and ten are *edges*
carrying amplitudes `c_ij`.  The Walsh reduction of the ten admissible flip
masks produces, division free,

  * `star_i`  :  sum_{j != i} b_j c_ij = 0                     (`C b = 0`),
  * `kb`      :  b_p * k_ij = 0 for both endpoints p of ij,
                 where `k_ij` is the phase defect of the edge,
  * `hf_i`    :  a k-linear identity whose right-hand side is `2 s H_i`,
                 `H_i` the hafnian of the four-set `V \\ {i}`,

together with the exact moment data
`sum_{j != i} |c_ij|^2 = |b_i|^2 + 1/8`, `sum |b_i|^2 = 3/8`,
`sum |c_ij|^2 = 1/2`.

The proof splits on which point amplitudes vanish.

  |A| = 0  the total point mass 3/8 is not zero;
  |A| = 1  every edge at the single active point is killed by `star`, and
           then its degree equation reads `0 = |b_a|^2 + 1/8`;
  |A| = 2  the edge between the two active points is killed by `star`, so the
           two weighted stars are edge disjoint and carry mass 5/8 > 1/2;
  |A| = 3  the moment data force the internal edge mass to be at least 1/4,
           and an internal edge propagates through `star` to the whole
           triangle, which is an odd triangle;
  |A| >= 4 every edge has an active endpoint, so every `k_ij` vanishes and
           `hf_i` collapses to `H_i = 0`.  The support graph then has minimum
           degree at least two, and `graph` closes every such support.

`graph` is a decision tree over the ten edge supports.  Its leaves use four
closing rules: a degree bound, a hafnian equation with a single surviving
monomial, an odd binomial cycle of three hafnian equations, and the
determinant identity

    det C + 32 c01 c02 c12 c34^2  =  Q0 H0 + Q1 H1 + Q2 H2 + Q3 H3

(and its ten vertex relabellings), which with `C b = 0` and `b != 0` forbids a
triangle whose complementary edge is also active.

    python tools/run.py generators/genk5.py
"""
import io
import os
import re
import sys
from collections import Counter
from functools import lru_cache
from itertools import combinations

import sympy as sp

NL = chr(10)
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    '..', '..'))
V = list(range(5))
E = list(combinations(V, 2))
IDX = {e: r for r, e in enumerate(E)}
key = lambda i, j: (min(i, j), max(i, j))
AT = {v: [e for e in E if v in e] for v in V}
CN = {e: 'c%d%d' % e for e in E}
KN = {e: 'k%d%d' % e for e in E}


def hafterms(i):
    j, k, l, m = [v for v in V if v != i]
    return [(key(j, k), key(l, m)), (key(j, l), key(k, m)), (key(j, m), key(k, l))]


HAF = {i: hafterms(i) for i in V}
TRI = {}
for l, m in E:
    tri = [v for v in V if v not in (l, m)]
    TRI[(l, m)] = [key(*p) for p in combinations(tri, 2)]

# ---------------------------------------------------------------- certificates
SY, SYM = {}, []
for e in E:
    s = sp.symbols(CN[e])
    SY[e] = s
    SYM.append(s)
BS = list(sp.symbols('b0:5'))
CM = sp.Matrix(5, 5, lambda i, j: 0 if i == j else SY[key(i, j)])
DET = sp.expand(CM.det())
HS = [sp.expand(sum(SY[t[0]] * SY[t[1]] for t in HAF[i])) for i in V]


def qcert(pair):
    """det C + 32 * (triangle) * c_pair^2  =  sum Q_i H_i."""
    l, m = pair
    mon = SY[pair] ** 2
    for t in TRI[pair]:
        mon *= SY[t]
    tgt = sp.expand(DET + 32 * mon)
    mons, unk, Q = [], [], []
    for i in V:
        rest = [v for v in V if v != i]
        mi = []
        for p, q in combinations(rest, 2):
            o = [v for v in rest if v not in (p, q)]
            mi.append(SY[key(i, p)] * SY[key(i, q)] * SY[key(o[0], o[1])])
        a = sp.symbols('t%d_0:6' % i)
        unk += list(a)
        Q.append(sum(x * y for x, y in zip(a, mi)))
    eq = sp.expand(tgt - sum(q * h for q, h in zip(Q, HS)))
    sol = sp.solve(sp.Poly(eq, *SYM).coeffs(), unk, dict=True)[0]
    Qv = [sp.expand(q.subs(sol).subs({u: 0 for u in unk})) for q in Q]
    assert sp.expand(tgt - sum(q * h for q, h in zip(Qv, HS))) == 0
    return Qv, mon


COF = {p: [sp.expand(CM.cofactor(j, p)) for j in V] for p in (0, 1)}


def lean(expr):
    s = str(sp.expand(expr)).replace('**', '^')
    return s


# ------------------------------------------------------------------- the tree
def closes(st):
    for v in V:
        zs = [e for e in AT[v] if st[IDX[e]] == 0]
        if len(zs) >= 3:
            return ('deg', v, tuple(zs[:3]))
    for i in V:
        live = [t for t in HAF[i] if st[IDX[t[0]]] == 1 and st[IDX[t[1]]] == 1]
        dead = [t for t in HAF[i] if st[IDX[t[0]]] == 0 or st[IDX[t[1]]] == 0]
        if len(live) == 1 and len(dead) == 2:
            return ('one', i, live[0], tuple(dead))
    for l, m in E:
        if st[IDX[(l, m)]] == 1 and all(st[IDX[x]] == 1 for x in TRI[(l, m)]):
            return ('det', (l, m))
    pairs = {}
    for i in V:
        live = [t for t in HAF[i] if st[IDX[t[0]]] == 1 and st[IDX[t[1]]] == 1]
        dead = [t for t in HAF[i] if st[IDX[t[0]]] == 0 or st[IDX[t[1]]] == 0]
        if len(live) == 2 and len(dead) == 1:
            pairs[i] = (live, dead[0])
    for combo in combinations(sorted(pairs), 3):
        for s0 in (0, 1):
            for s1 in (0, 1):
                for s2 in (0, 1):
                    sel = (s0, s1, s2)
                    A = [pairs[combo[r]][0][sel[r]] for r in range(3)]
                    B = [pairs[combo[r]][0][1 - sel[r]] for r in range(3)]
                    if Counter(x for t in A for x in t) == Counter(x for t in B for x in t):
                        return ('cyc', combo, tuple(A), tuple(B),
                                tuple(pairs[c][1] for c in combo))
    return None


@lru_cache(maxsize=None)
def build(st):
    c = closes(st)
    if c is not None:
        return (1, ('leaf', c))
    best = None
    for r in range(10):
        if st[r] is not None:
            continue
        s0 = list(st)
        s0[r] = 0
        s1 = list(st)
        s1[r] = 1
        n0, t0 = build(tuple(s0))
        n1, t1 = build(tuple(s1))
        cand = (n0 + n1 + 1, ('split', r, t0, t1))
        if best is None or cand[0] < best[0]:
            best = cand
    return best


def deadfix(t, st):
    """`c_a * c_b` where the pair t is dead: return (factor, zero-edge)."""
    a, b = t
    if st[IDX[a]] == 0:
        return CN[b], a
    return CN[a], b


def emit_leaf(L, c, st, ind):
    W = lambda s: L.append(ind + s)
    if c[0] == 'deg':
        v, zs = c[1], c[2]
        j = [e for e in AT[v] if e not in zs][0]
        jj = [x for x in j if x != v][0]
        W('exact dg_%d_%d %s' % (v, jj, ' '.join('q%d%d' % e for e in zs)))
    elif c[0] == 'one':
        i, live, dead = c[1], c[2], c[3]
        corr = []
        for t in dead:
            f, z = deadfix(t, st)
            corr.append('(%s : ℂ) * q%d%d' % (f, z[0], z[1]))
        W('refine (mul_ne_zero q%d%d q%d%d) ?_'
          % (live[0][0], live[0][1], live[1][0], live[1][1]))
        W('linear_combination haf%d%s' % (i, ''.join(' - ' + x for x in corr)))
    elif c[0] == 'det':
        l, m = c[1]
        tri = TRI[(l, m)]
        W('refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero '
          'q%d%d q%d%d) q%d%d) q%d%d) q%d%d) ?_'
          % (tri[0][0], tri[0][1], tri[1][0], tri[1][1], tri[2][0], tri[2][1],
             l, m, l, m))
        W('exact det%d%d' % (l, m))
    else:
        combo, A, B, dead = c[1], c[2], c[3], c[4]
        for r in range(3):
            f, z = deadfix(dead[r], st)
            W('have hr%d : %s * %s + %s * %s = 0 := by'
              % (r, CN[A[r][0]], CN[A[r][1]], CN[B[r][0]], CN[B[r][1]]))
            W('  linear_combination haf%d - (%s : ℂ) * q%d%d'
              % (combo[r], f, z[0], z[1]))
        a = ['%s * %s' % (CN[A[r][0]], CN[A[r][1]]) for r in range(3)]
        b = ['%s * %s' % (CN[B[r][0]], CN[B[r][1]]) for r in range(3)]
        W('have key : (2 : ℂ) * ((%s) * (%s) * (%s)) = 0 := by' % tuple(a))
        W('  linear_combination ((%s) * (%s) : ℂ) * hr0 - ((%s) * (%s) : ℂ) * hr1'
          % (a[1], a[2], b[0], a[2]))
        W('    + ((%s) * (%s) : ℂ) * hr2' % (b[0], b[1]))
        W('refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero '
          '(mul_ne_zero q%d%d q%d%d) (mul_ne_zero q%d%d q%d%d)) '
          '(mul_ne_zero q%d%d q%d%d))) ?_'
          % (A[0][0][0], A[0][0][1], A[0][1][0], A[0][1][1],
             A[1][0][0], A[1][0][1], A[1][1][0], A[1][1][1],
             A[2][0][0], A[2][0][1], A[2][1][0], A[2][1][1]))
        W('exact key')


def emit_tree(L, t, st, ind):
    if t[0] == 'leaf':
        emit_leaf(L, t[1], st, ind)
        return
    r = t[1]
    e = E[r]
    L.append(ind + 'rcases eq_or_ne %s 0 with q%d%d | q%d%d'
             % (CN[e], e[0], e[1], e[0], e[1]))
    s0 = list(st)
    s0[r] = 0
    s1 = list(st)
    s1[r] = 1
    L.append(ind + '· ' + '')
    emit_tree(L, t[2], tuple(s0), ind + '  ')
    L.append(ind + '· ' + '')
    emit_tree(L, t[3], tuple(s1), ind + '  ')


def tidy(L):
    """Merge a bare bullet line with the following line."""
    out = []
    for s in L:
        if out and out[-1].rstrip() and out[-1].rstrip()[-1] == '·' \
                and out[-1].strip() == '·':
            out[-1] = out[-1].rstrip() + ' ' + s.strip()
        else:
            out.append(s)
    return out


# ------------------------------------------------------------------ the module
STV = ' '.join(['s'] + ['b%d' % i for i in V] + [CN[e] for e in E]
               + [KN[e] for e in E])
BR = lambda e: '%s * %s' % (CN[e[0]], CN[e[1]])
HEXP = lambda i: ' + '.join(BR(t) for t in HAF[i])
STEXP = lambda i: ' + '.join('b%d * %s' % (j, CN[key(i, j)])
                             for j in V if j != i)
DGEXP = lambda i: ' + '.join('Complex.normSq %s' % CN[key(i, j)]
                             for j in V if j != i)
MONS = lambda e: ' * '.join([CN[t] for t in TRI[e]] + [CN[e], CN[e]])
NN = (['Complex.normSq_nonneg b%d' % i for i in V]
      + ['Complex.normSq_nonneg %s' % CN[e] for e in E])


def emit_graph(L):
    W = L.append
    _, tree = build(tuple([None] * 10))
    body = tidy_body(tree)
    used = NL.join(body)
    nm = lambda x: x if re.search(r'(?<![A-Za-z0-9_])' + x + r'(?![A-Za-z0-9_])',
                                  used) else '_' + x
    W('/-- **The support graph is impossible.**  A decision tree over the ten')
    W('edge supports; every leaf closes by a degree bound, by a hafnian')
    W('equation with one surviving monomial, by an odd binomial cycle, or by')
    W('the determinant identity. -/')
    W('theorem graph {%s : ℂ}' % ' '.join(CN[e] for e in E))
    for i in V:
        W('    (%s : %s = 0)' % (nm('haf%d' % i), HEXP(i)))
    for i in V:
        for j in V:
            if j == i:
                continue
            rest = [k for k in V if k != i and k != j]
            W('    (%s : %s → False)'
              % (nm('dg_%d_%d' % (i, j)),
                 ' → '.join('%s = 0' % CN[key(i, k)] for k in rest)))
    for e in E:
        W('    (%s : %s = 0)' % (nm('det%d%d' % e), MONS(e)))
    W('    : False := by')
    L.extend(body)
    W('')


def tidy_body(tree):
    body = []
    emit_tree(body, tree, tuple([None] * 10), '  ')
    return tidy(body)


def emit_dets(L, p):
    W = L.append
    Q = {e: qcert(e)[0] for e in E}
    W('/-- The determinant identity, in the ten shapes obtained by relabelling')
    W('the vertices, cancelled against the nonzero point amplitude `b%d`. -/' % p)
    W('theorem dets%d {%s : ℂ}' % (p, ' '.join(['b%d' % i for i in V]
                                               + [CN[e] for e in E])))
    for i in V:
        W('    (st%d : %s = 0)' % (i, STEXP(i)))
    for i in V:
        W('    (haf%d : %s = 0)' % (i, HEXP(i)))
    W('    (hb : b%d ≠ 0) :' % p)
    W('    ' + (NL + '      ∧ ').join('%s = 0' % MONS(e) for e in E) + ' := by')
    W('  refine ⟨' + ', '.join('?_' for _ in E) + '⟩')
    for e in E:
        W('  · have hx : %s * b%d = 0 := by' % (MONS(e), p))
        terms = []
        for i in V:
            if Q[e][i] != 0:
                terms.append('+ (((%s) * b%d) / 32 : ℂ) * haf%d'
                             % (lean(Q[e][i]), p, i))
        for j in V:
            terms.append('- ((%s) / 32 : ℂ) * st%d' % (lean(COF[p][j]), j))
        W('      linear_combination '
          + (NL + '        ').join(terms).lstrip('+ '))
        W('    rcases mul_eq_zero.mp hx with y | y')
        W('    · exact y')
        W('    · exact absurd y hb')
    W('')


def emit_sys(L):
    W = L.append
    W('/-- The reduced Walsh data of orbit 30 on the `K_5` labelling, together')
    W('with the exact moment data. -/')
    W('structure Sys (%s : ℂ) : Prop where' % STV)
    W('  hs : s ≠ 0')
    for i in V:
        W('  st%d : %s = 0' % (i, STEXP(i)))
    for e in E:
        for p in e:
            W('  kb%d%d_%d : b%d * %s = 0' % (e[0], e[1], p, p, KN[e]))
    for i in V:
        j, k, l, m = [v for v in V if v != i]
        terms = []
        for t in HAF[i]:
            terms.append('%s * %s' % (CN[t[0]], KN[t[1]]))
            terms.append('%s * %s' % (CN[t[1]], KN[t[0]]))
        W('  hf%d : %s' % (i, ' + '.join(terms)))
        W('      = 2 * s * (%s)' % HEXP(i))
    for i in V:
        W('  dg%d : %s = Complex.normSq b%d + 1/8' % (i, DGEXP(i), i))
    W('  tb : %s = 3/8' % ' + '.join('Complex.normSq b%d' % i for i in V))
    W('  tc : %s = 1/2' % ' + '.join('Complex.normSq %s' % CN[e] for e in E))
    W('')


def iso(i, t):
    """Isolate the term b_t * c_it of st_i, killing the others."""
    others = [j for j in V if j != i and j != t]
    return 'h.st%d%s' % (i, ''.join(' - (%s : ℂ) * p%d' % (CN[key(i, j)], j)
                                    for j in others))


def emit_case(L, act, ind):
    W = lambda s: L.append(ind + s)
    zero = [i for i in V if i not in act]
    if len(act) == 0:
        W('have ht := h.tb')
        W('rw [%s, Complex.normSq_zero] at ht'
          % ', '.join('p%d' % i for i in V))
        W('norm_num at ht')
    elif len(act) == 1:
        a = act[0]
        for k in V:
            if k == a:
                continue
            W('have x%d : %s = 0 := by' % (k, CN[key(a, k)]))
            W('  have hx : b%d * %s = 0 := by linear_combination %s'
              % (a, CN[key(a, k)], iso(k, a)))
            W('  rcases mul_eq_zero.mp hx with y | y')
            W('  · exact absurd y p%d' % a)
            W('  · exact y')
        W('have hd := h.dg%d' % a)
        W('rw [%s, Complex.normSq_zero] at hd'
          % ', '.join('x%d' % k for k in V if k != a))
        W('linarith only [hd, Complex.normSq_nonneg b%d]' % a)
    elif len(act) == 2:
        a, b = act
        W('have hab : %s = 0 := by' % CN[key(a, b)])
        W('  have hx : b%d * %s = 0 := by linear_combination %s'
          % (b, CN[key(a, b)], iso(a, b)))
        W('  rcases mul_eq_zero.mp hx with y | y')
        W('  · exact absurd y p%d' % b)
        W('  · exact y')
        W('have hd1 := h.dg%d' % a)
        W('have hd2 := h.dg%d' % b)
        W('have ht := h.tb')
        W('have hc := h.tc')
        W('rw [hab, Complex.normSq_zero] at hd1 hd2 hc')
        W('rw [%s, Complex.normSq_zero] at ht'
          % ', '.join('p%d' % i for i in zero))
        W('linarith only [hd1, hd2, ht, hc, %s]' % ', '.join(NN))
    elif len(act) == 3:
        a, b, c = act
        r, s2 = zero
        ab, ac, bc = CN[key(a, b)], CN[key(a, c)], CN[key(b, c)]
        W('have hd1 := h.dg%d' % a)
        W('have hd2 := h.dg%d' % b)
        W('have hd3 := h.dg%d' % c)
        W('have ht := h.tb')
        W('have hc := h.tc')
        W('rw [p%d, p%d, Complex.normSq_zero] at ht' % (r, s2))
        W('have hW : (0:Real) < Complex.normSq %s + Complex.normSq %s '
          '+ Complex.normSq %s := by' % (ab, ac, bc))
        W('  linarith only [hd1, hd2, hd3, ht, hc, %s]' % ', '.join(NN))
        W('have sa : b%d * %s + b%d * %s = 0 := by linear_combination '
          'h.st%d - (%s : ℂ) * p%d - (%s : ℂ) * p%d'
          % (b, ab, c, ac, a, CN[key(a, r)], r, CN[key(a, s2)], s2))
        W('have sb : b%d * %s + b%d * %s = 0 := by linear_combination '
          'h.st%d - (%s : ℂ) * p%d - (%s : ℂ) * p%d'
          % (a, ab, c, bc, b, CN[key(b, r)], r, CN[key(b, s2)], s2))
        W('have sc : b%d * %s + b%d * %s = 0 := by linear_combination '
          'h.st%d - (%s : ℂ) * p%d - (%s : ℂ) * p%d'
          % (a, ac, b, bc, c, CN[key(c, r)], r, CN[key(c, s2)], s2))
        W('have kk := SixQubit.Triangle.prod_eq_zero sc sb sa')
        W('have z1 : %s = 0 ∨ %s = 0 := by' % (bc, ac))
        W('  rcases mul_eq_zero.mp kk with y | y')
        W('  · rcases mul_eq_zero.mp y with y2 | y2')
        W('    · exact absurd y2 p%d' % c)
        W('    · exact Or.inl y2')
        W('  · exact Or.inr y')
        W('have zz : %s = 0 ∧ %s = 0 ∧ %s = 0 := by' % (ab, ac, bc))
        W('  rcases z1 with y | y')
        W('  · have h1 : %s = 0 := by' % ab)
        W('      have hx : b%d * %s = 0 := by linear_combination sb - (b%d : ℂ) * y'
          % (a, ab, c))
        W('      rcases mul_eq_zero.mp hx with w | w')
        W('      · exact absurd w p%d' % a)
        W('      · exact w')
        W('    have h2 : %s = 0 := by' % ac)
        W('      have hx : b%d * %s = 0 := by linear_combination sc - (b%d : ℂ) * y'
          % (a, ac, b))
        W('      rcases mul_eq_zero.mp hx with w | w')
        W('      · exact absurd w p%d' % a)
        W('      · exact w')
        W('    exact ⟨h1, h2, y⟩')
        W('  · have h1 : %s = 0 := by' % ab)
        W('      have hx : b%d * %s = 0 := by linear_combination sa - (b%d : ℂ) * y'
          % (b, ab, c))
        W('      rcases mul_eq_zero.mp hx with w | w')
        W('      · exact absurd w p%d' % b)
        W('      · exact w')
        W('    have h2 : %s = 0 := by' % bc)
        W('      have hx : b%d * %s = 0 := by linear_combination sc - (b%d : ℂ) * y'
          % (b, bc, a))
        W('      rcases mul_eq_zero.mp hx with w | w')
        W('      · exact absurd w p%d' % b)
        W('      · exact w')
        W('    exact ⟨h1, y, h2⟩')
        W('obtain ⟨u1, u2, u3⟩ := zz')
        W('rw [u1, u2, u3, Complex.normSq_zero] at hW')
        W('norm_num at hW')
    else:
        pc = 0 if 0 in act else 1
        for e in E:
            p = e[0] if e[0] in act else e[1]
            W('have kk%d%d : %s = 0 := by' % (e[0], e[1], KN[e]))
            W('  rcases mul_eq_zero.mp h.kb%d%d_%d with y | y' % (e[0], e[1], p))
            W('  · exact absurd y p%d' % p)
            W('  · exact y')
        for i in V:
            W('have haf%d : %s = 0 := by' % (i, HEXP(i)))
            W('  have hx : (2 : ℂ) * s * (%s) = 0 := by' % HEXP(i))
            terms = []
            for t in HAF[i]:
                terms.append('(%s : ℂ) * kk%d%d' % (CN[t[0]], t[1][0], t[1][1]))
                terms.append('(%s : ℂ) * kk%d%d' % (CN[t[1]], t[0][0], t[0][1]))
            W('    linear_combination (-1 : ℂ) * h.hf%d + %s'
              % (i, ' + '.join(terms)))
            W('  rcases mul_eq_zero.mp hx with y | y')
            W('  · rcases mul_eq_zero.mp y with y2 | y2')
            W('    · norm_num at y2')
            W('    · exact absurd y2 h.hs')
            W('  · exact y')
        for i in V:
            for j in V:
                if j == i:
                    continue
                rest = [k for k in V if k != i and k != j]
                W('have dg_%d_%d : %s → False := by'
                  % (i, j, ' → '.join('%s = 0' % CN[key(i, k)] for k in rest)))
                W('  intro z1 z2 z3')
                if j in act:
                    W('  have hij : %s = 0 := by' % CN[key(i, j)])
                    W('    have hx : b%d * %s = 0 := by linear_combination h.st%d %s'
                      % (j, CN[key(i, j)], i,
                         ' '.join('- (b%d : ℂ) * z%d' % (k, r + 1)
                                  for r, k in enumerate(rest))))
                    W('    rcases mul_eq_zero.mp hx with y | y')
                    W('    · exact absurd y p%d' % j)
                    W('    · exact y')
                    W('  have hd := h.dg%d' % i)
                    W('  rw [hij, z1, z2, z3, Complex.normSq_zero] at hd')
                    W('  linarith only [hd, Complex.normSq_nonneg b%d]' % i)
                else:
                    W('  have hd1 := h.dg%d' % i)
                    W('  have hd2 := h.dg%d' % j)
                    W('  rw [z1, z2, z3, Complex.normSq_zero] at hd1')
                    W('  rw [p%d, Complex.normSq_zero] at hd2' % j)
                    W('  have hz : Complex.normSq b%d = 0 := by'
                      ' linarith only [hd1, hd2, Complex.normSq_nonneg b%d, %s]'
                      % (i, i, ', '.join('Complex.normSq_nonneg %s'
                                         % CN[key(j, t)]
                                         for t in V if t != j and t != i)))
                    W('  exact p%d (Complex.normSq_eq_zero.mp hz)' % i)
        W('obtain ⟨%s⟩ := dets%d %s %s p%d'
          % (', '.join('d%d%d' % e for e in E), pc,
             ' '.join('h.st%d' % i for i in V),
             ' '.join('haf%d' % i for i in V), pc))
        W('exact graph %s %s %s'
          % (' '.join('haf%d' % i for i in V),
             ' '.join('dg_%d_%d' % (i, j) for i in V for j in V if j != i),
             ' '.join('d%d%d' % e for e in E)))


def emit_nogo(L):
    W = L.append
    for mask in range(32):
        act = [i for i in V if (mask >> i) & 1]
        W('/-- The branch in which exactly the point amplitudes %s are nonzero. -/'
          % (', '.join('b%d' % i for i in act) or 'none'))
        body = []
        emit_case(body, act, '  ')
        body = tidy(body)
        txt = NL.join(body)
        pn = lambda i: ('p%d' % i) if re.search(
            r'(?<![A-Za-z0-9_])p%d(?![A-Za-z0-9_])' % i, txt) else '_p%d' % i
        W('theorem case%d {%s : ℂ} (h : Sys %s)' % (mask, STV, STV))
        W('    ' + ' '.join('(%s : b%d %s 0)'
                            % (pn(i), i, '≠' if i in act else '=')
                            for i in V) + ' : False := by')
        L.extend(body)
        W('')
    W('/-- **The K_5 system is contradictory.** -/')
    W('theorem no_go {%s : ℂ} (h : Sys %s) : False := by' % (STV, STV))
    saved = len(L)

    def rec(i, act, ind):
        if i == 5:
            mask = sum(1 << k for k in act)
            L.append(ind + 'exact case%d h p0 p1 p2 p3 p4' % mask)
            return
        L.append(ind + 'rcases eq_or_ne b%d 0 with p%d | p%d' % (i, i, i))
        L.append(ind + '·')
        rec(i + 1, act, ind + '  ')
        L.append(ind + '·')
        rec(i + 1, act + [i], ind + '  ')

    rec(0, [], '  ')
    merged = tidy(L[saved:])
    del L[saved:]
    L.extend(merged)
    W('')


def emit():
    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('import SixQubit.Triangle')
    W('')
    W('/-!')
    W('# The K_5 configuration behind orbit 30')
    W('')
    for line in __doc__.strip().split(NL)[2:-2]:
        W(line)
    W('')
    W('`native_decide` is not used, and the module mentions no bit strings.')
    W('-/')
    W('')
    W('namespace SixQubit.K5')
    W('')
    W('open scoped ComplexConjugate')
    W('')
    W('noncomputable section')
    W('')
    W('/-! ## The support-graph decision tree -/')
    W('')
    emit_graph(L)
    W('/-! ## The determinant identities -/')
    W('')
    emit_dets(L, 0)
    emit_dets(L, 1)
    W('/-! ## The hypothesis bundle -/')
    W('')
    emit_sys(L)
    W('/-! ## The no-go -/')
    W('')
    emit_nogo(L)
    W('end')
    W('')
    W('end SixQubit.K5')
    return NL.join(L) + NL


if __name__ == '__main__':
    src = emit()
    p = os.path.join(REPO, 'SixQubit', 'K5.lean')
    io.open(p, 'w', encoding='utf-8').write(src)
    print('%s : %d lines' % (p, src.count(NL)))
