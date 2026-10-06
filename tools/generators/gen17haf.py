"""Generate SixQubit/Hafnian.lean -- the division-free hafnian algebra layer.

Fifteen edge variables c_ij of K_6, fifteen four-set hafnian equations and the
six weighted-degree equations.  The layer proves the whole system contradictory.

Everything is driven by the vertex relabelling action: the hypothesis bundle
`Sys` is closed under the five adjacent transpositions, so every lemma is proved
once in a canonical labelling and transported.
"""
from itertools import combinations

V = list(range(6))
SLOTS = list(combinations(V, 2))
FOURS = list(combinations(V, 4))


def nm(e):
    return 'c%d%d' % e


def srt(i, j):
    return (i, j) if i < j else (j, i)


ARGS = ' '.join(nm(e) for e in SLOTS)


def perm_args(p):
    """argument list of Sys after relabelling by p (p[i] is the image of i)"""
    return ' '.join(nm(srt(p[i], p[j])) for (i, j) in SLOTS)


def haf_eq(q, p=None):
    """the hafnian equation of four-set q, in variables relabelled by p"""
    if p is None:
        p = list(range(6))
    i, j, k, l = q
    terms = []
    for (a, b), (x, y) in [((i, j), (k, l)), ((i, k), (j, l)), ((i, l), (j, k))]:
        terms.append('%s * %s' % (nm(srt(p[a], p[b])), nm(srt(p[x], p[y]))))
    return ' + '.join(terms) + ' = 0'


def deg_eq(v, p=None):
    if p is None:
        p = list(range(6))
    terms = ['Complex.normSq %s' % nm(srt(p[v], p[u])) for u in V if u != v]
    return ' + '.join(terms) + ' = 1/4'


# ---------------------------------------------------------------- permutations
GENS = {}
for k in range(5):
    p = list(range(6))
    p[k], p[k + 1] = p[k + 1], p[k]
    GENS['swap%d%d' % (k, k + 1)] = tuple(p)


def compose(p, q):
    """(p o q)(i) = p[q[i]]"""
    return tuple(p[q[i]] for i in range(6))


IDENT = tuple(range(6))

# BFS: word[perm] = list of generator names g1,...,gk with perm = t1 o t2 o ... o tk
# and the Lean term is  gk (... (g1 h))
word = {IDENT: []}
frontier = [IDENT]
while frontier:
    nxt = []
    for s in frontier:
        for g, t in GENS.items():
            r = compose(s, t)
            if r not in word:
                word[r] = word[s] + [g]
                nxt.append(r)
    frontier = nxt
assert len(word) == 720


def term(p, base='h'):
    p = tuple(p)
    out = base
    for g in word[p]:
        out = '%s (%s)' % (g, out) if ' ' in out else '%s %s' % (g, out)
    return out


def find_perm(pairs, fixed=None):
    """smallest permutation p with p[a] = b for every (a, b) in pairs"""
    p = [None] * 6
    used = set()
    for a, b in pairs:
        p[a] = b
        used.add(b)
    rest = [x for x in V if x not in used]
    for i in V:
        if p[i] is None:
            p[i] = rest.pop(0)
    return tuple(p)


# ---------------------------------------------------------------- emit
L = []
A = L.append

A('import Mathlib')
A('')
A('import SS.FullKL')
A('import SixQubit.Common')
A('')
A('/-!')
A('# Vanishing hafnians on the six-vertex support graph')
A('')
A('Orbit 17 of `six_qubit_sslp.tex` reduces to the following purely algebraic')
A('configuration.  Fifteen complex numbers `c_ij` are indexed by the edges of')
A('`K_6`.  Every four-set carries a *hafnian* equation')
A('')
A('```')
A('c_ij c_kl + c_ik c_jl + c_il c_jk = 0 ,')
A('```')
A('')
A('and the squared moduli form a scaled fractional perfect matching:')
A('`sum_{e ni v} |c_e|^2 = 1/4` at every vertex `v`.  The two families are')
A('contradictory.')
A('')
A('The proof never divides.  Three facts do all the work.')
A('')
A('* `deg4`: the single monomial identity')
A('  `c01 c02 c03 c45 = (c04 c05 / 3) H_0123 - (c03 c05 / 6) H_0124 - ...`,')
A('  found by eliminating in the ten hafnians through one vertex.  It says a')
A('  vertex with three active edges forces the complementary edge to vanish.')
A('* `tri`: the odd-triangle elimination `uc * va * vb = 0`, reused from the')
A('  shape already met by several orbits.')
A('* the degree equations, which forbid an isolated vertex and forbid a star.')
A('')
A('Because the whole hypothesis bundle `Sys` is stable under vertex relabelling')
A('(`swap01`, ..., `swap45`), each combinatorial case is proved once in a')
A('canonical labelling and transported by a word in those five lemmas.')
A('')
A('`native_decide` is not used, and the module mentions no bit strings.')
A('-/')
A('')
A('namespace SixQubit.Hafnian')
A('')
A('open scoped ComplexConjugate')
A('')
A('noncomputable section')
A('')
A('/-! ## The hypothesis bundle -/')
A('')
A('/-- The fifteen four-set hafnian equations together with the six weighted')
A('degree equations of the fractional perfect matching. -/')
A('structure Sys (%s : ℂ) : Prop where' % ARGS)
for q in FOURS:
    A('  h%d%d%d%d : %s' % (q + (haf_eq(q),)))
for v in V:
    A('  d%d : %s' % (v, deg_eq(v)))
A('')
A('variable {%s : ℂ}' % ARGS)
A('')
A('/-! ## Elementary helpers -/')
A('')
A('/-- Cancel three nonzero factors from a four-fold product. -/')
A('theorem mul4 {a b c d : ℂ} (h : a * b * c * d = 0)')
A('    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : d = 0 := by')
A('  rcases mul_eq_zero.mp h with h1 | h1')
A('  · rcases mul_eq_zero.mp h1 with h2 | h2')
A('    · rcases mul_eq_zero.mp h2 with h3 | h3')
A('      · exact absurd h3 ha')
A('      · exact absurd h3 hb')
A('    · exact absurd h2 hc')
A('  · exact h1')
A('')
A('/-- Cancel two nonzero factors from a threefold product. -/')
A('theorem mul3 {a b c : ℂ} (h : a * b * c = 0) (hb : b ≠ 0) (hc : c ≠ 0) : a = 0 := by')
A('  rcases mul_eq_zero.mp h with h1 | h1')
A('  · rcases mul_eq_zero.mp h1 with h2 | h2')
A('    · exact h2')
A('    · exact absurd h2 hb')
A('  · exact absurd h1 hc')
A('')
A('/-- The odd-triangle elimination: three reciprocal relations force a single')
A('product to vanish, with no division and no nonvanishing side condition. -/')
A('theorem tri {ua ub uc va vb vc : ℂ}')
A('    (h1 : ua * vb + ub * va = 0)')
A('    (h2 : ua * vc + uc * va = 0)')
A('    (h3 : ub * vc + uc * vb = 0) : uc * va * vb = 0 := by')
A('  linear_combination (-vc / 2) * h1 + (vb / 2) * h2 + (va / 2) * h3')
A('')
A('/-! ## Vertex relabelling -/')
A('')
for g, p in GENS.items():
    a, b = [i for i in V if p[i] != i]
    A('/-- Relabelling the two vertices %d and %d preserves the system. -/' % (a, b))
    A('theorem %s (h : Sys %s) :' % (g, ARGS))
    A('    Sys %s :=' % perm_args(p))
    body = []
    for q in FOURS:
        img = tuple(sorted(p[x] for x in q))
        body.append('by linear_combination h.h%d%d%d%d' % img)
    for v in V:
        body.append('by linear_combination h.d%d' % p[v])
    lines = ['  ' + chr(0x27e8) + body[0] + ',']
    lines += ['   ' + b + ',' for b in body[1:-1]]
    lines.append('   ' + body[-1] + chr(0x27e9))
    for ln in lines:
        A(ln)
    A('')

A('/-! ## The degree-four monomial certificate -/')
A('')
A('/-- **Three active edges at a vertex kill the complementary edge.**  The')
A('identity is a rational combination of the ten hafnians through vertex `0`;')
A('it was obtained by eliminating the ten edges of the opposite `K_5`. -/')
A('theorem deg4 (h : Sys %s) :' % ARGS)
A('    c01 * c02 * c03 * c45 = 0 := by')
A('  linear_combination (c04 * c05 / 3) * h.h0123 - (c03 * c05 / 6) * h.h0124')
A('    - (c03 * c04 / 6) * h.h0125 - (c02 * c05 / 6) * h.h0134')
A('    - (c02 * c04 / 6) * h.h0135 + (c02 * c03 / 3) * h.h0145')
A('    - (c01 * c05 / 6) * h.h0234 - (c01 * c04 / 6) * h.h0235')
A('    + (c01 * c03 / 3) * h.h0245 + (c01 * c02 / 3) * h.h0345')
A('')
A('/-! ## Isolated vertices and stars -/')
A('')
A('/-- A vertex with no active edge contradicts its degree equation. -/')
A('theorem iso (h : Sys %s)' % ARGS)
A('    (z1 : c01 = 0) (z2 : c02 = 0) (z3 : c03 = 0) (z4 : c04 = 0) (z5 : c05 = 0) :')
A('    False := by')
A('  have hd := h.d0')
A('  rw [z1, z2, z3, z4, z5] at hd')
A('  norm_num at hd')
A('')
A('/-- A star has a leaf mass of `1/4` on every one of its five edges, so its')
A('centre carries weighted degree `5/4`. -/')
A('theorem star (h : Sys %s)' % ARGS)
zs = [e for e in SLOTS if 0 not in e]
A('    ' + ' '.join('(z%d%d : %s = 0)' % (e + (nm(e),)) for e in zs) + ' :')
A('    False := by')
for v in range(1, 6):
    others = [e for e in SLOTS if v in e and 0 not in e]
    A('  have k%d : Complex.normSq %s = 1/4 := by' % (v, nm(srt(0, v))))
    A('    have hd := h.d%d' % v)
    A('    rw [%s] at hd' % ', '.join('z%d%d' % e for e in others))
    A('    simpa using hd')
A('  linarith [h.d0, k1, k2, k3, k4, k5]')
A('')
A('/-! ## No vertex carries three active edges -/')
A('')
A('/-- **The key lemma.**  If three edges at a vertex are all active the system')
A('collapses: the complementary edge dies by `deg4`, and then either the odd')
A('triangle isolates one of the two remaining vertices, or the vertex becomes')
A('universal and the support is a star. -/')
A('theorem key (h : Sys %s)' % ARGS)
A('    (n1 : c01 ≠ 0) (n2 : c02 ≠ 0) (n3 : c03 ≠ 0) : False := by')
A('  have e45 : c45 = 0 := mul4 (deg4 h) n1 n2 n3')
A('  by_cases h04 : c04 = 0')
A('  · -- vertex 4 is not joined to 0: the odd triangle kills its other edges')
A('    have t1 : c14 * c02 + c24 * c01 = 0 := by linear_combination h.h0124 - c12 * h04')
A('    have t2 : c14 * c03 + c34 * c01 = 0 := by linear_combination h.h0134 - c13 * h04')
A('    have t3 : c24 * c03 + c34 * c02 = 0 := by linear_combination h.h0234 - c23 * h04')
A('    have z34 : c34 = 0 := mul3 (tri t1 t2 t3) n1 n2')
A('    have z24 : c24 = 0 := mul3 (tri t2 t1 (by linear_combination t3)) n1 n3')
A("    have t4 : c24 * c01 + c14 * c02 = 0 := by linear_combination t1")
A('    have z14 : c14 = 0 := mul3 (tri t3 t4 (by linear_combination t2)) n2 n3')
A('    exact iso (%s) h04 z14 z24 z34 e45' % term(find_perm([(0, 4), (1, 0), (2, 1), (3, 2), (4, 3), (5, 5)])))
A('  · -- vertex 0 also reaches 4')
p35 = find_perm([(0, 0), (1, 1), (2, 2), (3, 4)])
p25 = find_perm([(0, 0), (1, 1), (2, 3), (3, 4)])
p15 = find_perm([(0, 0), (1, 2), (2, 3), (3, 4)])
A('    have e35 : c35 = 0 := mul4 (deg4 (%s)) n1 n2 h04' % term(p35))
A('    have e25 : c25 = 0 := mul4 (deg4 (%s)) n1 n3 h04' % term(p25))
A('    have e15 : c15 = 0 := mul4 (deg4 (%s)) n2 n3 h04' % term(p15))
A('    by_cases h05 : c05 = 0')
A('    · exact iso (%s) h05 e15 e25 e35 e45' % term(find_perm([(0, 5), (1, 0), (2, 1), (3, 2), (4, 3), (5, 4)])))
A('    · -- vertex 0 is universal, so every other edge dies and the support is a star')
for (trio, target) in [((1, 2, 5), (3, 4)), ((1, 3, 5), (2, 4)), ((2, 3, 5), (1, 4)),
                       ((1, 4, 5), (2, 3)), ((2, 4, 5), (1, 3)), ((3, 4, 5), (1, 2))]:
    p = find_perm([(0, 0), (1, trio[0]), (2, trio[1]), (3, trio[2])])
    ns = {1: 'n1', 2: 'n2', 3: 'n3', 4: 'h04', 5: 'h05'}
    A('      have z%d%d : %s = 0 := mul4 (deg4 (%s)) %s %s %s'
      % (target + (nm(target), term(p), ns[trio[0]], ns[trio[1]], ns[trio[2]])))
A('      exact star h z12 z13 z14 e15 z23 z24 e25 z34 e35 e45')
A('')
A('/-! ## Two disjoint active edges -/')
A('')
A('/-- The four-cycle case: with `c01`, `c23`, `c02`, `c13` all active every')
A('vertex of `{0,1,2,3}` already carries two edges, so `key` empties the eight')
A('crossing edges, the two remaining vertices are joined, and the hafnian of')
A('`{0,1,4,5}` is the single monomial `c01 * c45`. -/')
A('theorem disjA (h : Sys %s)' % ARGS)
A('    (n01 : c01 ≠ 0) (n23 : c23 ≠ 0) (n02 : c02 ≠ 0) (n13 : c13 ≠ 0) : False := by')
kills = [
    ((0, 3), (0, 1, 2, 3), 'n01', 'n02'),
    ((0, 4), (0, 1, 2, 4), 'n01', 'n02'),
    ((0, 5), (0, 1, 2, 5), 'n01', 'n02'),
    ((1, 2), (1, 0, 3, 2), 'n01', 'n13'),
    ((1, 4), (1, 0, 3, 4), 'n01', 'n13'),
    ((1, 5), (1, 0, 3, 5), 'n01', 'n13'),
    ((2, 4), (2, 0, 3, 4), 'n02', 'n23'),
    ((2, 5), (2, 0, 3, 5), 'n02', 'n23'),
    ((3, 4), (3, 1, 2, 4), 'n13', 'n23'),
    ((3, 5), (3, 1, 2, 5), 'n13', 'n23'),
]
for (tgt, cfg, na, nb) in kills:
    v, i, j, k = cfg
    p = find_perm([(0, v), (1, i), (2, j), (3, k)])
    A('  have z%d%d : %s = 0 := by' % (tgt + (nm(tgt),)))
    A('    by_contra hx')
    A('    exact key (%s) %s %s hx' % (term(p), na, nb))
A('  have n45 : c45 ≠ 0 := by')
A('    intro hx')
A('    exact iso (%s) z04 z14 z24 z34 hx' % term(find_perm([(0, 4), (1, 0), (2, 1), (3, 2), (4, 3), (5, 5)])))
A('  have hz : c01 * c45 = 0 := by linear_combination h.h0145 - c15 * z04 - c14 * z05')
A('  rcases mul_eq_zero.mp hz with hh | hh')
A('  · exact n01 hh')
A('  · exact n45 hh')
A('')
A('/-- **Two disjoint active edges are impossible.**  The hafnian of their')
A('four-set has to activate a second matching, and that is the four-cycle. -/')
A('theorem disj (h : Sys %s)' % ARGS)
A('    (n01 : c01 ≠ 0) (n23 : c23 ≠ 0) : False := by')
A('  have hb : c02 * c13 ≠ 0 ∨ c03 * c12 ≠ 0 := by')
A('    by_contra hc')
A('    push_neg at hc')
A('    obtain ⟨p, q⟩ := hc')
A('    have hz : c01 * c23 = 0 := by linear_combination h.h0123 - p - q')
A('    rcases mul_eq_zero.mp hz with hh | hh')
A('    · exact n01 hh')
A('    · exact n23 hh')
A('  rcases hb with hm | hm')
A('  · exact disjA h n01 n23 (left_ne_zero_of_mul hm) (right_ne_zero_of_mul hm)')
A('  · exact disjA (%s) n01 n23 (left_ne_zero_of_mul hm) (right_ne_zero_of_mul hm)'
  % term(find_perm([(0, 0), (1, 1), (2, 3), (3, 2), (4, 4), (5, 5)])))
A('')
A('/-! ## The headline -/')
A('')


def iso_at(v):
    rest = [u for u in V if u != v]
    return find_perm([(0, v)] + [(t + 1, rest[t]) for t in range(5)])


def disj_at(e, g):
    return find_perm([(0, e[0]), (1, e[1]), (2, g[0]), (3, g[1])])


A('/-- With one active edge at vertex `0` fixed, every way of not being isolated')
A('at a second vertex either produces two disjoint active edges or three active')
A('edges at one vertex. -/')
A('theorem main1 (h : Sys %s) (n01 : c01 ≠ 0) : False := by' % ARGS)
A('  by_cases n02 : c02 = 0')
A('  · by_cases n12 : c12 = 0')
A('    · by_cases n23 : c23 = 0')
A('      · by_cases n24 : c24 = 0')
A('        · by_cases n25 : c25 = 0')
A('          · exact iso (%s) n02 n12 n23 n24 n25' % term(iso_at(2)))
A('          · exact disj (%s) n01 n25' % term(disj_at((0, 1), (2, 5))))
A('        · exact disj (%s) n01 n24' % term(disj_at((0, 1), (2, 4))))
A('      · exact disj h n01 n23')
A('    · by_cases m03 : c03 = 0')
A('      · by_cases m13 : c13 = 0')
A('        · by_cases m23 : c23 = 0')
A('          · by_cases m34 : c34 = 0')
A('            · by_cases m35 : c35 = 0')
A('              · exact iso (%s) m03 m13 m23 m34 m35' % term(iso_at(3)))
A('              · exact disj (%s) n01 m35' % term(disj_at((0, 1), (3, 5))))
A('            · exact disj (%s) n01 m34' % term(disj_at((0, 1), (3, 4))))
A('          · exact disj (%s) n01 m23' % term(disj_at((0, 1), (2, 3))))
A('        · exact key (%s) n01 n12 m13' % term(find_perm([(0, 1), (1, 0), (2, 2), (3, 3)])))
A('      · exact disj (%s) m03 n12' % term(disj_at((0, 3), (1, 2))))
A('  · by_cases m03 : c03 = 0')
A('    · by_cases m13 : c13 = 0')
A('      · by_cases m23 : c23 = 0')
A('        · by_cases m34 : c34 = 0')
A('          · by_cases m35 : c35 = 0')
A('            · exact iso (%s) m03 m13 m23 m34 m35' % term(iso_at(3)))
A('            · exact disj (%s) n01 m35' % term(disj_at((0, 1), (3, 5))))
A('          · exact disj (%s) n01 m34' % term(disj_at((0, 1), (3, 4))))
A('        · exact disj (%s) n01 m23' % term(disj_at((0, 1), (2, 3))))
A('      · exact disj (%s) n02 m13' % term(disj_at((0, 2), (1, 3))))
A('    · exact key h n01 n02 m03')
A('')
A('/-- **The hafnian system has no fractional perfect matching.**  This is the')
A('whole combinatorial content of the orbit 17 no-go. -/')
A('theorem no_go (h : Sys %s) : False := by' % ARGS)
A('  by_cases n01 : c01 = 0')
A('  · by_cases n02 : c02 = 0')
A('    · by_cases n03 : c03 = 0')
A('      · by_cases n04 : c04 = 0')
A('        · by_cases n05 : c05 = 0')
A('          · exact iso h n01 n02 n03 n04 n05')
A('          · exact main1 (%s) n05' % term(find_perm([(0, 0), (1, 5)])))
A('        · exact main1 (%s) n04' % term(find_perm([(0, 0), (1, 4)])))
A('      · exact main1 (%s) n03' % term(find_perm([(0, 0), (1, 3)])))
A('    · exact main1 (%s) n02' % term(find_perm([(0, 0), (1, 2)])))
A('  · exact main1 h n01')
A('')
A('end')
A('')
A('end SixQubit.Hafnian')

out = 'SixQubit/Hafnian.lean'
with open(out, 'w', encoding='utf-8') as f:
    f.write('\n'.join(L) + '\n')
print('wrote', out, len(L), 'lines')
