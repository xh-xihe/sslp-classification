"""Orbit 25, the argument: pinning, hub links, the bottom relations, and the
diagonal contradiction.

Steps, all division-free:

  pin    ten of the squared-modulus consequences reduce to LINEAR relations
         modulo the moment ideal, and together they pin every probability to
         3/16 or 1/16;
  hub    each point a is tied to hub 0 by  u_0 v_{a-hat} + s_a u_a v_{0-hat} = 0,
         except a = 6, which needs one transitivity step through 9;
  bot    multiplying a cross relation by u_0 and substituting two hub relations
         cancels v_{0-hat} and leaves  u_0 u_{6+k} = u_k u_6;
  D      multiplying that by c_0 c_k gives  q_0 D_k = q_k A, so 3 D_k = A;
  E      multiplying two hub relations gives q_0 E_k = -r_{0-hat} D_{5-k}, so
         E_k = -D_{5-k};
  diag   the two dressings of X_1 give sum D_k = sum E_k, hence sum D_k = 0,
         hence (8/3) A = 0, against normSq A = q_0 q_6 = 9/256.
"""
import io
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from orbit import fiber
from scan import bits, xor, dot, dressings
from cert import build, reduce_mod_linear
from relations import analyse

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

OFF = sorted({e for i, j, k, l, sg, e in rel['direct'] + rel['derived']})
LNK = sorted({e for i, j, k, l, sg, e in rel['links']})
MASKS = sorted(set(OFF) | set(LNK) | {E1})
mid = {m: n for n, m in enumerate(MASKS)}
INC = {m: [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
       for m in MASKS}
ZS = {m: dressings(m) for m in MASKS}
zall = sorted({z for m in MASKS for z in ZS[m]})
zname = {z: ('w%d' % zall.index(z)) for z in zall}


def solve_row(m, tgt):
    M = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in INC[m]] for z in ZS[m]])
    sol = M.T.gauss_jordan_solve(sp.Matrix(tgt))[0]
    mu = sol.subs({p: 0 for p in sol.free_symbols})
    return [(ZS[m][u], sp.Rational(mu[u])) for u in range(len(ZS[m])) if mu[u] != 0]


def target(m, pairs):
    return [1 if (a, b) == pairs[0] else (pairs[2] if (a, b) == pairs[1] else 0)
            for a, b in INC[m]]


# hub links from 0
HUB = {}
for i, j, k, l, sg, e in rel['links']:
    if i == 0 and k != 0:
        HUB[k] = (e, sg, (0, hat[k]), (k, hat[0]))
    elif k == 0 and i != 0:
        HUB[i] = (e, sg, (0, hat[i]), (i, hat[0]))
assert set(HUB) == set(range(1, 12)) - {6}

# the cross relations that give u_0 u_{6+k} = u_k u_6
CROSS = {}
for i, j, k, l, sg, e in rel['direct'] + rel['derived']:
    if (i, k) == (0, 0):
        continue
    if i == 0 and 6 + 0 <= j and k in range(1, 6) and l == 6:
        CROSS[k] = (e, sg, (0, hat[j]), (k, hat[6]), j)
assert set(CROSS) == set(range(1, 6)), sorted(CROSS)

# the ten linear consequences that pin the probabilities
seen, LIN = set(), []
for i, j, k, l, sg, e in rel['direct'] + rel['derived']:
    key = tuple(sorted([(i, j), (k, l)]))
    if key in seen:
        continue
    seen.add(key)
    cof, rem = reduce_mod_linear(Q[i] * R[hat[j]] - Q[k] * R[hat[l]], V, Am, bv)
    if rem != 0 and sp.total_degree(sp.expand(rem)) <= 1:
        LIN.append((i, hat[j], k, hat[l], e, sg, sp.nsimplify(rem), cof))
PIN = [sp.Rational(3, 16)] + [sp.Rational(1, 16)] * 5 + [sp.Rational(3, 16)] \
      + [sp.Rational(1, 16)] * 5 + [sp.Rational(1, 16)] * 5 + [sp.Rational(3, 16)] \
      + [sp.Rational(1, 16)] * 5 + [sp.Rational(3, 16)]

L = []
W = L.append
W('/-! ## The moment system -/')
W('')
W('/-- The two normalizations, the twenty-one moment equalities, and the')
W('nonnegativity of every probability. -/')
qs = ' '.join('q%d' % k for k in range(n0))
rs = ' '.join('r%d' % k for k in range(n1))
W('structure MomentSystem (%s %s : Real) : Prop where' % (qs, rs))
for row in range(Am.rows):
    if enames[row] in ('n0', 'n1'):
        trm = ' + '.join(('q%d' % k) if k < n0 else ('r%d' % (k - n0))
                         for k in range(n0 + n1) if Am[row, k] != 0)
        W('  %s : %s = 1' % (enames[row], trm))
    else:
        lhs = ' + '.join('q%d' % k for k in range(n0) if Am[row, k] > 0) or '0'
        rhs = ' + '.join('r%d' % (k - n0) for k in range(n0, n0 + n1) if Am[row, k] < 0) or '0'
        W('  %s : %s = %s' % (enames[row], lhs, rhs))
W('')
for k in range(n0):
    W('  nq%d : 0 ≤ q%d' % (k, k))
for k in range(n1):
    W('  nr%d : 0 ≤ r%d' % (k, k))
W('')
for n, (i, ji, k, li, e, sg, rem, cof) in enumerate(LIN):
    W('set_option maxHeartbeats 2000000 in')
    W('/-- Squared-modulus consequence %d, reduced against the moment system. -/' % n)
    W('theorem lin%d {%s %s : Real} (h : MomentSystem %s %s)' % (n, qs, rs, qs, rs))
    W('    (hq : q%d * r%d = q%d * r%d) :' % (i, ji, k, li))
    W('    %s = 0 := by' % sp.printing.sstr(rem).replace('**', '^'))
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    terms = ['hq'] + ['(%s) * %s' % (sp.printing.sstr(-cof[row]).replace('**', '^'),
                                     enames[row])
                      for row in range(Am.rows) if cof[row] != 0]
    W('  linear_combination ' + ' + '.join(terms))
    W('')
W('set_option maxHeartbeats 4000000 in')
W('/-- The ten reduced consequences pin every probability. -/')
W('theorem pinned {%s %s : Real} (h : MomentSystem %s %s)' % (qs, rs, qs, rs))
for n, u in enumerate(LIN):
    W('    (v%d : %s = 0)' % (n, sp.printing.sstr(u[6]).replace('**', '^')))
W('    : ' + ' ∧ '.join('%s = %s' % (('q%d' % k) if k < n0 else ('r%d' % (k - n0)), PIN[k])
                        for k in range(n0 + n1)) + ' := by')
W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
W('  refine ⟨' + ', '.join('?_' for _ in range(n0 + n1)) + '⟩ <;> linarith')
W('')
W('/-! ## Walsh expansions -/')
W('')
for m in MASKS:
    nn = mid[m]
    ii = INC[m]
    if not ii:
        continue
    for z in ZS[m]:
        body = ' '.join('%s star (c y%d) * d z%d' % ('-' if dot(z, S1[t]) else '+', i, t)
                        for i, t in ii).lstrip('+ ')
        W('theorem ex%d_%s (c d : SS.BitString 6 -> ℂ) :' % (nn, zname[z]))
        W('    offSum c d ef%d %s = %s := by' % (nn, zname[z], body))
        W('  unfold offSum')
        W('  rw [incidence%d]' % nn)
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(ii) - 1))
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('fl%d_%d' % (nn, t) for _, t in ii) + ']')
        lem = ['sg%d_%s_%d' % (nn, zname[z], t) for _, t in ii]
        if any(dot(z, S1[t]) for _, t in ii):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S1[t]) for _, t in ii):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
W('/-! ## Hub links -/')
W('')
for x in sorted(HUB):
    e, sg, pa, pb = HUB[x]
    nn = mid[e]
    used = solve_row(e, target(e, (pa, pb, sg)))
    W('/-- Point y%d is tied to the hub y0. -/' % x)
    W('theorem hb%d (c d : SS.BitString 6 -> ℂ)' % x)
    for u, (z, mu) in enumerate(used):
        W('    (h%d : offSum c d ef%d %s = 0)' % (u, nn, zname[z]))
    W('    : star (c y0) * d z%d %s star (c y%d) * d z%d = 0 := by'
      % (hat[x], '+' if sg == 1 else '-', x, hat[0]))
    for u, (z, mu) in enumerate(used):
        W('  rw [ex%d_%s] at h%d' % (nn, zname[z], u))
    W('  linear_combination ' + ' + '.join(
        '(%s : ℂ) * h%d' % (mu, u) for u, (z, mu) in enumerate(used)))
    W('')
io.open('gen15b_body.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('body: %d lines; hub links %s; cross %s; linear pins %d'
      % (len(L), sorted(HUB), sorted(CROSS), len(LIN)))
print('masks:', MASKS)
