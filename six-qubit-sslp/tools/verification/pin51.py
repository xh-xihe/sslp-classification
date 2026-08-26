"""Orbits 49 and 51: two-term relations give quadratic consequences
p_i q_j = p_k q_l which pin the moment polytope; a triangle then closes.

Here we (a) list every genuine two-term relation, (b) turn each into its
quadratic consequence, (c) see how far those pin the polytope, and (d) check
whether a reciprocal triangle survives on the pinned point.
"""
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
sys.path.insert(0, '.')
from orbit import fiber

bits = lambda s: [int(c) for c in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
comp = lambda s: ''.join('01'[1 - int(c)] for c in s)
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]

for oid, q, a, d in ((51, 6, [1, 1, 2, 3, 3, 4], 2), (49, 6, [1, 1, 1, 3, 3, 5], 2)):
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    n0, n1 = len(S0), len(S1)
    top = {r: S1.index(comp(S0[r])) for r in range(n0)}
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
    free = sorted({y for e in expr for y in e.free_symbols}, key=lambda y: y.name)

    # every genuine two-term relation, with its sign
    two = []
    for e in ALL:
        if not 1 <= len(supp(e)) <= 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        if len(inc) < 2:
            continue
        Z = dress(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        for k1, k2 in combinations(range(len(inc)), 2):
            for sg in (1, -1):
                tgt = sp.Matrix([1 if r == k1 else (sg if r == k2 else 0)
                                 for r in range(len(inc))])
                try:
                    mu = W.T.gauss_jordan_solve(tgt)[0]
                except ValueError:
                    continue
                mu = mu.subs({s: 0 for s in mu.free_symbols})
                used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z))
                        if mu[r] != 0]
                two.append((e, inc[k1], inc[k2], sg, used))
                break
    print('orbit %d: %d free moment parameters, %d two-term relations'
          % (oid, len(free), len(two)))

    # quadratic consequences  p_i q_j = p_k q_l
    quad = set()
    for e, (i1, t1), (i2, t2), sg, used in two:
        lhs = sp.expand(expr[i1] * expr[n0 + t1] - expr[i2] * expr[n0 + t2])
        if lhs != 0:
            quad.add(sp.simplify(lhs))
    quad = [x for x in quad if x != 0]
    print('   %d nontrivial quadratic consequences' % len(quad))
    sols = sp.solve(quad, free, dict=True)
    print('   solving them pins the polytope to %d point(s)' % len(sols))
    for sset in sols[:4]:
        pt = [sp.simplify(e.subs(sset)) for e in expr]
        okdom = all(x.is_number and x >= 0 for x in pt)
        if not okdom:
            print('      -> %s  (leaves free params or negative)' % sset)
            continue
        print('      -> bottom probabilities %s' % pt[:n0])
        act = [k for k in range(n0) if pt[k] > 0]
        # reciprocal MINUS pairs among the active indices
        rec = set()
        for e, (i1, t1), (i2, t2), sg, used in two:
            if sg == 1 and top[i1] == t2 and top[i2] == t1:
                rec.add((min(i1, i2), max(i1, i2)))
        tri = [t for t in combinations(act, 3)
               if all(tuple(sorted(p)) in rec for p in combinations(t, 2))]
        print('         active %s, reciprocal pairs %d, triangles %s'
              % (act, len(rec), tri[:3] if tri else 'NONE'))
