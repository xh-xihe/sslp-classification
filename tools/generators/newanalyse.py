"""For each of the 22 newly excluded orbits, search for an ISOLATION
CERTIFICATE:

  a flip mask e, a set of admissible dressings z, and exact rational
  multipliers mu with   sum_z mu_z * (row of z)  =  indicator of one
  incidence k,

so the KL equations force that single monomial to vanish, while the moment
polytope keeps both of its endpoint probabilities bounded away from zero.

Output feeds the Lean generator directly.
"""
import io
import json
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
from orbit import fiber

ORB = [
    (5, 3, [0, 0, 1, 1, 1, 1], 1), (6, 3, [0, 1, 1, 1, 1, 1], 1),
    (47, 6, [1, 1, 1, 1, 2, 2], 2), (48, 6, [1, 1, 1, 2, 2, 2], 2),
    (49, 6, [1, 1, 1, 3, 3, 5], 2), (50, 6, [1, 1, 1, 3, 4, 4], 2),
    (51, 6, [1, 1, 2, 3, 3, 4], 2), (52, 6, [1, 2, 3, 3, 4, 4], 2),
    (12, 4, [0, 1, 1, 1, 1, 2], 2), (13, 4, [0, 1, 1, 1, 2, 2], 2),
    (14, 4, [0, 1, 1, 2, 2, 2], 2), (15, 4, [0, 1, 2, 2, 2, 2], 2),
    (17, 4, [1, 1, 1, 1, 1, 1], 2), (18, 4, [1, 1, 1, 1, 1, 2], 2),
    (19, 4, [1, 1, 1, 1, 2, 2], 2), (20, 4, [1, 1, 1, 2, 2, 2], 2),
    (24, 4, [1, 2, 2, 2, 2, 3], 2), (41, 6, [1, 1, 1, 1, 2, 3], 3),
    (42, 6, [1, 1, 1, 1, 3, 3], 3), (43, 6, [1, 1, 1, 2, 3, 3], 3),
    (44, 6, [1, 1, 2, 3, 3, 4], 3), (46, 6, [1, 2, 2, 2, 3, 3], 3),
]

bits = lambda s: [int(ch) for ch in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
supp = lambda s: {i for i, ch in enumerate(s) if ch == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]


def dressings(e):
    """Every z with |supp(e) u supp(z)| <= 2 -- the corrected rule."""
    return [z for z in ALL if len(supp(e) | supp(z)) <= 2]


def momentmat(S0, S1):
    n0, n1 = len(S0), len(S1)
    rows, rhs = [[1] * n0 + [0] * n1, [0] * n0 + [1] * n1], [1, 1]
    for T in [(i,) for i in range(6)] + list(combinations(range(6), 2)):
        chi = lambda z: (-1) ** sum(bits(z)[i] for i in T)
        rows.append([chi(x) for x in S0] + [-chi(y) for y in S1])
        rhs.append(0)
    return sp.Matrix(rows), sp.Matrix(rhs)


def forced_positive(S0, S1, M, rhs):
    """Exact minimum of each coordinate over {Mv=rhs, v>=0} via vertex
    enumeration is too slow; instead solve the affine system symbolically and
    read off which coordinates are constant, then check that constant."""
    n = M.cols
    v = sp.Matrix(sp.symbols('t0:%d' % n))
    sol = sp.solve([sp.Eq(a, b) for a, b in zip(M * v, rhs)], list(v), dict=True)
    if not sol:
        return {}
    sol = sol[0]
    out = {}
    for k in range(n):
        e = sp.simplify(sol.get(v[k], v[k]))
        if e.is_number:
            out[k] = sp.Rational(e)
    return out


def certificate(S0, S1, const):
    """Search every weight<=2 flip mask for an isolable incidence whose two
    endpoint probabilities are forced positive constants."""
    n0 = len(S0)
    best = None
    for e in ALL:
        if not 1 <= len(supp(e)) <= 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1)
               if xor(y, e) in S0]
        if not inc:
            continue
        Z = dressings(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        for k, (i, t) in enumerate(inc):
            pk, qk = const.get(i), const.get(n0 + t)
            if pk is None or qk is None or pk <= 0 or qk <= 0:
                continue
            tgt = sp.Matrix([1 if r == k else 0 for r in range(len(inc))])
            try:
                mu = W.T.gauss_jordan_solve(tgt)[0]
            except ValueError:
                continue
            mu = mu.subs({s: 0 for s in mu.free_symbols})
            used = [(Z[r], sp.Rational(mu[r])) for r in range(len(Z))
                    if mu[r] != 0]
            cand = (len(inc), len(used), e, k, i, t, pk, qk, used)
            if best is None or (len(used), len(inc)) < (best[1], best[0]):
                best = cand
    return best


res = {}
for oid, q, a, d in ORB:
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    M, rhs = momentmat(S0, S1)
    const = forced_positive(S0, S1, M, rhs)
    cert = certificate(S0, S1, const)
    if cert:
        ninc, nused, e, k, i, t, pk, qk, used = cert
        print('orbit %-3d  %2d+%-2d  flip %s  %2d incidences  isolate #%d '
              '(%s,%s)  p=%s q=%s  via %d dressings'
              % (oid, len(S0), len(S1), e, ninc, k, S0[i], S1[t], pk, qk, nused))
        res[oid] = dict(q=q, a=a, d=d, S0=S0, S1=S1, e=e, k=k, i=i, t=t,
                        inc=[(S0.index(xor(y, e)), tt)
                             for tt, y in enumerate(S1) if xor(y, e) in S0],
                        used=[(z, str(m)) for z, m in used],
                        pk=str(pk), qk=str(qk),
                        const={str(kk): str(vv) for kk, vv in const.items()})
    else:
        print('orbit %-3d  %2d+%-2d  NO isolation certificate  '
              '(%d forced constants)  -> needs an algebra layer'
              % (oid, len(S0), len(S1), len(const)))
io.open('newcerts.json', 'w', encoding='utf-8').write(json.dumps(res, indent=1))
print()
print('isolation certificates found for %d of %d orbits' % (len(res), len(ORB)))
print('  ->', sorted(res))
