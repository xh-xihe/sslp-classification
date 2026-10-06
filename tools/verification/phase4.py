"""Phase 4: orbits with a zero-angle (or effective repetition) qubit, where the
KL rows isolate a C^2 INNER PRODUCT

    <c_x , d_y> = conj(c_{0x}) d_{0y} + conj(c_{1x}) d_{1y}

rather than a single monomial.  Search for such isolations and report which
orbits become closable by frame arguments.
"""
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, 'tools/core')
sys.path.insert(0, '.')
from orbit import fiber

ORB = [(13, 4, [0, 1, 1, 1, 2, 2], 2), (12, 4, [0, 1, 1, 1, 1, 2], 2),
       (14, 4, [0, 1, 1, 2, 2, 2], 2), (15, 4, [0, 1, 2, 2, 2, 2], 2),
       (6, 3, [0, 1, 1, 1, 1, 1], 1), (5, 3, [0, 0, 1, 1, 1, 1], 1),
       (24, 4, [1, 2, 2, 2, 2, 3], 2), (20, 4, [1, 1, 1, 2, 2, 2], 2),
       (19, 4, [1, 1, 1, 1, 2, 2], 2), (17, 4, [1, 1, 1, 1, 1, 1], 2)]

bits = lambda s: [int(c) for c in s]
xor = lambda s, t: ''.join('01'[bits(s)[i] ^ bits(t)[i]] for i in range(6))
supp = lambda s: {i for i, c in enumerate(s) if c == '1'}
dot = lambda z, x: sum(bits(z)[i] * bits(x)[i] for i in range(6)) % 2
ALL = [format(k, '06b') for k in range(64)]
dress = lambda e: [z for z in ALL if len(supp(e) | supp(z)) <= 2]

for oid, q, a, d in ORB:
    S0, S1 = fiber(a, q, 0), fiber(a, q, d)
    # which coordinate is "free" (both values occur for every other pattern)?
    frees = []
    for j in range(6):
        ok = True
        for F in (S0, S1):
            tails = {}
            for s in F:
                tails.setdefault(s[:j] + s[j + 1:], set()).add(s[j])
            if any(len(v) != 2 for v in tails.values()):
                ok = False
        if ok:
            frees.append(j)
    if not frees:
        print('orbit %-3d  no free qubit -> not a C^2 orbit' % oid)
        continue
    j = frees[0]
    hits = 0
    detail = []
    for e in ALL:
        if not 1 <= len(supp(e)) <= 2 or e[j] == '1':
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        if not inc:
            continue
        Z = dress(e)
        W = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in Z])
        # group incidences into pairs differing only in coordinate j
        grp = {}
        for k, (i2, t2) in enumerate(inc):
            key = (S0[i2][:j] + S0[i2][j + 1:], S1[t2][:j] + S1[t2][j + 1:])
            grp.setdefault(key, []).append(k)
        for key, ks in grp.items():
            if len(ks) != 2:
                continue
            k1, k2 = ks
            if dot('0' * 6, S1[inc[k1][1]]):
                pass
            tgt = sp.Matrix([1 if r in ks else 0 for r in range(len(inc))])
            try:
                W.T.gauss_jordan_solve(tgt)
            except ValueError:
                continue
            hits += 1
            if len(detail) < 3:
                detail.append((e, key))
    print('orbit %-3d  free qubit %d, %3d isolable C^2 inner products   %s'
          % (oid, j + 1, hits,
             ' '.join('%s:%s|%s' % (e, k[0], k[1]) for e, k in detail)))
