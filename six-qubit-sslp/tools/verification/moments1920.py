"""Exact-rational confirmation that the derived-probability lemmas of orbits 19
and 20 really are consequences of the weight-<=2 pure-Z moment rows.

Orbit 19: `MomentSystem.anchors` claims P0 = Q0, P4 = Q4 and P0 + P4 = 1/2.
Orbit 20: `MomentSystem.blockMass` claims the four bottom/top block masses agree,
and `MomentSystem.uniform` claims that adjoining the sixteen complement-matching
equalities makes every block uniform, with 4*(a_000+a_011+a_101+a_110) = 1.

A functional f is "pinned to k" when lam^T A = f is solvable over Q and
lam^T b = k, i.e. f is constant equal to k on the whole affine solution set.
`None` means f is NOT determined by the system -- printed for P0 alone as a
control, to show the test can fail.

The Lean proofs are the real certificates; this is an independent cross-check.
"""
from itertools import combinations

import sympy as sp

N = 6


def fiber(a, q, res):
    return [format(k, '06b') for k in range(1 << N)
            if sum(a[i] for i in range(N) if format(k, '06b')[i] == '1') % q == res]


def xor(s, t):
    return ''.join('1' if (s[i] == '1') != (t[i] == '1') else '0' for i in range(N))


def base(S0, S1):
    n0, n1 = len(S0), len(S1)
    R, b = [], []
    R.append([1] * n0 + [0] * n1)
    b.append(sp.Integer(1))
    R.append([0] * n0 + [1] * n1)
    b.append(sp.Integer(1))
    for T in [(i,) for i in range(6)] + list(combinations(range(6), 2)):
        R.append([1 if all(x[j] == '1' for j in T) else 0 for x in S0]
                 + [-1 if all(y[j] == '1' for j in T) else 0 for y in S1])
        b.append(sp.Integer(0))
    return R, b


def pinned(R, b, f):
    A, bb = sp.Matrix(R), sp.Matrix(b)
    if A.rank() != A.col_join(sp.Matrix([list(f)])).rank():
        return None
    lam = sp.symbols('t0:%d' % A.rows)
    s = list(sp.linsolve((A.T, sp.Matrix(list(f))), lam))[0]
    s = [v.subs({x: 0 for x in lam}) for v in s]
    return sum(s[i] * bb[i] for i in range(A.rows))


def orbit19():
    a = [1, 1, 1, 1, 2, 2]
    S0, S1 = fiber(a, 4, 0), fiber(a, 4, 2)
    n0 = len(S0)
    R, b = base(S0, S1)
    print('=== orbit 19  a=%s  rank %d ===' % (a, sp.Matrix(R).rank()))

    def ev(bots, tops):
        f = [0] * (n0 + len(S1))
        for s in bots:
            f[S0.index(s)] += 1
        for s in tops:
            f[n0 + S1.index(s)] += 1
        return f

    P0, P4 = ['000000', '000011'], ['111100', '111111']
    Q0, Q4 = ['000001', '000010'], ['111101', '111110']
    sub = lambda u, v: [x - y for x, y in zip(u, v)]
    print('  P0 - Q0   pinned to', pinned(R, b, sub(ev(P0, []), ev([], Q0))))
    print('  P4 - Q4   pinned to', pinned(R, b, sub(ev(P4, []), ev([], Q4))))
    print('  P0 + P4   pinned to', pinned(R, b, ev(P0 + P4, [])))
    print('  Q0 + Q4   pinned to', pinned(R, b, ev([], Q0 + Q4)))
    print('  P0 alone  pinned to', pinned(R, b, ev(P0, [])), '  (control: not pinned)')


def orbit20():
    a = [1, 1, 1, 2, 2, 2]
    S0, S1 = fiber(a, 4, 0), fiber(a, 4, 2)
    n0, n1 = len(S0), len(S1)
    heads = []
    for x in S0:
        if x[:3] not in heads:
            heads.append(x[:3])
    blocks = [(r, [i for i in range(n0) if S0[i][:3] == r]) for r in heads]
    match = {i: S1.index(xor(S0[i], '000111')) for i in range(n0)}
    R, b = base(S0, S1)
    print('=== orbit 20  a=%s  rank %d ===' % (a, sp.Matrix(R).rank()))
    for r, bs in blocks:
        f = [0] * (n0 + n1)
        for i in bs:
            f[i] += 1
            f[n0 + match[i]] -= 1
        print('  block %s  bottom mass - top mass  pinned to %s' % (r, pinned(R, b, f)))
    R2, b2 = list(R), list(b)
    for i in range(n0):
        row = [0] * (n0 + n1)
        row[i], row[n0 + match[i]] = 1, -1
        R2.append(row)
        b2.append(sp.Integer(0))
    print('  augmented rank %d' % sp.Matrix(R2).rank())
    bad = []
    for r, bs in blocks:
        for i, j in combinations(bs, 2):
            f = [0] * (n0 + n1)
            f[i], f[j] = 1, -1
            if pinned(R2, b2, f) != 0:
                bad.append((i, j))
    print('  every within-block difference p_i - p_j pinned to 0:', not bad)
    f = [0] * (n0 + n1)
    for r, bs in blocks:
        f[bs[0]] = 4
    print('  4*(a_000 + a_011 + a_101 + a_110) pinned to', pinned(R2, b2, f))


if __name__ == '__main__':
    orbit19()
    print()
    orbit20()
