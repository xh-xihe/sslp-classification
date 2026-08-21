"""End-to-end Step A (fixed normalisation) + exact scalar content of the weight-1 masks."""
from stepA_audit import *          # noqa
import sympy as sp

cb = {(i, a): sp.Symbol('cb%d_%d' % (i, a)) for i in range(8) for a in (0, 1)}
d = {(i, a): sp.Symbol('d%d_%d' % (i, a)) for i in range(8) for a in (0, 1)}
PAIRS = [(0, 1), (0, 2), (1, 2)]


def canon_labs(g, h, a, b):
    return [(2 * g + c, a, 2 * h + 1 - c, b) for c in (0, 1)] \
         + [(2 * h + c, a, 2 * g + 1 - c, b) for c in (0, 1)]


print('=' * 78)
print('DIRECT MEMBERSHIP TEST of each canonical R1 entry E_ab in the Walsh row space')
allok = True
for (g, h) in PAIRS:
    for a in (0, 1):
        for b in (0, 1):
            ok, m = implied({l: 1 for l in canon_labs(g, h, a, b)})
            allok &= bool(ok)
            # the omega = -1 variant
            v = {}
            for c in (0, 1):
                v[(2 * g + c, a, 2 * h + 1 - c, b)] = 1
                v[(2 * h + c, a, 2 * g + 1 - c, b)] = -1
            okm, _ = implied(v)
            # the symplectic variant (internal sign -1)
            w = {}
            for c in (0, 1):
                w[(2 * g + c, a, 2 * h + 1 - c, b)] = (-1) ** c
                w[(2 * h + c, a, 2 * g + 1 - c, b)] = (-1) ** c
            oks, _ = implied(w)
            print('  (%d,%d)[%d,%d] mask %s : omega=+1 implied %s | omega=-1 implied %s | symplectic implied %s'
                  % (g, h, a, b, m, ok, okm, oks))
print('  every canonical E_ab implied:', allok)

print('=' * 78)
print('END-TO-END STEP A on the canonical relations')
for j in (6, 7):
    X = {i: sp.expand(sum(cb[(j, b)] * d[(i, b)] for b in (0, 1))) for i in range(6)}
    Y = {i: sp.expand(sum(cb[(i, a)] * d[(j, a)] for a in (0, 1))) for i in range(6)}
    for (g, h) in PAIRS:
        S = 0
        for a in (0, 1):
            for b in (0, 1):
                E = sum(cb[(l[0], l[1])] * d[(l[2], l[3])] for l in canon_labs(g, h, a, b))
                S += d[(j, a)] * cb[(j, b)] * E
        S = sp.expand(S)
        tgt = sp.expand(sum(Y[2 * g + c] * X[2 * h + 1 - c] for c in (0, 1))
                        + sum(Y[2 * h + c] * X[2 * g + 1 - c] for c in (0, 1)))
        sub = sp.expand(-sum(X[2 * g + c] * X[2 * h + 1 - c] for c in (0, 1))
                        - sum(X[2 * h + c] * X[2 * g + 1 - c] for c in (0, 1)))
        want = sp.expand(-2 * (X[2 * g] * X[2 * h + 1] + X[2 * g + 1] * X[2 * h]))
        print('  anchor %d pair (%d,%d): contraction = sum_c Y X  : %s ;  with Y=-X it is -2(X%dX%d+X%dX%d): %s ;  that target nonzero: %s'
              % (j, g, h, sp.expand(S - tgt) == 0, 2 * g, 2 * h + 1, 2 * g + 1, 2 * h,
                 sp.expand(sub - want) == 0, want != 0))

print('=' * 78)
print('EXACT SCALAR CONTENT of the three weight-one masks (s = block inner product)')
for m in ['010000', '001000', '000001']:
    pairs = sorted({(l[0], l[2]) for l in INC[m]})
    n = len(INC[m])
    B = RS[m]

    def basisvec(p, kind):
        v = sp.zeros(1, n)
        for a in (0, 1):
            v[0, COL[m][(p[0], a, p[1], a)]] = 1 if (kind == 's' or a == 0) else -1
        return v
    SB = sp.Matrix([list(basisvec(p, 's')) for p in pairs])
    EB = sp.Matrix([list(basisvec(p, 'e')) for p in pairs])
    for nm, M in (('s', SB), ('e', EB)):
        # relations in rowspace(B) that lie in rowspace(M): solve lam B = mu M
        r, k = B.rows, M.rows
        lam = sp.symbols('L0:%d' % r)
        mu = sp.symbols('M0:%d' % k)
        eqs = [sp.Eq(sum(lam[i] * B[i, c] for i in range(r))
                     - sum(mu[i] * M[i, c] for i in range(k)), 0) for c in range(n)]
        sol = sp.solve(eqs, list(lam) + list(mu), dict=True)[0]
        free = sorted({t for e in sol.values() for t in e.free_symbols} |
                      ({sp.Symbol(str(x)) for x in list(lam) + list(mu)} - set(sol)), key=str)
        vecs = []
        for f in free:
            sb = {t: (1 if t == f else 0) for t in free}
            row = [sp.simplify(sol.get(mu[i], mu[i]).subs(sb)) for i in range(k)]
            if any(x != 0 for x in row):
                vecs.append(row)
        R = sp.Matrix(vecs).rref()[0] if vecs else sp.zeros(0, k)
        R = sp.Matrix([list(R[i, :]) for i in range(R.rows) if any(R[i, c] != 0 for c in range(k))])
        print('  mask %s  %s-relations: dim %d   (variables %s)'
              % (m, nm, R.rows, ['%s%s' % (nm, p) for p in pairs]))
        for i in range(R.rows):
            print('      ' + ' '.join('%+s*%s%s' % (sp.nsimplify(R[i, c]), nm, pairs[c])
                                      for c in range(k) if R[i, c] != 0) + ' = 0')
