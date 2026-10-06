"""End-to-end: run Step A symbolically off the ACTUAL relation vectors."""
from stepA_audit import *          # noqa
import sympy as sp

cb = {(i, a): sp.Symbol('cb%d_%d' % (i, a)) for i in range(8) for a in (0, 1)}
d = {(i, a): sp.Symbol('d%d_%d' % (i, a)) for i in range(8) for a in (0, 1)}
PAIRS = [(0, 1), (0, 2), (1, 2)]


def poly_of(m, v):
    """turn a relation vector on mask m into a polynomial in cb, d"""
    return sp.expand(sum(v[0, k] * cb[(INC[m][k][0], INC[m][k][1])]
                         * d[(INC[m][k][2], INC[m][k][3])] for k in range(v.cols)))


def actual_R1(g, h, a, b):
    labs = []
    for c in (0, 1):
        labs.append((2 * g + c, a, 2 * h + 1 - c, b))
        labs.append((2 * h + c, a, 2 * g + 1 - c, b))
    m = mask_of(*labs[0])
    rels = relations_supported_on(m, labs)
    assert len(rels) == 1
    return m, rels[0]


print('=' * 78)
print('END-TO-END STEP A, using the relation vectors as computed (no idealisation)')
for j in (6, 7):
    X = {i: sp.expand(sum(cb[(j, b)] * d[(i, b)] for b in (0, 1))) for i in range(6)}
    Y = {i: sp.expand(sum(cb[(i, a)] * d[(j, a)] for a in (0, 1))) for i in range(6)}
    for (g, h) in PAIRS:
        S = 0
        for a in (0, 1):
            for b in (0, 1):
                m, v = actual_R1(g, h, a, b)
                S += d[(j, a)] * cb[(j, b)] * poly_of(m, v) / v[0, 0]   # normalise
        S = sp.expand(S)
        tgt = sp.expand(sum(Y[2 * g + c] * X[2 * h + 1 - c] for c in (0, 1))
                        + sum(Y[2 * h + c] * X[2 * g + 1 - c] for c in (0, 1)))
        # with the verified R2 substitution Y_i = -X_i
        tgtJ = sp.expand(-2 * (X[2 * g] * X[2 * h + 1] + X[2 * g + 1] * X[2 * h]))
        print('  anchor %d pair (%d,%d): contraction == sum Y X  : %s'
              % (j, g, h, sp.simplify(S - tgt) == 0))
        print('     after Y_i = -X_i, contraction == -2(X_%dX_%d + X_%dX_%d) : %s   (identically zero? %s)'
              % (2 * g, 2 * h + 1, 2 * g + 1, 2 * h,
                 sp.simplify(sp.expand(tgt.subs({Y[i]: -X[i] for i in range(6)})) - tgtJ) == 0
                 if False else sp.simplify(
                     sp.expand(sum(-X[2 * g + c] * X[2 * h + 1 - c] for c in (0, 1))
                               + sum(-X[2 * h + c] * X[2 * g + 1 - c] for c in (0, 1))) - tgtJ) == 0,
                 tgtJ == 0))

print('=' * 78)
print('BONUS: the full scalar content of the three weight-one masks.')
print('  s(b,t) := C_b^dag D_t = sum_a cc((C_b)_a)(D_t)_a   (block-to-block inner product)')
print('  e(b,t) := cc((C_b)_0)(D_t)_0 - cc((C_b)_1)(D_t)_1')
for m in ['010000', '001000', '000001']:
    pairs = sorted({(l[0], l[2]) for l in INC[m]})
    n = len(INC[m])

    def vec(co):
        v = sp.zeros(1, n)
        for (bt, kind), q in co.items():
            for a in (0, 1):
                v[0, COL[m][(bt[0], a, bt[1], a)]] += q * (1 if kind == 's' or a == 0 else -1)
        return v
    B = RS[m]
    inrs = lambda v: B.rank() == B.col_join(v).rank()
    print('  mask %s, block pairs %s' % (m, pairs))
    # every two-term and one-term s / e combination
    for kind in ('s', 'e'):
        for p in pairs:
            if inrs(vec({(p, kind): 1})):
                print('     %s%s = 0' % (kind, p))
        for x in range(len(pairs)):
            for y in range(x + 1, len(pairs)):
                for sg in (1, -1):
                    if inrs(vec({(pairs[x], kind): 1, (pairs[y], kind): sg})):
                        print('     %s%s %s %s%s = 0'
                              % (kind, pairs[x], '+' if sg > 0 else '-', kind, pairs[y]))
    # dimension of the s-part and e-part of the relation space
    sv = sp.Matrix([list(vec({(p, 's'): 1})) for p in pairs])
    ev = sp.Matrix([list(vec({(p, 'e'): 1})) for p in pairs])
    for nm, M in (('s', sv), ('e', ev)):
        keep = [k for k in range(n) if any(M[r, k] != 0 for r in range(M.rows))]
        lam = B[:, [k for k in range(n) if k not in keep]].T.nullspace() if keep != list(range(n)) else []
        print('     dim(relations lying purely in the %s-subspace) = %d'
              % (nm, len(sp.Matrix([[sum(l[i] * B[i, k] for i in range(B.rows))
                                     for k in range(n)] for l in lam]).rowspace()) if lam else 0))
