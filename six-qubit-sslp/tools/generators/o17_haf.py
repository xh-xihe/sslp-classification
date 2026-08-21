"""Orbit 17: the hafnian ideal.

Variables c_e for the 15 edges of K_6.  Generators
    H_{ijkl} = c_ij c_kl + c_ik c_jl + c_il c_jk        (15 four-sets)

Question 1: is the degree-3 monomial c_01 c_23 c_0e in the degree-3 part of the
ideal, for the edges e at the two vertices left over?  A positive answer gives a
`linear_combination` certificate directly.
"""
from fractions import Fraction as F
from itertools import combinations

EDGES = list(combinations(range(6), 2))
EI = {e: k for k, e in enumerate(EDGES)}


def ed(i, j):
    return EI[(i, j) if i < j else (j, i)]


FOURSETS = list(combinations(range(6), 4))


def hafnian(fs):
    """list of (edge index, edge index) monomials"""
    i, j, k, l = fs
    return [(ed(i, j), ed(k, l)), (ed(i, k), ed(j, l)), (ed(i, l), ed(j, k))]


# ---- degree-3 monomial basis in 15 variables -------------------------------
MON3 = list(combinations(range(15), 3)) + [(a, a, b) for a in range(15) for b in range(15) if a != b] + [(a, a, a) for a in range(15)]


def key3(t):
    return tuple(sorted(t))


MON3 = sorted({key3(m) for m in MON3})
M3I = {m: k for k, m in enumerate(MON3)}
print('degree-3 monomials:', len(MON3))

# ---- generators of the degree-3 part: c_e * H_Q -----------------------------
GENS = []
GLAB = []
for e in range(15):
    for fs in FOURSETS:
        vec = {}
        for (a, b) in hafnian(fs):
            k = M3I[key3((e, a, b))]
            vec[k] = vec.get(k, 0) + 1
        GENS.append(vec)
        GLAB.append((e, fs))
print('degree-3 generators:', len(GENS))


def solve_membership(target_vec, gens):
    """Exact Gaussian elimination: express target as rational combo of gens.
    Returns coefficient list or None."""
    rows = []
    for g in gens:
        rows.append(dict(g))
    # build augmented system: unknowns = coefficients of gens
    # equations indexed by monomials
    monset = set()
    for g in gens:
        monset |= set(g)
    monset |= set(target_vec)
    mons = sorted(monset)
    mi = {m: k for k, m in enumerate(mons)}
    nrow = len(mons)
    ncol = len(gens)
    # matrix A[nrow][ncol], rhs
    A = [[F(0)] * ncol for _ in range(nrow)]
    for c, g in enumerate(gens):
        for m, v in g.items():
            A[mi[m]][c] = F(v)
    rhs = [F(0)] * nrow
    for m, v in target_vec.items():
        rhs[mi[m]] = F(v)
    # gaussian elimination
    piv = []
    r = 0
    for c in range(ncol):
        p = None
        for rr in range(r, nrow):
            if A[rr][c] != 0:
                p = rr
                break
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        rhs[r], rhs[p] = rhs[p], rhs[r]
        inv = F(1) / A[r][c]
        A[r] = [x * inv for x in A[r]]
        rhs[r] = rhs[r] * inv
        for rr in range(nrow):
            if rr != r and A[rr][c] != 0:
                f = A[rr][c]
                A[rr] = [a - f * bb for a, bb in zip(A[rr], A[r])]
                rhs[rr] -= f * rhs[r]
        piv.append(c)
        r += 1
        if r == nrow:
            break
    # check consistency
    for rr in range(r, nrow):
        if rhs[rr] != 0 and all(A[rr][c] == 0 for c in range(ncol)):
            return None
    coeff = [F(0)] * ncol
    for k, c in enumerate(piv):
        coeff[c] = rhs[k]
    # verify
    chk = {}
    for c, g in enumerate(gens):
        if coeff[c] == 0:
            continue
        for m, v in g.items():
            chk[m] = chk.get(m, F(0)) + coeff[c] * v
    chk = {m: v for m, v in chk.items() if v != 0}
    tgt = {m: F(v) for m, v in target_vec.items() if v != 0}
    if chk != tgt:
        return None
    return coeff


if __name__ == '__main__':
    tests = []
    base = (ed(0, 1), ed(2, 3))
    for f in EDGES:
        if 4 in f or 5 in f:
            tests.append(f)
    for f in tests:
        tgt = {M3I[key3((base[0], base[1], ed(*f)))]: 1}
        co = solve_membership(tgt, GENS)
        if co is None:
            print('c01*c23*c%d%d : NOT in degree-3 ideal' % f)
        else:
            nz = [(GLAB[k], v) for k, v in enumerate(co) if v != 0]
            print('c01*c23*c%d%d : IN, %d terms' % (f + (len(nz),)))
