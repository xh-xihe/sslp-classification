"""Verified-facts model for orbit 26 as real quadratic forms (exact Jacobian).

x in R^64:   Re C_i[a] = x[4i+a],   Im C_i[a] = x[4i+2+a],
             Re D_i[a] = x[32+4i+a], Im D_i[a] = x[32+4i+2+a].

Facts:
  (M)  C_g C_g^dag + D_g D_g^dag = rho/2 for the four groups, rho = sum_g C_g C_g^dag
  (N)  tr rho = 1
  (E)  P_i = Q_i
  (A)  P_6 = P_7 = 1/8
  (T2) P_0+P_2+P_4 = 3/8 = Q_0+Q_2+Q_4
  (R1) conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0,  0 <= g < h <= 2
  (R2) C_j^dag D_i + C_i^dag D_j = 0,  i <= 5, j in {6,7}
Optional:
  (R3) the SIX weight-one scalar relations that R1 u R2 do not imply.
"""
import numpy as np
from scipy.optimize import least_squares

N = 64
GROUPS = [[0, 1], [2, 3], [4, 5], [6, 7]]
cR = lambda i, a: 4 * i + a
cI = lambda i, a: 4 * i + 2 + a
dR = lambda i, a: 32 + 4 * i + a
dI = lambda i, a: 32 + 4 * i + 2 + a


def blank():
    return {}


def addt(t, p, q, w):
    t[(p, q)] = t.get((p, q), 0.0) + w


def cc(t, i, a, b, w):          # w * (C_i C_i^dag)_{ab}  -> (re, im)
    pass


def cc_re(t, i, a, b, w):
    addt(t, cR(i, a), cR(i, b), w); addt(t, cI(i, a), cI(i, b), w)


def cc_im(t, i, a, b, w):
    addt(t, cI(i, a), cR(i, b), w); addt(t, cR(i, a), cI(i, b), -w)


def dd_re(t, i, a, b, w):
    addt(t, dR(i, a), dR(i, b), w); addt(t, dI(i, a), dI(i, b), w)


def dd_im(t, i, a, b, w):
    addt(t, dI(i, a), dR(i, b), w); addt(t, dR(i, a), dI(i, b), -w)


def cd_re(t, k, a, l, b, w):    # w * conj(C_k[a]) D_l[b]
    addt(t, cR(k, a), dR(l, b), w); addt(t, cI(k, a), dI(l, b), w)


def cd_im(t, k, a, l, b, w):
    addt(t, cR(k, a), dI(l, b), w); addt(t, cI(k, a), dR(l, b), -w)


def mat(t):
    M = np.zeros((N, N))
    for (p, q), w in t.items():
        M[p, q] += w / 2.0
        M[q, p] += w / 2.0
    return M


def build(extra_zero=(), use_R3=False):
    """extra_zero: iterable of (anchor j, block i) meaning C_j^dag D_i = 0."""
    Ms, cs = [], []

    def push(t, const=0.0):
        Ms.append(mat(t)); cs.append(const)

    # (M) group identity, Hermitian 2x2 -> 4 real residuals per group
    for g in range(4):
        for (a, b, part) in [(0, 0, 're'), (1, 1, 're'), (0, 1, 're'), (0, 1, 'im')]:
            t = blank()
            f_c = cc_re if part == 're' else cc_im
            f_d = dd_re if part == 're' else dd_im
            for i in GROUPS[g]:
                f_c(t, i, a, b, 1.0); f_d(t, i, a, b, 1.0)
            for i in range(8):
                f_c(t, i, a, b, -0.5)
            push(t)
    # (N) tr rho = 1
    t = blank()
    for i in range(8):
        for a in (0, 1):
            cc_re(t, i, a, a, 1.0)
    push(t, -1.0)
    # (E) P_i = Q_i
    for i in range(8):
        t = blank()
        for a in (0, 1):
            cc_re(t, i, a, a, 1.0); dd_re(t, i, a, a, -1.0)
        push(t)
    # (A) P_6 = P_7 = 1/8
    for i in (6, 7):
        t = blank()
        for a in (0, 1):
            cc_re(t, i, a, a, 1.0)
        push(t, -0.125)
    # (T2)
    for f in (cc_re, dd_re):
        t = blank()
        for i in (0, 2, 4):
            for a in (0, 1):
                f(t, i, a, a, 1.0)
        push(t, -0.375)
    # (R1)
    for g in range(3):
        for h in range(g + 1, 3):
            for a in (0, 1):
                for b in (0, 1):
                    for f in (cd_re, cd_im):
                        t = blank()
                        for c in (0, 1):
                            f(t, 2 * g + c, a, 2 * h + 1 - c, b, 1.0)
                            f(t, 2 * h + c, a, 2 * g + 1 - c, b, 1.0)
                        push(t)
    # (R2)
    for j in (6, 7):
        for i in range(6):
            for f in (cd_re, cd_im):
                t = blank()
                for a in (0, 1):
                    f(t, j, a, i, a, 1.0); f(t, i, a, j, a, 1.0)
                push(t)
    # (R3) scalar relations carried by the weight-one masks, not implied by R1/R2
    if use_R3:
        for (p, q, r) in [(0, 3, 1), (0, 5, 1), (2, 5, 3)]:
            pass
        TRIPLES = [((0, 3), (3, 0), (1, 2), (2, 1)),      # mask 010000, groups 0-1
                   ((0, 5), (5, 0), (1, 4), (4, 1)),      # mask 001000, groups 0-2
                   ((2, 5), (5, 2), (3, 4), (4, 3))]      # mask 000001, groups 1-2
        for (a1, d1, b1, c1) in TRIPLES:
            #  C_{a1[0]}^dag D_{a1[1]} = C_{d1[0]}^dag D_{d1[1]}
            #  C_{b1[0]}^dag D_{b1[1]} = - that,  C_{c1[0]}^dag D_{c1[1]} = - that
            for (u, v, sgn) in [(a1, d1, -1.0), (b1, d1, +1.0), (c1, d1, +1.0)]:
                for f in (cd_re, cd_im):
                    t = blank()
                    for a in (0, 1):
                        f(t, u[0], a, u[1], a, 1.0)
                        f(t, v[0], a, v[1], a, sgn)
                    push(t)
    # branch constraints
    for (j, i) in extra_zero:
        for f in (cd_re, cd_im):
            t = blank()
            for a in (0, 1):
                f(t, j, a, i, a, 1.0)
            push(t)
    return np.array(Ms), np.array(cs)


def solve(extra_zero=(), use_R3=False, nstart=300, seed=1, scale=0.4):
    M, c = build(extra_zero, use_R3)
    r = lambda x: np.einsum('kij,i,j->k', M, x, x) + c
    j = lambda x: 2.0 * np.einsum('kij,j->ki', M, x)
    rs = np.random.RandomState(seed)
    best, bx = np.inf, None
    for _ in range(nstart):
        s = least_squares(r, rs.randn(N) * scale, jac=j, method='lm', xtol=1e-15,
                          ftol=1e-15, gtol=1e-15, max_nfev=5000)
        v = np.linalg.norm(s.fun)
        if v < best:
            best, bx = v, s.x.copy()
    return best, bx


def report(x):
    C = np.array([[x[cR(i, a)] + 1j * x[cI(i, a)] for a in (0, 1)] for i in range(8)])
    D = np.array([[x[dR(i, a)] + 1j * x[dI(i, a)] for a in (0, 1)] for i in range(8)])
    return C, D
