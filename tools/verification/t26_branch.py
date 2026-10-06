"""Task 3: for each anchor j and group g, is R_g = 0 compatible with the
VERIFIED facts?

Facts model (a relaxation of the full KL system -- exactly what the argument uses):
  (M)  C_g C_g^dag + D_g D_g^dag = rho/2   for all four groups,  rho = sum_g C_g C_g^dag
  (N)  tr rho = 1
  (E)  P_i = Q_i for every block
  (A)  P_6 = P_7 = 1/8
  (T2) P_0+P_2+P_4 = 3/8 = Q_0+Q_2+Q_4   (the remaining moment-polytope relation)
  (R1) conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0     for 0 <= g < h <= 2
  (R2) C_j^dag D_i + C_i^dag D_j = 0                 for i <= 5, j in {6,7}
Branch constraint:  R_g^{(j)} = (C_j^dag D_{2g}, C_j^dag D_{2g+1}) = 0.

Feasibility by least squares from many random starts.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from itertools import combinations

import numpy as np
from scipy.optimize import least_squares

NB = 8
NV = 4 * NB * 2      # C and D, 8 blocks, 2 complex components -> 64 reals
J = np.array([[0.0, 1.0], [1.0, 0.0]])


def unpack(x):
    y = x.reshape(2, NB, 2, 2)        # [C/D][block][component][re/im]
    Z = y[..., 0] + 1j * y[..., 1]
    return Z[0], Z[1]                 # C[8][2], D[8][2]


def base_res(C, D, zero=()):
    Cg = [np.stack([C[2 * g], C[2 * g + 1]], axis=1) for g in range(4)]   # 2x2, columns
    Dg = [np.stack([D[2 * g], D[2 * g + 1]], axis=1) for g in range(4)]
    rho = sum(Cg[g] @ Cg[g].conj().T for g in range(4))
    out = []
    for g in range(4):                                    # (M) : Hermitian 2x2
        H = Cg[g] @ Cg[g].conj().T + Dg[g] @ Dg[g].conj().T - rho / 2
        out += [H[0, 0].real, H[1, 1].real, H[0, 1].real, H[0, 1].imag]
    out += [np.trace(rho).real - 1.0]                     # (N)
    P = np.array([np.vdot(C[i], C[i]).real for i in range(NB)])
    Qm = np.array([np.vdot(D[i], D[i]).real for i in range(NB)])
    out += list(P - Qm)                                   # (E)
    out += [P[6] - 0.125, P[7] - 0.125]                   # (A)
    out += [P[0] + P[2] + P[4] - 0.375]                   # (T2) moment polytope
    out += [Qm[0] + Qm[2] + Qm[4] - 0.375]
    for g in range(3):                                    # (R1)
        for h in range(g + 1, 3):
            M = Cg[g].conj() @ J @ Dg[h].T + Cg[h].conj() @ J @ Dg[g].T
            out += [M[0, 0].real, M[0, 0].imag, M[0, 1].real, M[0, 1].imag,
                    M[1, 0].real, M[1, 0].imag, M[1, 1].real, M[1, 1].imag]
    for j in (6, 7):                                      # (R2)
        for i in range(6):
            v = np.vdot(C[j], D[i]) + np.vdot(C[i], D[j])
            out += [v.real, v.imag]
    for (j, g) in zero:                                   # branch constraint
        for c in (0, 1):
            v = np.vdot(C[j], D[2 * g + c])
            out += [v.real, v.imag]
    return np.array(out)


def search(zero=(), nstart=150, seed=7):
    rs = np.random.RandomState(seed)
    f = lambda x: base_res(*unpack(x), zero=zero)
    best, bx = np.inf, None
    for _ in range(nstart):
        x0 = rs.randn(NV) * 0.35
        sol = least_squares(f, x0, method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15,
                            max_nfev=8000)
        v = np.linalg.norm(sol.fun)
        if v < best:
            best, bx = v, sol.x.copy()
    return best, bx


print('=== sanity: the facts model with NO branch constraint ===')
b0, x0 = search((), nstart=120)
C, D = unpack(x0)
print('  best residual %.3e' % b0)
print('  P = %s' % np.round([np.vdot(C[i], C[i]).real for i in range(NB)], 6))
Xs = {j: np.array([np.vdot(C[j], D[i]) for i in range(6)]) for j in (6, 7)}
for j in (6, 7):
    print('  |X_i^(%d)| = %s' % (j, np.round(np.abs(Xs[j]), 6)))

print()
print('=== single branch  R_g^{(j)} = 0 ===')
res1 = {}
for j in (6, 7):
    for g in range(3):
        v, xb = search(((j, g),), nstart=150, seed=11 + 3 * g + j)
        res1[(j, g)] = v
        Cb, Db = unpack(xb)
        Pb = np.round([np.vdot(Cb[i], Cb[i]).real for i in range(NB)], 5)
        print('  anchor j=%d, group g=%d : best residual %.3e   %-12s  P=%s'
              % (j, g, v, 'FEASIBLE' if v < 1e-8 else 'INFEASIBLE', Pb))

print()
print('=== two branches at the same anchor ===')
for j in (6, 7):
    for g, h in combinations(range(3), 2):
        v, xb = search(((j, g), (j, h)), nstart=150, seed=31 + 5 * g + h + j)
        print('  anchor j=%d, groups {%d,%d} : best residual %.3e   %s'
              % (j, g, h, v, 'FEASIBLE' if v < 1e-8 else 'INFEASIBLE'))

print()
print('=== all three branches at the same anchor ===')
for j in (6, 7):
    v, _ = search(((j, 0), (j, 1), (j, 2)), nstart=150, seed=97 + j)
    print('  anchor j=%d, groups {0,1,2} : best residual %.3e   %s'
          % (j, v, 'FEASIBLE' if v < 1e-8 else 'INFEASIBLE'))

print()
print('=== one branch at EACH anchor (cross-anchor mixed) ===')
for g in range(3):
    for h in range(3):
        v, _ = search(((6, g), (7, h)), nstart=120, seed=211 + 7 * g + h)
        print('  R_%d^{(6)}=0 and R_%d^{(7)}=0 : best residual %.3e   %s'
              % (g, h, v, 'FEASIBLE' if v < 1e-8 else 'INFEASIBLE'))
