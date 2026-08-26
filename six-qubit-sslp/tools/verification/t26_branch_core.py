"""Residuals of the VERIFIED-FACTS model for orbit 26 (shared by the branch scans).

  (M)  C_g C_g^dag + D_g D_g^dag = rho/2   for all four groups, rho = sum_g C_g C_g^dag
  (N)  tr rho = 1
  (E)  P_i = Q_i for every block
  (A)  P_6 = P_7 = 1/8
  (T2) P_0+P_2+P_4 = 3/8 = Q_0+Q_2+Q_4          (remaining moment-polytope relation)
  (R1) conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0     for 0 <= g < h <= 2
  (R2) C_j^dag D_i + C_i^dag D_j = 0                 for i <= 5, j in {6,7}
"""
import numpy as np

NB = 8
NV = 4 * NB * 2
J = np.array([[0.0, 1.0], [1.0, 0.0]])


def unpack(x):
    y = x.reshape(2, NB, 2, 2)
    Z = y[..., 0] + 1j * y[..., 1]
    return Z[0], Z[1]


def base_res(C, D, zero=()):
    Cg = [np.stack([C[2 * g], C[2 * g + 1]], axis=1) for g in range(4)]
    Dg = [np.stack([D[2 * g], D[2 * g + 1]], axis=1) for g in range(4)]
    rho = sum(Cg[g] @ Cg[g].conj().T for g in range(4))
    out = []
    for g in range(4):
        H = Cg[g] @ Cg[g].conj().T + Dg[g] @ Dg[g].conj().T - rho / 2
        out += [H[0, 0].real, H[1, 1].real, H[0, 1].real, H[0, 1].imag]
    out += [np.trace(rho).real - 1.0]
    P = np.array([np.vdot(C[i], C[i]).real for i in range(NB)])
    Qm = np.array([np.vdot(D[i], D[i]).real for i in range(NB)])
    out += list(P - Qm)
    out += [P[6] - 0.125, P[7] - 0.125]
    out += [P[0] + P[2] + P[4] - 0.375, Qm[0] + Qm[2] + Qm[4] - 0.375]
    for g in range(3):
        for h in range(g + 1, 3):
            M = Cg[g].conj() @ J @ Dg[h].T + Cg[h].conj() @ J @ Dg[g].T
            out += [M[0, 0].real, M[0, 0].imag, M[0, 1].real, M[0, 1].imag,
                    M[1, 0].real, M[1, 0].imag, M[1, 1].real, M[1, 1].imag]
    for j in (6, 7):
        for i in range(6):
            v = np.vdot(C[j], D[i]) + np.vdot(C[i], D[j])
            out += [v.real, v.imag]
    for (j, g) in zero:
        for c in (0, 1):
            v = np.vdot(C[j], D[2 * g + c])
            out += [v.real, v.imag]
    return np.array(out)
