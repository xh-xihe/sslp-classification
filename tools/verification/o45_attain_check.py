"""Numerical diagnostic for the direct full-fibre orbit-45 ansatz.

This is not proof evidence.  The Lean module independently proves every KL
row; this script is only useful while designing the sparse formula.
"""

from cmath import sqrt

S0 = [0, 55, 36, 19, 20, 35, 58, 13, 14, 57]
S1 = [8, 63, 44, 27, 28, 43, 50, 5, 6, 49]


def wt_pauli(x, z):
    return (x | z).bit_count()


def parity(x):
    return x.bit_count() & 1


def code(g, lam):
    a = [sqrt(x) / 2 for x in g]
    q = sqrt(1 / 8)
    cv = [a[0], -lam[0].conjugate() * a[0],
          a[1], -lam[1].conjugate() * a[1],
          a[2], -lam[2].conjugate() * a[2], q, q, q, -q]
    dv = [lam[0] * a[0], -a[0], lam[1] * a[1], -a[1],
          lam[2] * a[2], -a[2], q, q, -q, q]
    c = dict(zip(S0, cv))
    d = dict(zip(S1, dv))
    return c, d


def raw(a, b, x, z):
    return sum(((-1) ** parity(z & s)) * a.get(s ^ x, 0).conjugate() * v
               for s, v in b.items())


def check(g, lam):
    c, d = code(g, lam)
    worst = (0.0, None)
    for x in range(64):
        for z in range(64):
            if wt_pauli(x, z) > 2:
                continue
            vals = (raw(c, c, x, z) - raw(d, d, x, z),
                    raw(c, d, x, z), raw(d, c, x, z))
            for k, v in enumerate(vals):
                if abs(v) > worst[0]:
                    worst = abs(v), (x, z, k, v)
    return worst


if __name__ == "__main__":
    print("high", check([.1, .4, .5], [1, 1, -1]))
    s = .2
    u = (1 - s) / (1 + s)
    v = 2 * sqrt(s) / (1 + s)
    print("low", check([(1+s)/4, (1+s)/4, (1-s)/2],
                       [u+1j*v, u-1j*v, -1]))
