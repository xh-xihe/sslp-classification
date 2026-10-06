"""Exact exploratory certificates for the orbit-45 Gram reduction.

This is *not* a proof artifact.  Its purpose is to print and independently
check the small rational identities that are intended to be transcribed into
Lean.  Everything below uses SymPy rationals; there is no floating point and
no numerical optimizer.

Coordinates use the Lean convention in which the first displayed bit is bit
0.  Thus the coefficient-3 coordinate is mask 8 and the five block pairs are
the orbits of mask 55 inside the residue-zero fibre.
"""

from __future__ import annotations

from itertools import combinations

import sympy as sp


AV = (1, 1, 2, 3, 4, 4)
E3 = 1 << 3
H = 55


def residue(x: int) -> int:
    return sum(AV[i] * ((x >> i) & 1) for i in range(6)) % 6


F0 = tuple(x for x in range(64) if residue(x) == 0)
F3 = tuple(x for x in range(64) if residue(x) == 3)

# (a_j,b_j) in the notation used by the certificate discussion.  The
# corresponding top pair is obtained by xor E3.
BLOCKS = ((0, 55), (36, 19), (20, 35), (58, 13), (14, 57))


def chi(z: int, s: int) -> int:
    return -1 if (z & s).bit_count() % 2 else 1


def walsh_rows(x: int) -> tuple[tuple[int, ...], tuple[int, ...], sp.Matrix]:
    """Raw cross-KL Walsh matrix for a fixed X mask.

    Its columns index s in F0 for which y=s xor x lies in F3.  The character
    is evaluated at that top source y, exactly as in CodeBridge.offSumOn.
    Only the global nonzero i^numY Pauli phase has been removed.
    """

    edges = tuple(s for s in F0 if (s ^ x) in F3)
    zs = tuple(z for z in range(64) if (z | x).bit_count() <= 2)
    mat = sp.Matrix([[chi(z, s ^ x) for s in edges] for z in zs])
    return edges, zs, mat


def exact_row_certificate(x: int, target: tuple[int, ...]) -> tuple[tuple[int, sp.Rational], ...]:
    """Return lambda with target = sum_z lambda_z * WalshRow(x,z)."""

    _edges, zs, mat = walsh_rows(x)
    target_col = sp.Matrix(target)
    # There are at most twelve rows.  Exhaustively choose the smallest support
    # so the printed certificate is useful to a human Lean transcription.
    for width in range(1, len(zs) + 1):
        for indices in combinations(range(len(zs)), width):
            chosen = sp.Matrix.hstack(*(mat.row(i).T for i in indices))
            if chosen.rank() != chosen.row_join(target_col).rank():
                continue
            answer = next(iter(sp.linsolve((chosen, target_col))))
            free = set().union(*(entry.free_symbols for entry in answer))
            answer = tuple(sp.factor(entry.subs({v: 0 for v in free})) for entry in answer)
            assert chosen * sp.Matrix(answer) == target_col
            return tuple((zs[i], lam) for i, lam in zip(indices, answer) if lam != 0)
    raise AssertionError("target is not in the raw Walsh row span")


def diagonal_reduction() -> None:
    """Check the exact three-parameter solution of all diagonal KL rows."""

    q = sp.symbols(f"q0:{len(F0)}")
    d = sp.symbols(f"d0:{len(F3)}")
    variables = q + d
    equations = [sum(q) - 1, sum(d) - 1]
    for degree in (1, 2):
        for support in combinations(range(6), degree):
            equations.append(
                sum(q[j] * int(all((s >> i) & 1 for i in support)) for j, s in enumerate(F0))
                - sum(d[j] * int(all((s >> i) & 1 for i in support)) for j, s in enumerate(F3))
            )
    mat, rhs = sp.linear_eq_to_matrix(equations, variables)
    assert len(equations) == 23 and mat.rank() == 17

    g1, g2, g3, g4, g5 = sp.symbols("g1:6")
    by_block = {s: j for j, pair in enumerate(BLOCKS) for s in pair}
    expected = tuple(g1 if False else (g1, g2, g3, g4, g5)[by_block[s]] / 4 for s in F0)
    expected += tuple((g1, g2, g3, g4, g5)[by_block[s ^ E3]] / 4 for s in F3)
    residual = mat * sp.Matrix(expected) - rhs
    substitutions = {g3: 1 - g1 - g2, g5: 1 - g4}
    assert all(sp.expand(entry.subs(substitutions)) == 0 for entry in residual)

    # Conversely, the exact rref has three free parameters and is precisely
    # the displayed five-block family.
    solution = next(iter(sp.linsolve((mat, rhs), variables)))
    assert len(set().union(*(entry.free_symbols for entry in solution))) == 3
    print("diagonal KL: 23 rows, rank 17; exact five-block parametrization checked")
    print("  each of the four entries of block j has normSq g_j/4")
    print("  g1+g2+g3=1, g4+g5=1")


def cross_walsh_certificates() -> None:
    """Print the sparse rational multipliers used in the Gram proof."""

    # On x=8, columns are F0 in increasing integer order.
    edges, _zs, mat = walsh_rows(E3)
    assert edges == F0 and mat.rank() == 7
    targets = {
        # p13+p14=0, hence g4=g5.
        "p13+p14": tuple(int(s in (13, 14)) for s in edges),
        # p0+p19+p20=0, the triangle closure.
        "p0+p19+p20": tuple(int(s in (0, 19, 20)) for s in edges),
        # Within-block equalities needed to put the triangle closure in a_j,A_j form.
        "p19-p36": tuple((1 if s == 19 else -1 if s == 36 else 0) for s in edges),
        "p13-p58": tuple((1 if s == 13 else -1 if s == 58 else 0) for s in edges),
        "p14-p57": tuple((1 if s == 14 else -1 if s == 57 else 0) for s in edges),
    }
    print("x=8 cross-KL rational row certificates (mask: multiplier):")
    for name, target in targets.items():
        print(f"  {name:12s} = {exact_row_certificate(E3, target)}")

    # Connector rows.  Each target is a two-term binomial.  These are exactly
    # the E4_j and E5_j equations used below; only two raw Walsh rows occur.
    connector_targets = {
        5: ((1, 0, 0, 1), (0, 1, 1, 0)),
        6: ((1, 0, 0, 1), (0, 1, 1, 0)),
        17: ((1, 0, 1, 0), (0, 1, 0, 1)),
        18: ((1, 0, 1, 0), (0, 1, 0, 1)),
        33: ((1, 1, 0, 0), (0, 0, 1, 1)),
        34: ((1, 1, 0, 0), (0, 0, 1, 1)),
    }
    print("connector binomials:")
    for x, pair in connector_targets.items():
        edges, _zs, _mat = walsh_rows(x)
        print(f"  x={x:2d}, edges={edges}")
        for target in pair:
            print(f"    {exact_row_certificate(x, target)}")


def formal_gram_identities() -> None:
    """Verify the quartic Gram/frame identities as formal polynomials."""

    # bar variables are independent formal indeterminates.  The involution
    # below exchanges a<->ab and b<->bb, so a polynomial identity here is an
    # identity over every complex specialization.
    a = sp.symbols("a1:6")
    ab = sp.symbols("ab1:6")
    b = sp.symbols("b1:6")
    bb = sp.symbols("bb1:6")
    g = sp.symbols("g1:6")
    involution = {**dict(zip(a, ab)), **dict(zip(ab, a)), **dict(zip(b, bb)), **dict(zip(bb, b))}

    def star(expr: sp.Expr) -> sp.Expr:
        return sp.expand(expr.xreplace(involution))

    def nsq(expr: sp.Expr) -> sp.Expr:
        return sp.expand(expr * star(expr))

    # Twisted two-vectors u_j=(a_j,bar b_j).  The correlations below are the
    # four non-diagonal X-mask contributions to A_2, up to conjugation.
    f12 = ab[1] * a[0] + bb[0] * b[1]
    f13 = ab[2] * a[0] + bb[0] * b[2]
    f23 = ab[1] * a[2] + bb[2] * b[1]
    triangle_product = sum(a[j] * b[j] for j in range(3))

    # First check the identity before imposing equal block magnitudes.  Then
    # substitute |a_j|^2=|b_j|^2=g_j/4 and sum g_j=1.
    lhs = nsq(f12) + nsq(f13) + nsq(f23)
    rhs_general = (
        nsq(triangle_product)
        + sum((a[j] * ab[j]) * (a[k] * ab[k]) + (b[j] * bb[j]) * (b[k] * bb[k])
              for j, k in combinations(range(3), 2))
        - sum((a[j] * ab[j]) * (b[j] * bb[j]) for j in range(3))
    )
    assert sp.expand(lhs - rhs_general) == 0
    claimed = nsq(triangle_product) + (1 - 2 * sum(g[j] ** 2 for j in range(3))) / 16
    # Substitution of |a_j|^2=|b_j|^2=g_j/4 in rhs_general leaves this
    # scalar expression.  Check its reduction using g1+g2+g3=1 exactly.
    scalar_remainder = (
        sum(g[j] * g[k] / 8 for j, k in combinations(range(3), 2))
        - sum(g[j] ** 2 / 16 for j in range(3))
    )
    assert sp.factor(
        (nsq(triangle_product) + scalar_remainder - claimed).subs(g[2], 1 - g[0] - g[1])
    ) == 0

    # The fourth correlation has the same norm square as a4*b4+a5*b5 once
    # all four component magnitudes are equal (g4=g5=1/2).
    f45 = ab[4] * b[3] + ab[3] * b[4]
    t45 = a[3] * b[3] + a[4] * b[4]
    delta45 = sp.expand(nsq(f45) - nsq(t45))
    delta45_claim = -(
        a[3] * ab[3] - a[4] * ab[4]
    ) * (
        b[3] * bb[3] - b[4] * bb[4]
    )
    assert sp.expand(delta45 - delta45_claim) == 0

    # Diagonal weight-two Z contribution and the final A2 formula.
    block_of = {s: j for j, pair in enumerate(BLOCKS) for s in pair}
    q = {s: g[block_of[s]] / 4 for s in F0}
    diagonal = 0
    for z in range(64):
        if z.bit_count() == 2:
            ez = sum(chi(z, s) * q[s] for s in F0)
            diagonal += ez**2
    diagonal = sp.expand(diagonal)
    constraints = {g[2]: 1 - g[0] - g[1], g[4]: sp.Rational(1, 2), g[3]: sp.Rational(1, 2)}
    diagonal_claim = 3 * sum(g[j] ** 2 for j in range(3)) - sp.Rational(1, 2)
    assert sp.factor((diagonal - diagonal_claim).subs(constraints)) == 0
    off_diagonal_claim = sp.Rational(1, 2) - sum(g[j] ** 2 for j in range(3))
    a2_claim = 2 * sum(g[j] ** 2 for j in range(3))
    assert sp.expand(diagonal_claim + off_diagonal_claim - a2_claim) == 0

    r = tuple(1 - 2 * g[j] for j in range(3))
    simplex_form = (1 + sum(x**2 for x in r)) / 2
    assert sp.factor((a2_claim - simplex_form).subs(g[2], 1 - g[0] - g[1])) == 0
    print("formal Gram identities: PASS")
    print("  diagonal A2 contribution = 3*sum(g_j^2)-1/2")
    print("  off-diagonal contribution = 1/2-sum(g_j^2)")
    print("  A2 = 2*sum(g_j^2) = (1+sum((1-2*g_j)^2))/2")


def interval_sos() -> None:
    """Check the two elementary polynomial certificates for 2/3 <= A2 <= 1."""

    r1, r2, r3 = sp.symbols("r1 r2 r3", nonnegative=True)
    lower = 3 * (r1**2 + r2**2 + r3**2) - (r1 + r2 + r3) ** 2
    lower_sos = (r1 - r2) ** 2 + (r2 - r3) ** 2 + (r3 - r1) ** 2
    assert sp.expand(lower - lower_sos) == 0
    upper = (r1 + r2 + r3) ** 2 - (r1**2 + r2**2 + r3**2)
    upper_pos = 2 * (r1 * r2 + r1 * r3 + r2 * r3)
    assert sp.expand(upper - upper_pos) == 0
    print("interval certificates: PASS")
    print("  3*sum(r^2)-(sum r)^2 = sum_cyclic((ri-rj)^2)")
    print("  (sum r)^2-sum(r^2) = 2*sum_{i<j}(ri*rj)")


def main() -> None:
    assert F0 == (0, 13, 14, 19, 20, 35, 36, 55, 57, 58)
    assert F3 == tuple(sorted(s ^ E3 for s in F0))
    assert all((a ^ H) == b for a, b in BLOCKS)
    assert {s for pair in BLOCKS for s in pair} == set(F0)
    print(f"fibres: |F0|={len(F0)}, |F3|={len(F3)}, e3={E3}, h={H}")
    diagonal_reduction()
    cross_walsh_certificates()
    formal_gram_identities()
    interval_sos()


if __name__ == "__main__":
    main()
