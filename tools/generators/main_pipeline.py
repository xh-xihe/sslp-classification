"""Recompute the finite six-qubit pipeline in ``documents/20260822/main.tex``.

This is a generator/diagnostic, not a proof checker.  Its output is intended to
be turned into explicit certificates that Lean subsequently checks.  In
particular, none of the paper totals below are used to decide membership in a
stage: every stage is recomputed from the definitions.

The stages implemented here are

    primitive records -> nonempty labelled fibre pairs -> coarse affine rank
    -> exact moment feasibility -> active-support rank -> cube orbits.

Run through ``tools/run.py`` so that the repository's ``tools/core`` package is
on ``sys.path``::

    python tools/run.py generators/main_pipeline.py
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations
from math import gcd

import numpy as np
import sympy as sp
from scipy.optimize import linprog


MODULI = range(2, 10)
BETA = (0, 1, 1, 2, 3, 5, 9)


def logical_orders(q: int) -> list[int]:
    return [m for m in range(2, q + 1) if q % m == 0]


def primitive(a: tuple[int, ...], q: int) -> bool:
    g = q
    for x in a:
        g = gcd(g, x)
    return g == 1


def fibre_mask(a: tuple[int, ...], q: int, residue: int) -> int:
    ans = 0
    for x in range(64):
        if sum(a[j] for j in range(6) if x >> j & 1) % q == residue:
            ans |= 1 << x
    return ans


def mask_points(mask: int) -> list[int]:
    return [x for x in range(64) if mask >> x & 1]


def bit_vector(x: int) -> tuple[int, ...]:
    return tuple(x >> j & 1 for j in range(6))


def rational_rank(rows: list[tuple[int, ...]]) -> int:
    """Exact row rank; all matrices here have at most six columns."""
    if not rows:
        return 0
    a = [[Fraction(v) for v in row] for row in rows]
    nrow, ncol, pivot = len(a), len(a[0]), 0
    for col in range(ncol):
        hit = next((r for r in range(pivot, nrow) if a[r][col]), None)
        if hit is None:
            continue
        a[pivot], a[hit] = a[hit], a[pivot]
        scale = a[pivot][col]
        a[pivot] = [v / scale for v in a[pivot]]
        for r in range(nrow):
            if r != pivot and a[r][col]:
                scale = a[r][col]
                a[r] = [u - scale * v for u, v in zip(a[r], a[pivot])]
        pivot += 1
        if pivot == nrow:
            break
    return pivot


def affine_rank(points: list[int]) -> int:
    if not points:
        return 0
    base = bit_vector(points[0])
    return rational_rank(
        [tuple(u - v for u, v in zip(bit_vector(x), base)) for x in points[1:]]
    )


PAIR_COORDS = tuple(combinations(range(6), 2))


def phi(x: int) -> tuple[int, ...]:
    b = bit_vector(x)
    return b + tuple(b[i] * b[j] for i, j in PAIR_COORDS)


def moment_system(mask0: int, mask1: int) -> tuple[np.ndarray, np.ndarray, list[int], list[int]]:
    s0, s1 = mask_points(mask0), mask_points(mask1)
    n = len(s0) + len(s1)
    a = np.zeros((23, n), dtype=float)
    a[0, : len(s0)] = 1
    a[1, len(s0) :] = 1
    for j, x in enumerate(s0):
        a[2:, j] = phi(x)
    for j, x in enumerate(s1, start=len(s0)):
        a[2:, j] = -np.asarray(phi(x))
    b = np.zeros(23, dtype=float)
    b[:2] = 1
    return a, b, s0, s1


def feasible_point(mask0: int, mask1: int, objective: np.ndarray | None = None):
    a, b, s0, s1 = moment_system(mask0, mask1)
    c = np.zeros(a.shape[1]) if objective is None else objective
    result = linprog(c, A_eq=a, b_eq=b, bounds=(0, None), method="highs")
    return result, a, b, s0, s1


def as_fraction(value: float, max_denominator: int = 10**7) -> Fraction:
    if abs(value) < 1e-10:
        return Fraction(0)
    return Fraction(float(value)).limit_denominator(max_denominator)


def exact_basic_solution(a: np.ndarray, b: np.ndarray, candidate: np.ndarray) -> list[Fraction]:
    """Recover and check the exact basic solution proposed by HiGHS.

    Merely rounding every coordinate is not robust enough for a certificate
    generator.  We instead solve the integer column system on the candidate's
    support over ``QQ`` and set any genuine free parameters to zero.
    """
    support = [j for j, value in enumerate(candidate) if value > 1e-9]
    aa = sp.Matrix(a.astype(int))
    bb = sp.Matrix(b.astype(int))
    sub = aa[:, support]
    solution, params = sub.gauss_jordan_solve(bb)
    if params.rows:
        solution = solution.subs({symbol: 0 for symbol in params})
    point = [Fraction(0) for _ in range(a.shape[1])]
    for j, value in zip(support, solution):
        point[j] = Fraction(int(value.p), int(value.q))
    if any(value < 0 for value in point):
        raise ValueError("reconstructed primal point is negative")
    for row in range(a.shape[0]):
        lhs = sum(Fraction(int(a[row, j])) * point[j] for j in range(a.shape[1]))
        if lhs != Fraction(int(b[row])):
            raise ValueError("reconstructed primal point misses an equality")
    return point


def separation_certificate(mask0: int, mask1: int) -> tuple[int, ...]:
    """Find an exact strict integer separator for two feature polytopes."""
    s0, s1 = mask_points(mask0), mask_points(mask1)
    # Variables are h[0:21], alpha, epsilon.  Bound h to make the maximization
    # finite; any positive epsilon gives the desired strict separator.
    aub, bub = [], []
    for x in s0:
        aub.append(list(phi(x)) + [-1, 1])
        bub.append(0)
    for y in s1:
        aub.append(list(-np.asarray(phi(y))) + [1, 1])
        bub.append(0)
    objective = np.zeros(23)
    objective[-1] = -1
    result = linprog(objective, A_ub=np.asarray(aub), b_ub=np.asarray(bub),
                     bounds=[(-1, 1)] * 21 + [(-30, 30), (0, None)],
                     method="highs")
    if not result.success or result.x[-1] < 1e-8:
        raise ValueError("failed to find a strict separator")
    hf = [as_fraction(value) for value in result.x[:21]]
    denominator = 1
    for value in hf:
        denominator = denominator * value.denominator // gcd(denominator, value.denominator)
    h = tuple(int(value * denominator) for value in hf)
    left = [sum(c * z for c, z in zip(h, phi(x))) for x in s0]
    right = [sum(c * z for c, z in zip(h, phi(y))) for y in s1]
    if max(left) >= min(right):
        # HiGHS may return the reverse orientation depending on a degenerate
        # optimum; try it explicitly before giving up.
        h = tuple(-value for value in h)
        left = [sum(c * z for c, z in zip(h, phi(x))) for x in s0]
        right = [sum(c * z for c, z in zip(h, phi(y))) for y in s1]
    if max(left) >= min(right):
        raise ValueError("rational reconstruction destroyed strict separation")
    common = 0
    for value in h:
        common = gcd(common, abs(value))
    if common > 1:
        h = tuple(value // common for value in h)
    return h


def relative_interior_point(mask0: int, mask1: int) -> tuple[list[Fraction], list[int]]:
    """Return one exact point positive on every active coordinate."""
    probe, a, b, _, _ = feasible_point(mask0, mask1)
    if not probe.success:
        raise ValueError("relative-interior query on an infeasible pair")
    active: list[int] = []
    witnesses: list[list[Fraction]] = []
    for j in range(a.shape[1]):
        objective = np.zeros(a.shape[1])
        objective[j] = -1
        result = linprog(objective, A_eq=a, b_eq=b, bounds=(0, None), method="highs")
        if not result.success:
            raise RuntimeError(result.message)
        if result.x[j] > 1e-8:
            exact = exact_basic_solution(a, b, result.x)
            if exact[j] <= 0:
                raise ValueError("active candidate did not reconstruct positively")
            active.append(j)
            witnesses.append(exact)
    total = [sum((point[j] for point in witnesses), Fraction(0)) / len(witnesses)
             for j in range(a.shape[1])]
    if any((total[j] > 0) != (j in active) for j in range(a.shape[1])):
        raise ValueError("averaged point does not have exactly the active support")
    return total, active


def face_certificate(a: np.ndarray, b: np.ndarray, active: list[int]) -> list[Fraction]:
    """One exact dual exposing the complete active face.

    Its transpose coefficients vanish on active columns and are strictly
    negative on every other column, while ``b^T y = 0``.  Hence every feasible
    nonnegative point vanishes outside ``active``.
    """
    inactive = [j for j in range(a.shape[1]) if j not in set(active)]
    if not inactive:
        return [Fraction(0) for _ in range(a.shape[0])]
    aeq = [a[:, j] for j in active]
    aeq.append(b)
    aub = [a[:, j] for j in inactive]
    result = linprog(np.zeros(a.shape[0]), A_ub=np.asarray(aub),
                     b_ub=-np.ones(len(inactive)), A_eq=np.asarray(aeq),
                     b_eq=np.zeros(len(aeq)), bounds=[(None, None)] * a.shape[0],
                     method="highs")
    if not result.success:
        raise ValueError("failed to expose the active face")
    y = [as_fraction(value) for value in result.x]
    # Verify exact signs and equalities before returning any data.
    for j in active:
        if sum(Fraction(int(a[i, j])) * y[i] for i in range(a.shape[0])) != 0:
            raise ValueError("face dual does not vanish on an active column")
    for j in inactive:
        if sum(Fraction(int(a[i, j])) * y[i] for i in range(a.shape[0])) >= 0:
            raise ValueError("face dual is not strict on an inactive column")
    if sum(Fraction(int(b[i])) * y[i] for i in range(a.shape[0])) != 0:
        raise ValueError("face dual has nonzero right-hand-side pairing")
    return y


def active_indices(mask0: int, mask1: int) -> tuple[list[int], list[int]]:
    probe, a, b, s0, s1 = feasible_point(mask0, mask1)
    if not probe.success:
        raise ValueError("active-index query on an infeasible pair")
    active: list[int] = []
    for j in range(a.shape[1]):
        c = np.zeros(a.shape[1])
        c[j] = -1
        result = linprog(c, A_eq=a, b_eq=b, bounds=(0, None), method="highs")
        if not result.success:
            raise RuntimeError(result.message)
        if result.x[j] > 1e-8:
            active.append(j)
    return ([s0[j] for j in active if j < len(s0)],
            [s1[j - len(s0)] for j in active if j >= len(s0)])


PERMS = tuple(permutations(range(6)))


def permute_word(x: int, p: tuple[int, ...]) -> int:
    """Output coordinate j receives input coordinate p[j]."""
    return sum(((x >> p[j]) & 1) << j for j in range(6))


PERM_TABLES = tuple(tuple(permute_word(x, p) for x in range(64)) for p in PERMS)


def transform_mask(mask: int, table: tuple[int, ...], shift: int) -> int:
    ans = 0
    for x in mask_points(mask):
        ans |= 1 << (table[x] ^ shift)
    return ans


def cube_key(m: int, mask0: int, mask1: int) -> tuple[int, int, int]:
    best: tuple[int, int] | None = None
    for table in PERM_TABLES:
        p0 = transform_mask(mask0, table, 0)
        p1 = transform_mask(mask1, table, 0)
        for shift in range(64):
            pair = tuple(sorted((
                transform_mask(p0, tuple(range(64)), shift),
                transform_mask(p1, tuple(range(64)), shift),
            )))
            if best is None or pair < best:
                best = pair
    assert best is not None
    return m, best[0], best[1]


def translate_mask(mask: int, shift: int) -> int:
    ans = 0
    for x in mask_points(mask):
        ans |= 1 << (x ^ shift)
    return ans


def cube_key_fast(m: int, mask0: int, mask1: int) -> tuple[int, int, int]:
    best: tuple[int, int] | None = None
    for table in PERM_TABLES:
        p0 = transform_mask(mask0, table, 0)
        p1 = transform_mask(mask1, table, 0)
        for shift in range(64):
            pair = tuple(sorted((translate_mask(p0, shift), translate_mask(p1, shift))))
            if best is None or pair < best:
                best = pair
    assert best is not None
    return m, best[0], best[1]


def cube_key_with_witness(m: int, mask0: int, mask1: int):
    best: tuple[int, int] | None = None
    witness: tuple[int, int, bool] | None = None
    for perm_index, table in enumerate(PERM_TABLES):
        p0 = transform_mask(mask0, table, 0)
        p1 = transform_mask(mask1, table, 0)
        for shift in range(64):
            t0, t1 = translate_mask(p0, shift), translate_mask(p1, shift)
            swap = t1 < t0
            pair = (t1, t0) if swap else (t0, t1)
            if best is None or pair < best:
                best, witness = pair, (perm_index, shift, swap)
    assert best is not None and witness is not None
    return (m, best[0], best[1]), witness


def distance_histogram(xs: list[int], ys: list[int], same: bool) -> tuple[int, ...]:
    counts = [0] * 7
    if same:
        for i, x in enumerate(xs):
            for y in xs[i + 1:]:
                counts[(x ^ y).bit_count()] += 1
    else:
        for x in xs:
            for y in ys:
                counts[(x ^ y).bit_count()] += 1
    return tuple(counts)


def distance_signature(q: int, m: int, mask0: int, mask1: int):
    """A cheap cube-isometry/color-swap invariant (not assumed complete)."""
    s0, s1 = mask_points(mask0), mask_points(mask1)
    within = sorted((distance_histogram(s0, s0, True),
                     distance_histogram(s1, s1, True)))
    return q, m, tuple(within), distance_histogram(s0, s1, False)


def rational_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def sparse_distribution(words: list[int], point: list[Fraction]) -> list[list[object]]:
    return [[word, rational_text(value)] for word, value in zip(words, point) if value]


def affine_rank_certificate(mask: int) -> dict[str, object]:
    """Exact lower/upper witnesses for the affine rank of one mask."""
    points = mask_points(mask)
    if not points:
        return {"rank": 0, "base": 0, "lower_points": [], "lower_coords": [],
                "normals": [[1, 0, 0, 0, 0, 0]], "normal_coords": [0]}
    base = points[0]
    basev = bit_vector(base)
    rows = [tuple(a - b for a, b in zip(bit_vector(x), basev)) for x in points[1:]]
    matrix = sp.Matrix(rows) if rows else sp.zeros(0, 6)
    rank = int(matrix.rank())
    selected: list[int] = []
    current = sp.zeros(0, 6)
    for row_index, row in enumerate(rows):
        candidate = current.col_join(sp.Matrix([row]))
        if candidate.rank() > current.rank():
            selected.append(row_index)
            current = candidate
        if len(selected) == rank:
            break
    lower_coords = list(current.rref()[1]) if rank else []
    if rank and current[:, lower_coords].det() == 0:
        raise AssertionError("bad lower affine-rank minor")
    normals = []
    for vector in matrix.nullspace():
        denominator = 1
        for value in vector:
            denominator = denominator * int(value.q) // gcd(denominator, int(value.q))
        normal = [int(value * denominator) for value in vector]
        common = 0
        for value in normal:
            common = gcd(common, abs(value))
        if common > 1:
            normal = [value // common for value in normal]
        normals.append(normal)
    if len(normals) != 6 - rank:
        raise AssertionError("wrong nullspace dimension")
    normal_matrix = sp.Matrix(normals) if normals else sp.zeros(0, 6)
    normal_coords = list(normal_matrix.rref()[1]) if normals else []
    if normals and normal_matrix[:, normal_coords].det() == 0:
        raise AssertionError("bad normal-independence minor")
    for row in rows:
        for normal in normals:
            if sum(a * b for a, b in zip(row, normal)):
                raise AssertionError("normal misses an affine difference")
    return {
        "rank": rank,
        "base": base,
        "lower_points": [points[i + 1] for i in selected],
        "lower_coords": lower_coords,
        "normals": normals,
        "normal_coords": normal_coords,
    }


def main(output: str | None = None) -> None:
    primitive_records: list[tuple[int, int, tuple[int, ...]]] = []
    nonempty_records: list[tuple[int, int, tuple[int, ...], int, int]] = []
    for q in MODULI:
        for m in logical_orders(q):
            for a in combinations_with_replacement(range(q), 6):
                if not primitive(a, q):
                    continue
                primitive_records.append((q, m, a))
                s0 = fibre_mask(a, q, 0)
                s1 = fibre_mask(a, q, q // m)
                if s1:
                    nonempty_records.append((q, m, a, s0, s1))

    pairs: dict[tuple[int, int, int, int], list[tuple[int, ...]]] = {}
    for q, m, a, s0, s1 in nonempty_records:
        pairs.setdefault((q, m, s0, s1), []).append(a)

    coarse = []
    for key, angles in pairs.items():
        q, m, s0, s1 = key
        rmin = next(r for r in range(1, 7) if BETA[r] >= q)
        if min(affine_rank(mask_points(s0)), affine_rank(mask_points(s1))) >= rmin:
            coarse.append((key, angles))

    moment = []
    moment_certificates = []
    for index, item in enumerate(coarse, 1):
        key, _ = item
        result, aeq, beq, s0words, s1words = feasible_point(key[2], key[3])
        if result.success:
            point = exact_basic_solution(aeq, beq, result.x)
            moment.append(item)
            moment_certificates.append({
                "pair": None,
                "kind": "primal",
                "p0": sparse_distribution(s0words, point[:len(s0words)]),
                "p1": sparse_distribution(s1words, point[len(s0words):]),
            })
        else:
            h = separation_certificate(key[2], key[3])
            left = [sum(c * z for c, z in zip(h, phi(x))) for x in s0words]
            right = [sum(c * z for c, z in zip(h, phi(x))) for x in s1words]
            moment_certificates.append({
                "pair": None,
                "kind": "separator",
                "h": list(h),
                "lower": max(left),
                "upper": min(right),
            })
        if index % 100 == 0:
            print(f"moment LP: {index}/{len(coarse)}", flush=True)

    rank_compatible = []
    rank_certificates = []
    active_breakdown: dict[tuple[int, int], list[int]] = {}
    for index, item in enumerate(moment, 1):
        key, _ = item
        q, m, s0, s1 = key
        point, active = relative_interior_point(s0, s1)
        _, aeq, beq, all0, all1 = feasible_point(s0, s1)
        dual = face_certificate(aeq, beq, active)
        u0 = [all0[j] for j in active if j < len(all0)]
        u1 = [all1[j - len(all0)] for j in active if j >= len(all0)]
        rank = min(affine_rank(u0), affine_rank(u1))
        active_breakdown.setdefault((q, m), [0, 0])[0] += 1
        if BETA[rank] >= q:
            rank_compatible.append(item)
            active_breakdown[(q, m)][1] += 1
        active0 = sum(1 << x for x in u0)
        active1 = sum(1 << x for x in u1)
        rank_certificates.append({
            "pair": None,
            "p0": sparse_distribution(all0, point[:len(all0)]),
            "p1": sparse_distribution(all1, point[len(all0):]),
            "active0": active0,
            "active1": active1,
            "dual": [rational_text(value) for value in dual],
            "rank0": affine_rank_certificate(active0),
            "rank1": affine_rank_certificate(active1),
            "compatible": BETA[rank] >= q,
        })
        if index % 50 == 0:
            print(f"active LP: {index}/{len(moment)}", flush=True)

    keys = {(key[0], *cube_key_fast(key[1], key[2], key[3]))
            for key, _ in rank_compatible}
    signatures = {
        distance_signature(q, m, mask0, mask1) for q, m, mask0, mask1 in keys
    }
    by_m: dict[int, list[int]] = {}
    for key, _ in rank_compatible:
        by_m.setdefault(key[1], [0, 0])[0] += 1
    for _, m, _, _ in keys:
        by_m.setdefault(m, [0, 0])[1] += 1

    print("\ncounts")
    print("primitive records", len(primitive_records))
    print("nonempty records", len(nonempty_records))
    print("labelled fibre pairs", len(pairs))
    print("coarse affine survivors", len(coarse), "angle records", sum(map(lambda x: len(x[1]), coarse)))
    print("moment feasible", len(moment), "angle records", sum(map(lambda x: len(x[1]), moment)))
    print("rank compatible", len(rank_compatible), "angle records", sum(map(lambda x: len(x[1]), rank_compatible)))
    print("cube orbits", len(keys))
    print("distinct distance signatures of canonical keys", len(signatures))
    print("by m", sorted(by_m.items()))
    print("moment/rank by (q,m)", sorted(active_breakdown.items()))

    if output is not None:
        pair_table = sorted(pairs)
        pair_id = {key: index for index, key in enumerate(pair_table)}
        record_ids = [pair_id[(q, m, s0, s1)] for q, m, _, s0, s1 in nonempty_records]
        first_record: dict[int, int] = {}
        for record_index, pid in enumerate(record_ids):
            first_record.setdefault(pid, record_index)
        coarse_ids = [pair_id[key] for key, _ in coarse]
        for cert, pid in zip(moment_certificates, coarse_ids):
            cert["pair"] = pid
        moment_ids = [pair_id[key] for key, _ in moment]
        for cert, pid in zip(rank_certificates, moment_ids):
            cert["pair"] = pid
        compatible_ids = [pair_id[key] for key, _ in rank_compatible]

        key_info = []
        for key, _ in rank_compatible:
            old_key, witness = cube_key_with_witness(key[1], key[2], key[3])
            key_info.append(((key[0], *old_key), witness))
        orbit_keys = sorted({info[0] for info in key_info})
        orbit_id = {key: index for index, key in enumerate(orbit_keys)}
        cube_witnesses = []
        for pid, (key, witness) in zip(compatible_ids, key_info):
            cube_witnesses.append({
                "pair": pid,
                "orbit": orbit_id[key],
                "perm": witness[0],
                # Store the semantic permutation itself.  The numerical index
                # is diagnostic metadata only; Lean must not depend on Python's
                # iteration order for ``itertools.permutations``.
                "permutation": list(PERMS[witness[0]]),
                "shift": witness[1],
                "swap": witness[2],
            })

        # Rank certificates are cached by mask.  Pair rows refer to this table;
        # this avoids repeating the same affine linear algebra data.
        masks = sorted({mask for key in pair_table for mask in key[2:]})
        mask_id = {mask: index for index, mask in enumerate(masks)}
        rank_data = [affine_rank_certificate(mask) for mask in masks]

        payload = {
            "pair_table": [list(key) for key in pair_table],
            "record_pair_ids": record_ids,
            "pair_witness_records": [first_record[i] for i in range(len(pair_table))],
            "pair_mask_rank_ids": [[mask_id[key[2]], mask_id[key[3]]] for key in pair_table],
            "mask_table": masks,
            "mask_rank_certificates": rank_data,
            "coarse_pair_ids": coarse_ids,
            "coarse_angle_count": sum(len(angles) for _, angles in coarse),
            "moment_certificates": moment_certificates,
            "rank_certificates": rank_certificates,
            "compatible_pair_ids": compatible_ids,
            "compatible_angle_count": sum(len(angles) for _, angles in rank_compatible),
            "orbit_keys": [list(key) for key in orbit_keys],
            "orbit_signatures": [distance_signature(*key) for key in orbit_keys],
            "cube_witnesses": cube_witnesses,
        }
        with open(output, "w", encoding="utf-8", newline="\n") as handle:
            json.dump(payload, handle, indent=2)
            handle.write("\n")
        print("wrote", output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", help="write exact generated certificate data as JSON")
    args = parser.parse_args()
    main(args.output)
