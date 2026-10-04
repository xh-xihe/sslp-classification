#!/usr/bin/env python3
"""Exact formal obstruction to a scalar-only SSLP class-3 converse.

This checks a rational relaxation point, NOT a projector or quantum code.
Only the Python standard library is required. All comparisons are exact.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path


def categories():
    # (nonidentity spectator, tail Z count, tail X/Y count)
    return [(a, j, k) for a in (0, 1) for k in range(6)
            for j in range(6-k)]


def orbit_size(label):
    a, j, k = label
    return 3**a * math.factorial(5) // (
        math.factorial(j)*math.factorial(k)*math.factorial(5-j-k)) * 2**k


def multiply(p, q):
    answer = {}
    for (i, j), x in p.items():
        for (k, l), y in q.items():
            answer[i+k, j+l] = answer.get((i+k, j+l), 0) + x*y
    return answer


def fourier_kernel(error, coefficient):
    a, j, k = error
    b, z, t = coefficient
    polynomial = {(0, 0): 1}
    for multiplicity, factor in (
        (5-j-k, {(0, 0): 1, (1, 0): 1, (0, 1): 2}),
        (j, {(0, 0): 1, (1, 0): 1, (0, 1): -2}),
        (k, {(0, 0): 1, (1, 0): -1}),
    ):
        for _ in range(multiplicity):
            polynomial = multiply(polynomial, factor)
    tail_size = orbit_size((0, z, t))
    spectator_factor = F(-1, 3) if a and b else F(1)
    return F(polynomial.get((z, t), 0), tail_size*32)*spectator_factor


def dual_certificates():
    """Check exact rational dual identities; no numerical optimizer is used."""
    columns = [label for label in categories() if label[2] % 2 == 0]
    def unit(label):
        return [F(int(column == label)) for column in columns]
    equalities = {("norm",): (unit((0, 0, 0)), F(1))}
    inequalities = {}
    for error in categories():
        transform = [fourier_kernel(error, column) for column in columns]
        spin = [value*(-1)**sum(column) for value, column in zip(transform, columns)]
        inequalities["B", error] = [-value for value in transform]
        inequalities["shadow", error] = [-value for value in spin]
        a, j, k = error
        if k % 2 == 0:
            complement = (a, 5-j-k, k)
            row = [value-F(int(column == error)+int(column == complement), orbit_size(error))
                   for value, column in zip(transform, columns)]
            equalities["diag", error] = (row, F(0))
        if sum(error) <= 2:
            row = [value-F(int(column == error), orbit_size(error))
                   for value, column in zip(transform, columns)]
            equalities["KL", error] = (row, F(0))
        if k % 2 and sum(error) % 2:
            equalities["shadowzero", error] = (spin, F(0))

    specifications = [
        ("active_one_body_zero", (0, 1, 0), [
            ("KL", (0,0,0), -3), ("KL", (0,1,0), -10),
            ("KL", (0,2,0), "-37/4"), ("KL", (0,0,1), -10),
            ("KL", (0,1,1), -20), ("diag", (0,0,2), 15),
            ("KL", (0,0,2), -20), ("diag", (0,0,4), 4),
            ("KL", (1,0,0), -6), ("KL", (1,1,0), "-33/4"),
            ("KL", (1,0,1), -30), ("shadowzero", (1,1,3), -18),
        ], [("shadow", (0,0,0), -2), ("shadow", (0,2,0), -10),
            ("shadow", (0,2,1), "-15/2")]),
        ("active_transverse_pair_zero", (0,0,2), [
            ("KL", (0,0,0), -3), ("KL", (0,1,0), -10),
            ("diag", (0,2,0), -1), ("KL", (0,0,1), -10),
            ("KL", (0,1,1), -20), ("diag", (0,0,2), 48),
            ("KL", (0,0,2), -20), ("KL", (1,0,0), -6),
            ("KL", (1,0,1), -30), ("shadowzero", (1,1,3), -84),
        ], [("shadow", (0,0,0), -2), ("shadow", (0,2,0), -10),
            ("shadow", (0,0,1), -16), ("shadow", (0,2,1), -6),
            ("shadow", (1,1,1), -6)]),
        ("active_three_body_zero", (0,1,2), [
            ("KL", (0,0,0), -6), ("KL", (0,1,0), -20),
            ("KL", (0,0,1), -20), ("KL", (0,1,1), -40),
            ("KL", (0,0,2), -40), ("KL", (1,0,0), -15),
            ("diag", (1,1,0), 5), ("KL", (1,0,1), -60),
            ("diag", (1,1,2), -80), ("shadowzero", (0,0,1), -10),
        ], [("shadow", (0,0,0), -4), ("shadow", (0,2,0), -20),
            ("shadow", (0,2,1), -70)]),
        ("spectator_times_active_ZZ_zero", (1,2,0), [
            ("KL", (0,0,0), -4), ("KL", (0,1,0), -10),
            ("KL", (0,0,1), -10), ("KL", (0,1,1), -20),
            ("diag", (0,0,2), 20), ("KL", (0,0,2), -20),
            ("KL", (1,0,0), -6), ("KL", (1,0,1), -30),
            ("diag", (1,1,2), -40), ("shadowzero", (1,1,3), -40),
        ], [("shadow", (0,0,0), -2), ("shadow", (0,2,0), -10),
            ("shadow", (0,2,1), -20)]),
        ("active_ZZZ_zero", (0,3,0), [
            ("diag", (0,2,0), 10), ("KL", (0,2,0), -10),
        ], []),
        ("A1_plus_A2_plus_A3_at_least_one", None, [
            ("norm", None, 1), ("KL", (0,0,0), 1),
            ("KL", (0,1,0), -5), ("KL", (1,0,0), -3),
            ("KL", (1,1,0), 15), ("KL", (1,0,1), -30),
            ("shadowzero", (0,0,1), -5),
            ("shadowzero", (0,0,3), -40),
            ("shadowzero", (0,0,5), -8),
        ], [("shadow", (0,2,0), -20), ("B", (0,0,1), -10),
            ("shadow", (0,2,1), -45)]),
    ]
    reports = []
    for name, target, eq_terms, ineq_terms in specifications:
        objective = ([F(int(sum(column) in (1,2,3))) for column in columns]
                     if target is None else [-x for x in unit(target)])
        remainder = objective.copy()
        bound = F(0)
        for kind, label, coefficient in eq_terms:
            coefficient = F(coefficient)
            row, rhs = equalities[(kind,) if label is None else (kind, label)]
            remainder = [x-coefficient*y for x, y in zip(remainder, row)]
            bound += coefficient*rhs
        for kind, label, coefficient in ineq_terms:
            coefficient = F(coefficient)
            assert coefficient <= 0
            remainder = [x-coefficient*y for x, y in
                         zip(remainder, inequalities[kind, label])]
        assert all(value >= 0 for value in remainder), (name, remainder)
        assert bound == (1 if target is None else 0)
        reports.append({"name": name, "proved_lower_bound": str(bound),
                        "equality_terms": eq_terms, "inequality_terms": ineq_terms,
                        "nonnegative_variable_remainder": [
                            {"category": label, "coefficient": str(value)}
                            for label, value in zip(columns, remainder) if value]})
    return reports


def stabilizer_boundary_certificate():
    """Exact symplectic checks for the charged-shortening counterexample."""
    alphabet = "IXYZ"
    def anticommutes(left, right):
        return sum(a != b and a != "I" and b != "I"
                   for a, b in zip(left, right)) % 2
    def product_label(left, right):
        return "".join(alphabet[alphabet.index(a)^alphabet.index(b)]
                       for a,b in zip(left,right))
    # Labels are sufficient for membership and distance. Phases of the
    # generators are fixed to +1 by their CZ-conjugation construction.
    generators = ["XZZXII", "IXZZXZ", "XIXZZI", "ZXIXZI", "IIIIZX"]
    assert all(not anticommutes(a,b) for a in generators for b in generators)
    group = {"IIIIII"}
    for generator in generators:
        group |= {product_label(word, generator) for word in tuple(group)}
    assert len(group) == 32
    logical = "IXYXZX"
    assert all(not anticommutes(logical, generator) for generator in generators)
    assert logical not in group and logical.count("I") == 1 and logical[0] == "I"
    checked = 0
    low_normalizer = []
    for letters in itertools.product(alphabet, repeat=6):
        word = "".join(letters)
        weight = 6-word.count("I")
        if 1 <= weight <= 2:
            checked += 1
            if all(not anticommutes(word,g) for g in generators):
                assert word in group
                low_normalizer.append(word)
    witness = "IXYXII"
    assert all(not anticommutes(witness,g) for g in generators)
    assert witness not in group and 6-witness.count("I") == 3
    assert low_normalizer == ["IIIIZX"]
    return {"construction": "CZ(data qubit 5, ancilla 6) applied to perfect-five code times |+>",
            "positive_stabilizer_generators": generators,
            "stabilizer_rank": 5, "low_weight_errors_checked": checked,
            "exact_distance": 3, "weight_three_logical_witness": witness,
            "class3_logical_involution": logical,
            "inactive_site_zero_based": 0,
            "surviving_active_weight_two_stabilizer": "IIIIZX",
            "conclusion": "Every nonzero inactive-site measurement outcome retains a weight-two stabilizer; no such outcome is a perfect-five code."}


def verify():
    # The value of A[label] is the SUM over its complete physical orbit.
    values = {
        (0, 0, 0): 1,
        (0, 2, 2): 4,
        (0, 0, 4): 1,
        (0, 1, 4): 2,
        (1, 3, 0): 1,
        (1, 0, 2): 1,
        (1, 1, 2): 6,
        (1, 2, 2): 7,
        (1, 3, 2): 2,
        (1, 0, 4): 6,
        (1, 1, 4): 1,
    }
    all_labels = categories()
    a = {label: F(values.get(label, 0)) for label in all_labels}
    assert a[0, 0, 0] == 1 and sum(a.values()) == 32
    assert all(value >= 0 for value in a.values())
    assert all(a[label] == 0 for label in all_labels if label[2] % 2)
    b, shadow = {}, {}
    for error in all_labels:
        b[error] = sum(fourier_kernel(error, label)*value
                       for label, value in a.items())
        shadow[error] = sum(fourier_kernel(error, label)*value
                            * (-1)**sum(label) for label, value in a.items())
        assert b[error] >= 0 and shadow[error] >= 0
        ordinary = a[error]/orbit_size(error)
        assert b[error] >= ordinary
        if sum(error) <= 2:
            assert b[error] == ordinary
        spectator, z_count, transverse_count = error
        if transverse_count % 2 == 0:
            complement = (spectator, 5-z_count-transverse_count,
                          transverse_count)
            assert b[error] == ordinary + a[complement]/orbit_size(error)
        elif sum(error) % 2:
            assert shadow[error] == 0

    enumerator = [sum(value for label, value in a.items() if sum(label) == w)
                  for w in range(7)]
    assert enumerator == [1, 0, 0, 1, 12, 15, 3]

    # Exact Walsh decomposition on each four-bit parity face.
    walsh_checks = []
    for parity in (0, 1):
        points = [bits for bits in itertools.product((0, 1), repeat=4)
                  if sum(bits) % 2 == parity]
        masks = [(), (0,), (1,), (2,), (3,), (0, 1), (0, 2), (0, 3)]
        rows = [[(-1)**sum(bits[i] for i in mask) for bits in points]
                for mask in masks]
        gram = [[sum(x*y for x, y in zip(left, right)) for right in rows]
                for left in rows]
        assert gram == [[8 if i == j else 0 for j in range(8)]
                        for i in range(8)]
        walsh_checks.append({"parity": parity, "face_size": 8,
                             "constrained_character_rank": 5,
                             "surviving_character_dimension": 3})

    return {
        "status": "exact_certificate_passed",
        "scope": "Formal nonnegative squared-coefficient array; not a quantum code.",
        "enumerator": [int(x) for x in enumerator],
        "category_convention": ["spectator_nonidentity", "tail_Z", "tail_X_or_Y"],
        "nonzero_category_masses": [
            {"category": list(label), "mass": str(value),
             "orbit_size": orbit_size(label)}
            for label, value in a.items() if value
        ],
        "checks": {
            "arithmetic": "fractions.Fraction; exact",
            "symmetry_refined_categories": len(all_labels),
            "normalization_and_rank_two_purity_sum": True,
            "parity_support": True,
            "all_weight_at_most_two_KL_Fourier_equalities": True,
            "all_B_ge_A_and_shadow_nonnegative": True,
            "all_commuting_error_B_equals_A_plus_DA": True,
            "odd_weight_anticommuting_error_shadow_zero": True,
            "walsh_faces": walsh_checks,
        },
        "conclusion": "These scalar constraints cannot imply the class-3 L-line converse.",
        "proved_class3_linear_consequences": dual_certificates(),
        "shortening_counterexample": stabilizer_boundary_certificate(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[2]/"tmp/orbit3-scalar-regenerated.json")
    args = parser.parse_args()
    report = verify()
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print("Exact class-3 scalar obstruction and parity-edge certificates passed.")
    print(args.output)


if __name__ == "__main__":
    main()
