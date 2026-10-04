#!/usr/bin/env python3
"""Rebuild orbit-2/3 finite coefficient payloads from exact Pauli arithmetic.

These checks are generator provenance, not Lean proofs of actual encoders.
The generated Lean declarations and encoder semantic bridges have separate
kernel obligations. No manuscript files or installed third-party packages
are required by this regeneration check.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def module(name, folder='certificates'):
    path = ROOT / 'tools' / folder / (name + '.py')
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def rebuild_orbit2():
    v = module('orbit2_exact_certificate')
    matrix = v.build_integer_certificate()
    zero = {i for i, (a, b) in enumerate(v.MONOMIALS)
            if not v.IS_B[a] and not v.IS_B[b]}
    characters = [v.MUL[v.T_IDS[a]][v.T_IDS[b]] for a, b in v.MONOMIALS]
    require(len(zero) == 36, 'orbit 2: wrong zero-coordinate count')
    require(all(r not in zero and c not in zero for r, c in matrix),
            'orbit 2: nonzero entry in a zero row')
    require(all(characters[r] == characters[c] for r, c in matrix),
            'orbit 2: nonzero off-block entry')
    groups = defaultdict(list)
    for i, character in enumerate(characters):
        if i not in zero:
            groups[character].append(i)
    blocks = []
    for character, indices in sorted(groups.items()):
        block = [[matrix.get((r, c), 0) for c in indices] for r in indices]
        shifted = [[x - 4 * (i == j) for j, x in enumerate(row)]
                   for i, row in enumerate(block)]
        blocks.append({'character': v.label_string(v.LABELS[character]),
                       'monomial_indices': indices, 'matrix': block,
                       'ldlt_pivots_of_matrix_minus_4I':
                           [str(x) for x in v.exact_ldlt_positive(shifted)]})
    require(len(blocks) == 111 and sum(len(b['matrix']) for b in blocks) == 492,
            'orbit 2: wrong partition dimensions')
    sparse = json.dumps(sorted((r, c, value) for (r, c), value in matrix.items()),
                        separators=(',', ':'))
    return {'description': 'Exact Orbit-2 global common-J rigidity certificate',
            'pauli_order': [v.label_string(p) for p in v.T_LABELS],
            'monomials': [list(p) for p in v.MONOMIALS],
            'zero_monomials': sorted(zero),
            'sparse_matrix_sha256': sha256(sparse.encode()).hexdigest(),
            'blocks': blocks}


def rebuild_orbit3(data):
    v = module('orbit3_exact_sextic_certificate')
    _, lookup, entries, pair_lookup, _ = v.coordinate_tables()
    square = [0] * 269
    polynomial = data['cubic_polynomial']
    for t, a in polynomial:
        for u, b in polynomial:
            j = entries[lookup[tuple(t)]][lookup[tuple(u)]]
            require(j >= 0, 'orbit 3: a positive-square coefficient was removed')
            square[j] += a * b
    target = [0] * 269
    target_count = 0
    for r in range(4096):
        if v.category(r) == (1, 0, 2):
            target_count += 1
            row = v.moment_row((r, r, 0), entries, pair_lookup)
            target = [a + b for a, b in zip(target, row)]
    require(target_count == 120, 'orbit 3: wrong full-target size')
    rows, multipliers = [], []
    constraints = v.constraints()
    for term in data['terms']:
        kind = term['kind']
        if kind == 'kl':
            labels = term['paulis']
            require(any(r in constraints for r in labels), 'invalid KL/scalar row')
            row = v.moment_row(labels, entries, pair_lookup)
        elif kind == 'spin':
            row = v.spin_row(term['triple'], lookup, entries)
        elif kind == 'H':
            labels = term['paulis']
            transformed, sign = v.hadamard(labels)
            row = v.moment_row(labels, entries, pair_lookup)
            other = v.moment_row(transformed, entries, pair_lookup)
            row = [a - sign * b for a, b in zip(row, other)]
        else:
            raise ValueError('invalid certificate row kind')
        divisor = int(term['row_divisor'])
        require(divisor != 0 and all(x % divisor == 0 for x in row),
                'nonintegral primitive row')
        rows.append([x // divisor for x in row])
        multipliers.append(str(Fraction(term['multiplier'])))
    require(all(3 * target[j] + 1280 * square[j] ==
                80 * sum(Fraction(m) * row[j] for m, row in zip(multipliers, rows))
                for j in range(269)), 'orbit 3: exact coefficient identity failed')
    return {'target': target, 'square': square, 'rows': rows, 'multipliers': multipliers}


def check(relative, rebuilt):
    stored = json.loads((ROOT / relative).read_text(encoding='utf-8'))
    require(stored == json.loads(json.dumps(rebuilt)), 'rebuilt payload differs: ' + relative)
    print('PASS exact regeneration:', relative, flush=True)


def check_generated_lean():
    """Regenerate independent candidate sources and compare every byte."""
    output_dir = ROOT / 'tmp/orbit-generated-source-regeneration'
    output_dir.mkdir(parents=True, exist_ok=True)
    variants = [
        ('emit_orbit3_scalar', 'scalar-certificate.json', 'Orbit3Scalar'),
        ('emit_orbit3_sextic_identity', 'reduced-coefficients.json', 'Orbit3SexticIdentity'),
        ('emit_orbit3_positive_square', 'certificate.json', 'Orbit3PositiveSquare'),
        ('emit_orbit3_category_fourier', None, 'Orbit3CategoryFourier'),
        ('emit_orbit3_category_rows', None, 'Orbit3CategoryRows'),
        ('emit_orbit3_pauli_constraints', 'certificate.json', 'Orbit3PauliConstraints'),
        ('emit_orbit3_hadamard_constraints', 'certificate.json', 'Orbit3HadamardConstraints'),
        ('emit_orbit3_spin_constraints', 'certificate.json', 'Orbit3SpinConstraints'),
        ('emit_orbit3_row_metadata', 'certificate.json', 'Orbit3RowMetadata'),
        ('emit_orbit3_cubic_triples', None, 'Orbit3CubicTriples'),
        ('emit_orbit3_permutation_metadata', None, 'Orbit3PermutationMetadata'),
        ('emit_spectator_clifford', None, 'SpectatorClifford'),
    ]
    for generator, source, basename in variants:
        output = output_dir / (basename + '.lean')
        emit = module(generator, 'generators').generate
        if source is None:
            emit(output)
        else:
            emit(ROOT / 'results/orbit3-kernel' / source, output)
        original = ROOT / 'SixQubit/Generated' / (basename + '.lean')
        require(output.read_bytes() == original.read_bytes(),
                'generated Lean source differs: ' + str(original.relative_to(ROOT)))
        print('PASS byte-exact Lean regeneration:', basename, flush=True)
    generated_dir = output_dir / 'Orbit3Coordinates'
    aggregate = output_dir / 'Orbit3ReducedCoordinates.lean'
    module('emit_orbit3_reduced_coordinates', 'generators').generate(generated_dir, aggregate)
    generated = [(aggregate, ROOT / 'SixQubit/Generated/Orbit3ReducedCoordinates.lean')]
    generated.extend((p, ROOT / 'SixQubit/Generated/Orbit3Coordinates' / p.name)
                     for p in sorted(generated_dir.glob('*.lean')))
    require(len(generated) == 18, 'wrong reduced-coordinate generated source count')
    for rebuilt, original in generated:
        require(rebuilt.read_bytes() == original.read_bytes(),
                'generated Lean source differs: ' + str(original.relative_to(ROOT)))
        print('PASS byte-exact Lean regeneration:',
              original.relative_to(ROOT).as_posix(), flush=True)
    module('orbit_generated_sources', 'verification').main()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', choices=['orbit2', 'orbit3', 'scalar', 'lean'])
    args = parser.parse_args()
    if args.only in (None, 'orbit2'):
        check('results/orbit2-kernel/gram-blocks.json', rebuild_orbit2())
    if args.only in (None, 'orbit3'):
        data = json.loads((ROOT / 'results/orbit3-kernel/certificate.json').read_text(encoding='utf-8'))
        check('results/orbit3-kernel/reduced-coefficients.json', rebuild_orbit3(data))
    if args.only in (None, 'scalar'):
        check('results/orbit3-kernel/scalar-certificate.json', module('orbit3_scalar_certificate').verify())
    if args.only in (None, 'lean'):
        check_generated_lean()


if __name__ == '__main__':
    main()
