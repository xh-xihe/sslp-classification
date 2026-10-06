#!/usr/bin/env python3
"""Emit the fully kernel-checked certificate for ``BetaExact 6 9``.

The generator is deliberately outside the trusted argument.  It performs a
small amount of exact rational bookkeeping only to *propose* a sharding and
symmetry reduction.  Every proposed fact is checked again in generated Lean:

* the 79 full-rank representatives use explicit ``3 x 6`` integer matrices;
* every numerical leaf is an ordinary-kernel ``decide`` proof of one
  ``FastPairChunk`` containing at most sixteen bottom-row pairs;
* each representative aggregate proves all 2080 unordered row-code pairs;
* every full-rank target checks its explicit integral ``3 x 3`` transform,
  its determinant ``+-1``, its genuine ``Fin 6`` column equivalence, and all
  18 entries of the transported top block;
* every rank-deficient target checks an explicit nonzero integral relation
  among its top rows, so all completions have determinant zero;
* a proof-only six-level ``Fin 8`` tree covers every weakly increasing top
  pattern, and the final theorem returns through ``AllCanonicalBottomBound``
  to the semantic ``BetaBound`` definition.

Consequently no Python count, orbit label, rational matrix, permutation, or
rank decision is an assumption of the Lean theorem.  Omitting a target makes
the generated coverage tree fail to elaborate.  A wrong transform, relation,
permutation, matrix entry, or numerical inequality fails in its own bounded
Lean theorem.

There is no ``native_decide``, ``sorry``, axiom, heartbeat override, or
external solver in the emitted source.  This script only writes source and
never invokes Lean or Lake.  Full generation requires the explicit
``--confirm-full-generation`` flag because it creates roughly 1,100 small
modules.  Same-depth coverage proofs are grouped at no more than 32 theorem
commands per module; heartbeat accounting still resets at each theorem.
Compile the modules serially with the repository's resource-safe wrapper.
The completed run writes an exact SHA-256 source manifest and a topological
``serial-build-order.txt``.  At the start of a replacement run the old final
certificate and control files are invalidated; unexpected old Lean shards are
rejected instead of being silently mixed into a new result.
For proof-tree migrations, ``--fresh-staging-root`` requires a new empty
workspace-local filesystem root and guarantees that the live
``MainTheory/Generated`` tree is neither that root nor its ancestor/descendant.
"""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import combinations_with_replacement, permutations
from math import gcd
from pathlib import Path
from typing import TypeAlias


MODULE_PREFIX = "MainTheory.Generated."
BASE_MODULE = "MainTheory.Generated.BinaryBetaSixKernel"
WIDTH = 64
TOP_ALPHABET = 8
BOUND = 9
CHUNK_SIZE = 16
DEFAULT_CHUNKS_PER_MODULE = 16
DEFAULT_TARGETS_PER_MODULE = 16
DEFAULT_COVER_THEOREMS_PER_MODULE = 32


Pattern: TypeAlias = tuple[int, int, int, int, int, int]
Vector3: TypeAlias = tuple[int, int, int]
RatVector3: TypeAlias = tuple[Fraction, Fraction, Fraction]
Matrix3: TypeAlias = tuple[Vector3, Vector3, Vector3]
RatMatrix3: TypeAlias = tuple[RatVector3, RatVector3, RatVector3]
TopRows: TypeAlias = tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]
Basis: TypeAlias = tuple[int, int, int]
Signature: TypeAlias = tuple[int, tuple[RatVector3, ...]]
Chunk: TypeAlias = tuple[int, int, int]  # fixed a, start b, count


@dataclass(frozen=True)
class CanonicalData:
    signature: Signature
    basis: Basis


@dataclass(frozen=True)
class FullRankTarget:
    representative: int
    transform: Matrix3
    permutation: tuple[int, int, int, int, int, int]
    inverse_permutation: tuple[int, int, int, int, int, int]


@dataclass(frozen=True)
class SingularTarget:
    relation: Vector3
    witness: int


TargetData: TypeAlias = FullRankTarget | SingularTarget


def write_if_changed(path: Path, text: str) -> None:
    """Write UTF-8 source without touching an unchanged file."""
    if path.exists() and path.read_text(encoding="utf-8") == text:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def module_path(output_root: Path, module: str) -> Path:
    if not module.startswith(MODULE_PREFIX):
        raise ValueError(f"module lies outside {MODULE_PREFIX}: {module}")
    relative = module[len(MODULE_PREFIX) :].replace(".", "/") + ".lean"
    return output_root / relative


def column(code: int) -> Vector3:
    if not 0 <= code < TOP_ALPHABET:
        raise ValueError(f"not a three-bit column code: {code}")
    return ((code >> 0) & 1, (code >> 1) & 1, (code >> 2) & 1)


def columns(pattern: Pattern) -> tuple[Vector3, ...]:
    return tuple(column(code) for code in pattern)


def top_rows(pattern: Pattern) -> TopRows:
    cols = columns(pattern)
    return tuple(tuple(col[i] for col in cols) for i in range(3))  # type: ignore[return-value]


def determinant3(matrix: Matrix3) -> int:
    a, b, c = matrix[0]
    d, e, f = matrix[1]
    g, h, i = matrix[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def inverse3(matrix: Matrix3) -> RatMatrix3:
    a, b, c = matrix[0]
    d, e, f = matrix[1]
    g, h, i = matrix[2]
    det = determinant3(matrix)
    if det == 0:
        raise ValueError("attempted to invert a singular 3 x 3 matrix")
    adjugate = (
        (e * i - f * h, c * h - b * i, b * f - c * e),
        (f * g - d * i, a * i - c * g, c * d - a * f),
        (d * h - e * g, b * g - a * h, a * e - b * d),
    )
    return tuple(
        tuple(Fraction(entry, det) for entry in row) for row in adjugate
    )  # type: ignore[return-value]


def basis_matrix(cols: tuple[Vector3, ...], basis: Basis) -> Matrix3:
    return tuple(
        tuple(cols[basis[j]][i] for j in range(3)) for i in range(3)
    )  # type: ignore[return-value]


def rat_matvec(matrix: RatMatrix3, vector: Vector3) -> RatVector3:
    return tuple(
        sum((matrix[i][j] * vector[j] for j in range(3)), Fraction(0))
        for i in range(3)
    )  # type: ignore[return-value]


def rat_matmul(left: Matrix3, right: RatMatrix3) -> RatMatrix3:
    return tuple(
        tuple(
            sum((Fraction(left[i][k]) * right[k][j] for k in range(3)), Fraction(0))
            for j in range(3)
        )
        for i in range(3)
    )  # type: ignore[return-value]


def int_matvec(matrix: Matrix3, vector: Vector3) -> Vector3:
    return tuple(
        sum(matrix[i][j] * vector[j] for j in range(3))
        for i in range(3)
    )  # type: ignore[return-value]


@lru_cache(maxsize=None)
def canonical_data(pattern: Pattern) -> CanonicalData | None:
    """Exact GL(3,Q)-plus-column signature, retaining a witnessing basis.

    The absolute basis determinant is part of the signature.  Thus equal
    signatures propose a determinant-one rational change of basis.  The
    stronger facts that its entries are integral and its determinant is +-1
    are checked below and, independently, in generated Lean.
    """
    cols = columns(pattern)
    best: CanonicalData | None = None
    for raw_basis in permutations(range(6), 3):
        basis: Basis = raw_basis
        matrix = basis_matrix(cols, basis)
        det = determinant3(matrix)
        if det == 0:
            continue
        inv = inverse3(matrix)
        coordinates = tuple(rat_matvec(inv, col) for col in cols)
        signature: Signature = (abs(det), tuple(sorted(coordinates)))
        candidate = CanonicalData(signature, basis)
        if best is None or (candidate.signature, candidate.basis) < (
            best.signature,
            best.basis,
        ):
            best = candidate
    return best


def cross(left: Vector3, right: Vector3) -> Vector3:
    return (
        left[1] * right[2] - left[2] * right[1],
        left[2] * right[0] - left[0] * right[2],
        left[0] * right[1] - left[1] * right[0],
    )


def dot(left: Vector3, right: Vector3) -> int:
    return sum(left[i] * right[i] for i in range(3))


def primitive(vector: Vector3) -> Vector3:
    divisor = gcd(gcd(abs(vector[0]), abs(vector[1])), abs(vector[2]))
    if divisor == 0:
        raise ValueError("zero vector has no primitive normalization")
    result = tuple(value // divisor for value in vector)
    first = next(value for value in result if value != 0)
    if first < 0:
        result = tuple(-value for value in result)
    return result  # type: ignore[return-value]


def singular_relation(pattern: Pattern) -> SingularTarget:
    cols = columns(pattern)
    relation: Vector3 | None = None
    for i in range(6):
        for j in range(i + 1, 6):
            candidate = cross(cols[i], cols[j])
            if candidate != (0, 0, 0):
                relation = primitive(candidate)
                break
        if relation is not None:
            break
    if relation is None:
        nonzero = next((col for col in cols if col != (0, 0, 0)), None)
        if nonzero is None:
            relation = (1, 0, 0)
        elif nonzero[0] != 0 or nonzero[1] != 0:
            relation = primitive((nonzero[1], -nonzero[0], 0))
        else:
            relation = (1, 0, 0)
    if relation == (0, 0, 0):
        raise RuntimeError(f"zero relation proposed for {pattern}")
    if any(dot(relation, col) != 0 for col in cols):
        raise RuntimeError(f"invalid singular relation {relation} for {pattern}")
    witness = next(i for i, value in enumerate(relation) if value != 0)
    return SingularTarget(relation, witness)


def full_rank_transport(
    representative: Pattern,
    target: Pattern,
    representative_id: int,
) -> FullRankTarget:
    rep_data = canonical_data(representative)
    target_data = canonical_data(target)
    if rep_data is None or target_data is None:
        raise RuntimeError("full-rank transport received a singular pattern")
    if rep_data.signature != target_data.signature:
        raise RuntimeError("patterns with different signatures were grouped")
    rep_basis = basis_matrix(columns(representative), rep_data.basis)
    target_basis = basis_matrix(columns(target), target_data.basis)
    rational_transform = rat_matmul(target_basis, inverse3(rep_basis))
    if any(entry.denominator != 1 for row in rational_transform for entry in row):
        raise RuntimeError(
            f"signature class is not integral: {representative} -> {target}"
        )
    transform: Matrix3 = tuple(
        tuple(int(entry) for entry in row) for row in rational_transform
    )  # type: ignore[assignment]
    if abs(determinant3(transform)) != 1:
        raise RuntimeError(
            f"non-unimodular transform: {representative} -> {target}: {transform}"
        )

    transformed = tuple(int_matvec(transform, col) for col in columns(representative))
    available: dict[Vector3, list[int]] = {}
    for index, col in enumerate(transformed):
        available.setdefault(col, []).append(index)
    forward_list: list[int] = []
    for col in columns(target):
        candidates = available.get(col, [])
        if not candidates:
            raise RuntimeError(
                f"transformed columns do not match: {representative} -> {target}"
            )
        forward_list.append(candidates.pop(0))
    if any(indices for indices in available.values()):
        raise RuntimeError("column matching left an unused transformed column")
    if len(set(forward_list)) != 6:
        raise RuntimeError("proposed column map is not injective")
    inverse_list = [0] * 6
    for target_index, source_index in enumerate(forward_list):
        inverse_list[source_index] = target_index
    if any(
        transformed[forward_list[j]] != columns(target)[j] for j in range(6)
    ):
        raise RuntimeError("column permutation orientation is wrong")
    return FullRankTarget(
        representative_id,
        transform,
        tuple(forward_list),  # type: ignore[arg-type]
        tuple(inverse_list),  # type: ignore[arg-type]
    )


def classify_patterns() -> tuple[
    list[Pattern],
    list[Pattern],
    dict[Pattern, TargetData],
]:
    patterns: list[Pattern] = list(
        combinations_with_replacement(range(TOP_ALPHABET), 6)
    )  # type: ignore[assignment]
    if len(patterns) != 1716:
        raise RuntimeError(f"expected 1716 top patterns, got {len(patterns)}")

    classes: dict[Signature, list[Pattern]] = {}
    singular: list[Pattern] = []
    for pattern in patterns:
        data = canonical_data(pattern)
        if data is None:
            singular.append(pattern)
        else:
            classes.setdefault(data.signature, []).append(pattern)
    if sum(len(group) for group in classes.values()) != 1238:
        raise RuntimeError("expected exactly 1238 full-rank patterns")
    if len(singular) != 478:
        raise RuntimeError(f"expected 478 rank-deficient patterns, got {len(singular)}")

    representatives = sorted(min(group) for group in classes.values())
    if len(representatives) != 79:
        raise RuntimeError(
            f"expected 79 integral-unimodular signature classes, got {len(representatives)}"
        )
    representative_id = {
        canonical_data(pattern).signature: index  # type: ignore[union-attr]
        for index, pattern in enumerate(representatives)
    }
    representative_by_signature = {
        canonical_data(pattern).signature: pattern  # type: ignore[union-attr]
        for pattern in representatives
    }

    target_data: dict[Pattern, TargetData] = {}
    for pattern in patterns:
        data = canonical_data(pattern)
        if data is None:
            target_data[pattern] = singular_relation(pattern)
        else:
            rep = representative_by_signature[data.signature]
            rid = representative_id[data.signature]
            target_data[pattern] = full_rank_transport(rep, pattern, rid)
    if set(target_data) != set(patterns):
        raise RuntimeError("target classification does not cover every pattern")
    return patterns, representatives, target_data


def lean_int(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def lean_matrix(rows: tuple[tuple[int, ...], ...]) -> str:
    rendered = ";\n     ".join(
        ", ".join(lean_int(value) for value in row) for row in rows
    )
    return f"!![{rendered}]"


def lean_vector(values: tuple[int, ...]) -> str:
    return "![" + ", ".join(lean_int(value) for value in values) + "]"


def representative_base_module(representative: int) -> str:
    return f"{BASE_MODULE}.Representative.R{representative:03d}.Base"


def representative_arithmetic_module(representative: int, shard: int) -> str:
    return (
        f"{BASE_MODULE}.Representative.R{representative:03d}."
        f"Arithmetic.Shard{shard:03d}"
    )


def representative_aggregate_module(representative: int) -> str:
    return f"{BASE_MODULE}.Representative.R{representative:03d}.Aggregate"


def target_module(shard: int) -> str:
    return f"{BASE_MODULE}.Target.Shard{shard:03d}"


def cover_module(depth: int, shard: int) -> str:
    return f"{BASE_MODULE}.Cover.K{depth}.Shard{shard:03d}"


def cover_theorem_name(prefix: tuple[int, ...]) -> str:
    if not prefix:
        return "cover_root"
    return "cover_p_" + "_".join(map(str, prefix))


def certificate_module() -> str:
    return f"{BASE_MODULE}.Certificate"


def all_cover_prefixes(patterns: list[Pattern]) -> set[tuple[int, ...]]:
    prefixes: set[tuple[int, ...]] = {()}
    for pattern in patterns:
        for depth in range(1, 6):
            prefixes.add(pattern[:depth])
    if len(prefixes) != 1287:
        raise RuntimeError(f"expected 1287 proof-tree nodes, got {len(prefixes)}")
    return prefixes


def cover_plan(
    patterns: list[Pattern],
    theorems_per_module: int,
) -> tuple[dict[tuple[int, ...], str], list[str]]:
    """Assign same-depth coverage theorems to bounded proof-only modules."""
    prefixes = all_cover_prefixes(patterns)
    owner: dict[tuple[int, ...], str] = {}
    modules: list[str] = []
    for depth in range(5, -1, -1):
        at_depth = sorted(prefix for prefix in prefixes if len(prefix) == depth)
        for start in range(0, len(at_depth), theorems_per_module):
            shard = start // theorems_per_module
            module = cover_module(depth, shard)
            modules.append(module)
            for prefix in at_depth[start : start + theorems_per_module]:
                if prefix in owner:
                    raise RuntimeError(f"duplicate coverage owner for {prefix}")
                owner[prefix] = module
    if set(owner) != prefixes:
        raise RuntimeError("coverage module plan omits a canonical prefix")
    return owner, modules


def expected_module_order(
    patterns: list[Pattern],
    representatives: list[Pattern],
    chunks_per_module: int,
    targets_per_module: int,
    cover_theorems_per_module: int,
) -> list[str]:
    """Topological order consumed by the serial build wrapper."""
    modules: list[str] = []
    modules.extend(
        representative_base_module(representative)
        for representative in range(len(representatives))
    )
    arithmetic_modules_per_rep = (
        len(all_chunks()) + chunks_per_module - 1
    ) // chunks_per_module
    modules.extend(
        representative_arithmetic_module(representative, shard)
        for representative in range(len(representatives))
        for shard in range(arithmetic_modules_per_rep)
    )
    modules.extend(
        representative_aggregate_module(representative)
        for representative in range(len(representatives))
    )
    target_module_count = (
        len(patterns) + targets_per_module - 1
    ) // targets_per_module
    modules.extend(target_module(shard) for shard in range(target_module_count))
    _, cover_modules = cover_plan(patterns, cover_theorems_per_module)
    modules.extend(cover_modules)
    modules.append(certificate_module())
    if len(modules) != len(set(modules)):
        raise RuntimeError("generated module plan contains duplicate names")
    return modules


def kernel_output_directory(output_root: Path) -> Path:
    return output_root / "BinaryBetaSixKernel"


def prepare_output(
    output_root: Path,
    module_order: list[str],
) -> tuple[Path, Path]:
    """Reject stale unknown Lean files and invalidate an old final result.

    In particular, if generation is interrupted after this point, neither a
    success manifest nor the final ``Certificate.lean`` remains.  We never
    delete arithmetic or proof shards: a changed file plan must be generated
    in a fresh staging root instead of silently mixing runs.
    """
    expected = {module_path(output_root, module) for module in module_order}
    kernel_root = kernel_output_directory(output_root)
    existing = set(kernel_root.rglob("*.lean")) if kernel_root.exists() else set()
    unexpected = sorted(existing - expected)
    if unexpected:
        rendered = "\n  ".join(str(path) for path in unexpected[:20])
        suffix = "" if len(unexpected) <= 20 else f"\n  ... and {len(unexpected) - 20} more"
        raise RuntimeError(
            "refusing to mix a new generation with unexpected Lean files; "
            "use a fresh --output-root:\n  " + rendered + suffix
        )
    manifest = kernel_root / "generation-manifest.sha256"
    build_order = kernel_root / "serial-build-order.txt"
    final_source = module_path(output_root, certificate_module())
    # These are generated control artifacts at exact, narrow paths.  Removing
    # them makes an interrupted new run visibly incomplete and recoverable by
    # rerunning this source generator.
    for path in (manifest, build_order, final_source):
        if path.exists():
            path.unlink()
    return manifest, build_order


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(text, encoding="utf-8", newline="\n")
    temporary.replace(path)


def finish_output(
    output_root: Path,
    module_order: list[str],
    manifest: Path,
    build_order: Path,
) -> None:
    expected = {module_path(output_root, module) for module in module_order}
    kernel_root = kernel_output_directory(output_root)
    actual = set(kernel_root.rglob("*.lean"))
    missing = sorted(expected - actual)
    unexpected = sorted(actual - expected)
    if missing or unexpected:
        raise RuntimeError(
            f"generated file-set mismatch: {len(missing)} missing, "
            f"{len(unexpected)} unexpected; no success manifest was written"
        )
    manifest_lines = [
        "# gen_binary_beta_six_kernel.py exact generated-source manifest",
        f"# lean_files={len(module_order)}",
        "# sha256  module",
    ]
    for module in module_order:
        source = module_path(output_root, module)
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        manifest_lines.append(f"{digest}  {module}")
    atomic_write(build_order, "\n".join(module_order) + "\n")
    atomic_write(manifest, "\n".join(manifest_lines) + "\n")


def all_chunks() -> list[Chunk]:
    result: list[Chunk] = []
    for a in range(WIDTH):
        for start in range(a, WIDTH, CHUNK_SIZE):
            result.append((a, start, min(CHUNK_SIZE, WIDTH - start)))
    if len(result) != 160:
        raise RuntimeError(f"expected 160 chunks per representative, got {len(result)}")
    if sum(count for _, _, count in result) != 2080:
        raise RuntimeError("chunks do not cover the 2080 unordered bottom-row pairs")
    return result


def chunk_name(chunk: Chunk) -> str:
    a, start, _ = chunk
    return f"chunk_{a:02d}_{start:02d}"


def emit_representative_base(
    output_root: Path,
    representative: int,
    pattern: Pattern,
) -> str:
    module = representative_base_module(representative)
    text = f"""-- Generated explicit top block for GL(3,Z) representative {representative}.
import MainTheory.BinaryDetFast

namespace {module}

/-- Column codes `{pattern}`; entries are restated explicitly so numerical
leaves never reduce the authoritative 1716-element pattern list. -/
def explicitTop : Matrix (Fin 3) (Fin 6) ℤ :=
  {lean_matrix(top_rows(pattern))}

end {module}
"""
    write_if_changed(module_path(output_root, module), text)
    return module


def emit_representative_arithmetic(
    output_root: Path,
    representative: int,
    chunks_per_module: int,
) -> dict[Chunk, str]:
    base = representative_base_module(representative)
    chunks = all_chunks()
    owner: dict[Chunk, str] = {}
    for start_index in range(0, len(chunks), chunks_per_module):
        shard = start_index // chunks_per_module
        module = representative_arithmetic_module(representative, shard)
        batch = chunks[start_index : start_index + chunks_per_module]
        theorems: list[str] = []
        for chunk in batch:
            a, start, count = chunk
            theorems.append(
                f"""/-- Ordinary-kernel arithmetic for `{count}` bottom-row pairs. -/
theorem {chunk_name(chunk)} :
    FastPairChunk {base}.explicitTop {a} {start} {count} {BOUND} := by
  decide
"""
            )
            if chunk in owner:
                raise RuntimeError(f"duplicate arithmetic owner for {chunk}")
            owner[chunk] = module
        text = f"""-- Generated bounded arithmetic shard for representative {representative}.
-- Every theorem is an independent decision problem of at most 16 pairs.
import {base}

namespace {module}

open MainTheory.BinaryDetFast

{chr(10).join(theorems)}
end {module}
"""
        write_if_changed(module_path(output_root, module), text)
    if set(owner) != set(chunks):
        raise RuntimeError("arithmetic owners do not cover every chunk")
    return owner


def conjunction_term(terms: list[str]) -> str:
    if not terms:
        raise ValueError("cannot form an empty conjunction")
    if len(terms) == 1:
        return terms[0]
    return f"⟨{terms[0]}, {conjunction_term(terms[1:])}⟩"


def right_conjunction_chain(names: list[str], indentation: int = 2) -> str:
    """Build the conjunction to which `List.Forall` reduces on a literal list."""
    if not names:
        raise ValueError("cannot form an empty conjunction")
    if len(names) == 1:
        return names[0]
    indent = " " * indentation
    return (
        f"⟨{names[0]},\n{indent}"
        f"{right_conjunction_chain(names[1:], indentation + 2)}⟩"
    )


def emit_representative_aggregate(
    output_root: Path,
    representative: int,
    owner: dict[Chunk, str],
) -> str:
    base = representative_base_module(representative)
    module = representative_aggregate_module(representative)
    imports = sorted(set(owner.values()))
    slices: list[str] = []
    for a in range(WIDTH):
        chunks = [chunk for chunk in all_chunks() if chunk[0] == a]
        qualified = [f"{owner[chunk]}.{chunk_name(chunk)}" for chunk in chunks]
        if len(chunks) == 1:
            proof = f"""by
  simpa only [FastRowSlice, FastPairChunk] using {qualified[0]}"""
        else:
            range_sum = " ++\n        ".join(
                f"List.range' {start} {count}" for _, start, count in chunks
            )
            conjunction_type = " ∧\n      ".join(
                f"FastPairChunk {base}.explicitTop {fixed} {start} {count} {BOUND}"
                for fixed, start, count in chunks
            )
            proof = f"""by
  unfold FastRowSlice
  rw [show List.range' {a} ({WIDTH} - {a}) =
        {range_sum} by decide]
  have hchunks :
      {conjunction_type} :=
    {conjunction_term(qualified)}
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks"""
        slices.append(
            f"""theorem slice_{a:02d} :
    FastRowSlice {base}.explicitTop {a} {BOUND} := {proof}
"""
        )

    literal_range = ", ".join(str(value) for value in range(WIDTH))
    table_term = right_conjunction_chain(
        [f"slice_{a:02d}" for a in range(WIDTH)], 4
    )
    text = f"""-- Generated proof-only aggregation for representative {representative}.
{chr(10).join(f'import {imported}' for imported in imports)}
import MainTheory.BinaryDetSymmetry

namespace {module}

open MainTheory.BinaryDetFast
open MainTheory.BinaryDetSymmetry

{chr(10).join(slices)}
/-- The 64 slices cover every unordered pair of six-bit bottom rows. -/
theorem table : FastTriangularTable {base}.explicitTop {BOUND} := by
  unfold FastTriangularTable
  rw [show List.range {WIDTH} = [{literal_range}] by decide]
  exact {table_term}

/-- Semantic determinant bound for all three universally quantified bottom rows. -/
theorem bottomBound : BottomDetBound {base}.explicitTop {BOUND} :=
  MainTheory.BinaryDetSymmetry.ReducedBound.bottomDetBound
    (MainTheory.BinaryDetFast.FastTriangularTable.reducedBound table)

end {module}
"""
    write_if_changed(module_path(output_root, module), text)
    return module


def emit_all_representatives(
    output_root: Path,
    representatives: list[Pattern],
    chunks_per_module: int,
) -> dict[int, str]:
    aggregates: dict[int, str] = {}
    for representative, pattern in enumerate(representatives):
        emit_representative_base(output_root, representative, pattern)
        owners = emit_representative_arithmetic(
            output_root, representative, chunks_per_module
        )
        aggregates[representative] = emit_representative_aggregate(
            output_root, representative, owners
        )
    return aggregates


def render_column_equivalence(
    name: str,
    forward: tuple[int, int, int, int, int, int],
    inverse: tuple[int, int, int, int, int, int],
) -> str:
    return f"""def {name} : Equiv.Perm (Fin 6) where
  toFun := {lean_vector(forward)}
  invFun := {lean_vector(inverse)}
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl
"""


def pattern_expression(pattern: Pattern) -> str:
    return "angle6 " + " ".join(map(str, pattern))


def render_full_rank_target(
    index: int,
    pattern: Pattern,
    data: FullRankTarget,
) -> str:
    suffix = f"{index:04d}"
    top_name = f"targetTop_{suffix}"
    transform_name = f"rowTransform_{suffix}"
    permutation_name = f"columnPerm_{suffix}"
    base = representative_base_module(data.representative)
    aggregate = representative_aggregate_module(data.representative)
    determinant = determinant3(data.transform)
    return f"""/-- Explicit target top block for canonical pattern `{pattern}`. -/
def {top_name} : Matrix (Fin 3) (Fin 6) ℤ :=
  {lean_matrix(top_rows(pattern))}

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def {transform_name} : Matrix (Fin 3) (Fin 3) ℤ :=
  {lean_matrix(data.transform)}

{render_column_equivalence(permutation_name, data.permutation, data.inverse_permutation)}
theorem literalBound_{suffix} : BottomDetBound {top_name} {BOUND} := by
  have hU : {transform_name}.det.natAbs = 1 := by
    have hdet : {transform_name}.det = {lean_int(determinant)} := by decide
    simp [hdet]
  have hrows :=
    {aggregate}.bottomBound.transformTopRows {transform_name} hU
  have hcols := hrows.permuteColumns {permutation_name}
  have htop :
      permuteTopColumns
          (transformTopRows {transform_name} {base}.explicitTop)
          {permutation_name} = {top_name} := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_{suffix} :
    BottomDetBound
      (topOfPattern (R := ℤ) ({pattern_expression(pattern)})) {BOUND} := by
  have htop : {top_name} =
      topOfPattern (R := ℤ) ({pattern_expression(pattern)}) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_{suffix}
"""


def render_singular_target(
    index: int,
    pattern: Pattern,
    data: SingularTarget,
) -> str:
    suffix = f"{index:04d}"
    top_name = f"targetTop_{suffix}"
    relation_name = f"relationCoefficients_{suffix}"
    return f"""/-- Explicit rank-deficient target for canonical pattern `{pattern}`. -/
def {top_name} : Matrix (Fin 3) (Fin 6) ℤ :=
  {lean_matrix(top_rows(pattern))}

/-- A checked nonzero integral relation among the three fixed top rows. -/
def {relation_name} : Fin 3 → ℤ :=
  {lean_vector(data.relation)}

theorem topRelation_{suffix} :
    TopRowRelation {top_name} {relation_name} := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [{top_name}, {relation_name}, Fin.sum_univ_succ]
  · refine ⟨{data.witness}, ?_⟩
    change ({lean_int(data.relation[data.witness])} : ℤ) ≠ 0
    norm_num

theorem literalBound_{suffix} : BottomDetBound {top_name} {BOUND} :=
  BottomDetBound.ofTopRowRelation (B := {BOUND}) topRelation_{suffix}

theorem canonicalBound_{suffix} :
    BottomDetBound
      (topOfPattern (R := ℤ) ({pattern_expression(pattern)})) {BOUND} := by
  have htop : {top_name} =
      topOfPattern (R := ℤ) ({pattern_expression(pattern)}) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_{suffix}
"""


def emit_targets(
    output_root: Path,
    patterns: list[Pattern],
    target_data: dict[Pattern, TargetData],
    targets_per_module: int,
) -> dict[Pattern, str]:
    owner: dict[Pattern, str] = {}
    for start in range(0, len(patterns), targets_per_module):
        shard = start // targets_per_module
        module = target_module(shard)
        batch = patterns[start : start + targets_per_module]
        representative_imports = sorted(
            {
                representative_aggregate_module(data.representative)
                for pattern in batch
                for data in [target_data[pattern]]
                if isinstance(data, FullRankTarget)
            }
        )
        declarations: list[str] = []
        for pattern in batch:
            index = patterns.index(pattern)
            data = target_data[pattern]
            if isinstance(data, FullRankTarget):
                declarations.append(render_full_rank_target(index, pattern, data))
            else:
                declarations.append(render_singular_target(index, pattern, data))
            owner[pattern] = module
        text = f"""-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
{chr(10).join(f'import {imported}' for imported in representative_imports)}

namespace {module}

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

{chr(10).join(declarations)}
end {module}
"""
        write_if_changed(module_path(output_root, module), text)
    if set(owner) != set(patterns):
        raise RuntimeError("target theorem ownership is incomplete")
    return owner


def adjacent_hypotheses(prefix: tuple[int, ...]) -> list[tuple[str, str]]:
    depth = len(prefix)
    result: list[tuple[str, str]] = []
    if 0 < depth < 6:
        result.append((f"h{depth - 1}{depth}", f"{prefix[-1]} <= a{depth}.val"))
    start = depth + 1 if depth > 0 else 1
    for index in range(start, 6):
        result.append(
            (
                f"h{index - 1}{index}",
                f"a{index - 1}.val <= a{index}.val",
            )
        )
    return result


def node_pattern_expression(prefix: tuple[int, ...]) -> str:
    terms = [str(value) for value in prefix]
    terms.extend(f"a{index}.val" for index in range(len(prefix), 6))
    return "angle6 " + " ".join(terms)


def child_call(
    child: tuple[int, ...],
    target_owner: dict[Pattern, str],
    target_index: dict[Pattern, int],
    cover_owner: dict[tuple[int, ...], str],
) -> str:
    if len(child) == 6:
        pattern: Pattern = child  # type: ignore[assignment]
        return (
            f"{target_owner[pattern]}.canonicalBound_"
            f"{target_index[pattern]:04d}"
        )
    variables = [f"a{index}" for index in range(len(child), 6)]
    hypotheses = [name for name, _ in adjacent_hypotheses(child)]
    arguments = " ".join(variables + hypotheses)
    return (
        f"{cover_owner[child]}.{cover_theorem_name(child)} {arguments}"
    ).rstrip()


def first_tactic(alternatives: list[str]) -> str:
    return "\n".join(
        ["    first", *(f"    | {alternative}" for alternative in alternatives)]
    )


def cover_children(prefix: tuple[int, ...]) -> list[tuple[int, ...]]:
    lower = prefix[-1] if prefix else 0
    return [prefix + (value,) for value in range(lower, TOP_ALPHABET)]


def render_cover_theorem(
    prefix: tuple[int, ...],
    target_owner: dict[Pattern, str],
    target_index: dict[Pattern, int],
    cover_owner: dict[tuple[int, ...], str],
) -> str:
    depth = len(prefix)
    if depth >= 6:
        raise ValueError("terminal patterns are target theorems, not cover nodes")
    children = cover_children(prefix)
    variables = " ".join(f"a{index}" for index in range(depth, 6))
    hypotheses = adjacent_hypotheses(prefix)
    hypothesis_text = "\n".join(
        f"    ({name} : {proposition})" for name, proposition in hypotheses
    )
    if hypothesis_text:
        hypothesis_text = "\n" + hypothesis_text
    # One bullet per `fin_cases` branch, dispatched directly.
    #
    # The earlier form was `fin_cases a{depth} <;> first | omega | exact ...`,
    # which made branch `v` try every child from `lower` up to `v` before
    # finding its own.  Each failed `exact` has to unfold the whole determinant
    # circuit before it can be rejected, and at depth five -- where five of the
    # six pattern indices are fixed and the circuits are largest -- that drove a
    # single `lean.exe` to a 93 GB working set and exhausted a 128 GB machine.
    # Raising `maxHeartbeats` only lets the same blow-up run longer.
    #
    # The prefix already determines which child belongs to which branch, so
    # nothing has to be searched: branches below `lower` contradict the adjacency
    # hypothesis and close by `omega`, and every other branch names its child.
    lower = prefix[-1] if prefix else 0
    branch_lines: list[str] = []
    for value in range(TOP_ALPHABET):
        if value < lower:
            # `fin_cases` leaves the branch index under a double coercion,
            # `4 <= up-up((fun i => i) <0, _>)`, which `omega` treats as an
            # opaque atom and cannot refute.  The old `first | omega | exact ..`
            # form hid this: omega failed there too and one of the `exact`
            # alternatives closed the branch instead.  `simp` reduces the
            # coercion and discharges the contradictory adjacency hypothesis.
            branch_lines.append(f"  · simp at h{depth - 1}{depth}")
        else:
            child = prefix + (value,)
            call = child_call(child, target_owner, target_index, cover_owner)
            branch_lines.append(f"  · exact {call}")
    branches = chr(10).join(branch_lines)
    return f"""theorem {cover_theorem_name(prefix)} ({variables} : Fin 8){hypothesis_text} :
    BottomDetBound
      (topOfPattern (R := ℤ) ({node_pattern_expression(prefix)})) {BOUND} := by
  fin_cases a{depth}
{branches}
"""


def emit_cover_modules(
    output_root: Path,
    patterns: list[Pattern],
    target_owner: dict[Pattern, str],
    theorems_per_module: int,
) -> tuple[str, str]:
    target_index = {pattern: index for index, pattern in enumerate(patterns)}
    prefixes = all_cover_prefixes(patterns)
    cover_owner, modules = cover_plan(patterns, theorems_per_module)
    prefixes_by_module: dict[str, list[tuple[int, ...]]] = {
        module: [] for module in modules
    }
    for prefix in prefixes:
        prefixes_by_module[cover_owner[prefix]].append(prefix)
    for module in modules:
        batch = sorted(prefixes_by_module[module])
        imports: set[str] = set()
        for prefix in batch:
            for child in cover_children(prefix):
                if len(child) == 6:
                    pattern: Pattern = child  # type: ignore[assignment]
                    imports.add(target_owner[pattern])
                else:
                    imports.add(cover_owner[child])
        declarations = "\n".join(
            render_cover_theorem(
                prefix, target_owner, target_index, cover_owner
            )
            for prefix in batch
        )
        text = f"""-- Generated proof-only `Fin 8` coverage shard.
-- At most {theorems_per_module} independent theorems; heartbeat limits reset per command.
{chr(10).join(f'import {imported}' for imported in sorted(imports))}

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace {module}

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

{declarations}
end {module}
"""
        write_if_changed(module_path(output_root, module), text)
    root: tuple[int, ...] = ()
    return cover_owner[root], f"{cover_owner[root]}.{cover_theorem_name(root)}"


def emit_certificate(
    output_root: Path,
    root_cover_module: str,
    root_cover_theorem: str,
) -> str:
    module = certificate_module()
    lets = "\n".join(
        f"  let a{index} : Fin 8 := ⟨p {index}, hrange {index}⟩"
        for index in range(6)
    )
    monotone = "\n".join(
        f"""  have h{index - 1}{index} : a{index - 1}.val <= a{index}.val := by
    simpa [a{index - 1}, a{index}] using
      hmono (show ({index - 1} : Fin 6) <= {index} by decide)"""
        for index in range(1, 6)
    )
    arguments = " ".join(f"a{index}" for index in range(6))
    hypotheses = " ".join(f"h{index - 1}{index}" for index in range(1, 6))
    angle = "angle6 " + " ".join(f"a{index}.val" for index in range(6))
    text = f"""-- Generated semantic endpoint for the fully kernel-checked beta-six bound.
import {root_cover_module}
import MainTheory.BinaryBetaSixCanonical
import MainTheory.BinaryBetaSixLower

namespace {module}

open MainTheory.BinaryBeta
open MainTheory.BinaryBetaSixCanonical
open MainTheory.OuterCompleteness
open MainTheory.OuterEnumeration

/-- Every in-range weakly increasing six-tuple is dispatched by Lean's
six-level `Fin 8` coverage tree. -/
theorem allCanonical : AllCanonicalBottomBound {BOUND} := by
  intro p hp
  rcases hp with ⟨hrange, hmono⟩
{lets}
{monotone}
  have hbound := {root_cover_theorem} {arguments} {hypotheses}
  have hvec : p = {angle} := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
  exact hbound

theorem upper : BetaBound 6 {BOUND} :=
  betaSixBound_of_allCanonicalBottomBound allCanonical

theorem betaExact : BetaExact 6 {BOUND} :=
  ⟨upper, MainTheory.BinaryBetaSixLower.betaSixAttained⟩

end {module}
"""
    write_if_changed(module_path(output_root, module), text)
    return module


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-root",
        type=Path,
        default=Path("MainTheory/Generated"),
        help="filesystem root corresponding to MainTheory.Generated",
    )
    parser.add_argument(
        "--fresh-staging-root",
        type=Path,
        help=(
            "new empty workspace-local root corresponding to MainTheory.Generated; "
            "overrides --output-root and is forbidden from overlapping the live root"
        ),
    )
    parser.add_argument(
        "--chunks-per-module",
        type=int,
        default=DEFAULT_CHUNKS_PER_MODULE,
        help="independent 16-pair chunk theorems per arithmetic module (1..16)",
    )
    parser.add_argument(
        "--targets-per-module",
        type=int,
        default=DEFAULT_TARGETS_PER_MODULE,
        help="independent transport/relation theorems per target module (1..16)",
    )
    parser.add_argument(
        "--cover-theorems-per-module",
        type=int,
        default=DEFAULT_COVER_THEOREMS_PER_MODULE,
        help="independent proof-only coverage theorems per module (1..32)",
    )
    parser.add_argument(
        "--confirm-full-generation",
        action="store_true",
        help="required acknowledgement that roughly 1100 source files are emitted",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if not args.confirm_full_generation:
        raise SystemExit(
            "refusing bulk output without --confirm-full-generation; "
            "the script never invokes Lean or Lake"
        )
    if not 1 <= args.chunks_per_module <= 16:
        raise SystemExit("--chunks-per-module must lie in 1..16")
    if not 1 <= args.targets_per_module <= 16:
        raise SystemExit("--targets-per-module must lie in 1..16")
    if not 1 <= args.cover_theorems_per_module <= 32:
        raise SystemExit("--cover-theorems-per-module must lie in 1..32")
    if args.fresh_staging_root is not None:
        workspace = Path.cwd().resolve()
        staging = args.fresh_staging_root.resolve()
        live = Path("MainTheory/Generated").resolve()
        if not staging.is_relative_to(workspace):
            raise SystemExit("--fresh-staging-root must stay inside the workspace")
        if staging == live or staging in live.parents or live in staging.parents:
            raise SystemExit(
                "--fresh-staging-root must not equal, contain, or lie inside "
                "the live MainTheory/Generated root"
            )
        if staging.exists() and (
            not staging.is_dir() or any(staging.iterdir())
        ):
            raise SystemExit("--fresh-staging-root must be an absent or empty directory")
        args.output_root = staging

    patterns, representatives, target_data = classify_patterns()
    module_order = expected_module_order(
        patterns,
        representatives,
        args.chunks_per_module,
        args.targets_per_module,
        args.cover_theorems_per_module,
    )
    manifest, build_order = prepare_output(args.output_root, module_order)
    aggregates = emit_all_representatives(
        args.output_root, representatives, args.chunks_per_module
    )
    if len(aggregates) != 79:
        raise RuntimeError("representative aggregation is incomplete")
    target_owners = emit_targets(
        args.output_root, patterns, target_data, args.targets_per_module
    )
    root_cover_module, root_cover_theorem = emit_cover_modules(
        args.output_root,
        patterns,
        target_owners,
        args.cover_theorems_per_module,
    )
    final_module = emit_certificate(
        args.output_root, root_cover_module, root_cover_theorem
    )
    finish_output(
        args.output_root,
        module_order,
        manifest,
        build_order,
    )

    arithmetic_modules_per_rep = (
        len(all_chunks()) + args.chunks_per_module - 1
    ) // args.chunks_per_module
    arithmetic_modules = len(representatives) * arithmetic_modules_per_rep
    target_modules = (
        len(patterns) + args.targets_per_module - 1
    ) // args.targets_per_module
    _, cover_modules = cover_plan(patterns, args.cover_theorems_per_module)
    total_files = len(module_order)
    print(
        f"emitted {final_module}: 79 representatives, "
        f"{arithmetic_modules} arithmetic modules, {target_modules} target modules, "
        f"{len(cover_modules)} coverage modules, "
        f"{total_files} files total; manifest={manifest}; build_order={build_order}"
    )


if __name__ == "__main__":
    main()
