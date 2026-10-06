#!/usr/bin/env python3
"""Emit the fully kernel-checked fast certificate for ``BetaExact 5 5``.

This generator is deliberately outside the trusted argument.  Its output
proves all coverage inside Lean:

* one arithmetic theorem checks ``FastLastCodeSlice a b c 5`` with ordinary
  kernel ``decide``; a slice contains exactly the final codes ``c,...,31``
  and therefore at most 32 cheap integer-prefix calculations;
* proof-only modules enumerate ``c``, then ``b``, then ``a`` as ``Fin 32``;
* the endpoint derives the adjacent inequalities from ``Monotone`` and uses
  ``FastPrefixBound.toReducedAtRowBits`` to return to the semantic determinant;
* ``betaBound_of_monotonePrefixCertificate`` then proves ``BetaBound 5 5``.

There is no ``native_decide``, ``sorry``, axiom, heartbeat override, or
externally trusted list of covered tuples.  The Python loops only choose how
to shard declarations.  The generated Lean proof tree itself rules out an
omitted canonical row-code triple.

The default places eight *separate* slice theorems in one arithmetic module.
Each individual decision problem retains the already probed 32-item cap.
Use ``--slices-per-module 1`` for the most conservative build, or a value up
to eight after representative first/middle/last shard builds.  The 528 pair
coverage theorems and 32 first-code theorems are likewise grouped at most
eight independent commands per proof-only module; no arithmetic is repeated
there.  This script only writes source and never invokes Lean or Lake.
Full generation requires ``--confirm-full-generation``.  A successful run
writes an exact SHA-256 source manifest and a topological serial-build list;
at the start of a replacement run it invalidates the old final certificate
and rejects unexpected Lean shards instead of silently mixing generations.
``--fresh-staging-root`` additionally requires an empty workspace-local root
which cannot overlap the live ``MainTheory/Generated`` directory.
"""

from __future__ import annotations

import argparse
import hashlib
from itertools import combinations_with_replacement
from pathlib import Path


MODULE_PREFIX = "MainTheory.Generated."
BASE_MODULE = "MainTheory.Generated.BinaryBetaFiveFast"
DEFAULT_SLICES_PER_MODULE = 8
DEFAULT_PAIR_THEOREMS_PER_MODULE = 8
DEFAULT_FIRST_THEOREMS_PER_MODULE = 8
WIDTH = 32
BOUND = 5


Triple = tuple[int, int, int]


def write_if_changed(path: Path, text: str) -> None:
    """Write UTF-8 Lean source without touching an unchanged file."""
    if path.exists() and path.read_text(encoding="utf-8") == text:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def module_path(output_root: Path, module: str) -> Path:
    if not module.startswith(MODULE_PREFIX):
        raise ValueError(f"unexpected module outside {MODULE_PREFIX}: {module}")
    relative = module[len(MODULE_PREFIX) :].replace(".", "/") + ".lean"
    return output_root / relative


def arithmetic_module(shard: int) -> str:
    return f"{BASE_MODULE}.Arithmetic.Shard{shard:04d}"


def pair_module(shard: int) -> str:
    return f"{BASE_MODULE}.Cover.Pair.Shard{shard:03d}"


def first_module(shard: int) -> str:
    return f"{BASE_MODULE}.Cover.First.Shard{shard:03d}"


def pair_theorem_name(a: int, b: int) -> str:
    return f"cover_pair_{a:02d}_{b:02d}"


def first_theorem_name(a: int) -> str:
    return f"cover_first_{a:02d}"


def certificate_module() -> str:
    return f"{BASE_MODULE}.Certificate"


def canonical_pairs() -> list[tuple[int, int]]:
    pairs = [(a, b) for a in range(WIDTH) for b in range(a, WIDTH)]
    if len(pairs) != 528:
        raise RuntimeError(f"expected 528 canonical pairs, got {len(pairs)}")
    return pairs


def expected_module_order(
    triples: list[Triple],
    slices_per_module: int,
    pair_theorems_per_module: int,
    first_theorems_per_module: int,
) -> list[str]:
    """Exact topological order for the resource-safe serial builder."""
    arithmetic_count = (
        len(triples) + slices_per_module - 1
    ) // slices_per_module
    modules = [arithmetic_module(shard) for shard in range(arithmetic_count)]
    pair_count = (
        len(canonical_pairs()) + pair_theorems_per_module - 1
    ) // pair_theorems_per_module
    first_count = (
        WIDTH + first_theorems_per_module - 1
    ) // first_theorems_per_module
    modules.extend(pair_module(shard) for shard in range(pair_count))
    modules.extend(first_module(shard) for shard in range(first_count))
    modules.append(certificate_module())
    if len(modules) != len(set(modules)):
        raise RuntimeError("generated module plan contains duplicate names")
    return modules


def kernel_output_directory(output_root: Path) -> Path:
    return output_root / "BinaryBetaFiveFast"


def prepare_output(
    output_root: Path,
    module_order: list[str],
) -> tuple[Path, Path]:
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
    actual = set(kernel_output_directory(output_root).rglob("*.lean"))
    missing = sorted(expected - actual)
    unexpected = sorted(actual - expected)
    if missing or unexpected:
        raise RuntimeError(
            f"generated file-set mismatch: {len(missing)} missing, "
            f"{len(unexpected)} unexpected; no success manifest was written"
        )
    lines = [
        "# gen_binary_beta_five_fast.py exact generated-source manifest",
        f"# lean_files={len(module_order)}",
        "# sha256  module",
    ]
    for module in module_order:
        source = module_path(output_root, module)
        lines.append(f"{hashlib.sha256(source.read_bytes()).hexdigest()}  {module}")
    atomic_write(build_order, "\n".join(module_order) + "\n")
    atomic_write(manifest, "\n".join(lines) + "\n")


def slice_name(a: int, b: int, c: int) -> str:
    return f"slice_{a:02d}_{b:02d}_{c:02d}"


def all_triples() -> list[Triple]:
    triples = list(combinations_with_replacement(range(WIDTH), 3))
    # choose(32 + 3 - 1, 3) = choose(34, 3) = 5984.
    if len(triples) != 5984:
        raise RuntimeError(f"expected 5984 canonical triples, got {len(triples)}")
    prefix_count = sum(WIDTH - c for _, _, c in triples)
    # Each triple owns d=c,...,31.  The disjoint union is precisely the
    # choose(32 + 4 - 1, 4) = choose(35, 4) monotone four-tuples.
    if prefix_count != 52360:
        raise RuntimeError(
            f"expected 52360 monotone prefixes, got {prefix_count}"
        )
    return triples


def render_arithmetic_theorem(triple: Triple) -> str:
    a, b, c = triple
    return f"""/-- Kernel arithmetic for final codes `{c},...,31`. -/
theorem {slice_name(a, b, c)} : FastLastCodeSlice {a} {b} {c} {BOUND} := by
  decide
"""


def emit_arithmetic(
    output_root: Path,
    triples: list[Triple],
    slices_per_module: int,
) -> dict[Triple, str]:
    owner: dict[Triple, str] = {}
    for start in range(0, len(triples), slices_per_module):
        shard = start // slices_per_module
        module = arithmetic_module(shard)
        batch = triples[start : start + slices_per_module]
        body = "\n".join(render_arithmetic_theorem(t) for t in batch)
        text = f"""-- Generated by gen_binary_beta_five_fast.py.
-- Each `decide` below checks one independent slice of at most 32 prefixes.
import MainTheory.BinaryDetFiveFast

namespace {module}

open MainTheory.BinaryDetFiveFast

{body}
end {module}
"""
        write_if_changed(module_path(output_root, module), text)
        for triple in batch:
            if triple in owner:
                raise RuntimeError(f"duplicate arithmetic owner for {triple}")
            owner[triple] = module
    if set(owner) != set(triples):
        raise RuntimeError("arithmetic ownership does not cover every triple")
    return owner


def render_fin_value_cases(
    variable: str,
    values_and_proofs: list[tuple[int, str]],
) -> str:
    """Render low-resource `interval_cases` branches for a `Fin 32` value.

    Each branch first reconstructs the `Fin` value extensionally.  This keeps
    the arithmetic certificate theorem syntactically fixed and avoids the
    expensive 32-way term expansion caused by `fin_cases`.
    """
    branches: list[str] = []
    for value, proof in values_and_proofs:
        branches.append(
            f"""  · have hcode{value:02d} : {variable} = ⟨{value}, by decide⟩ := by
      apply Fin.ext
      simp [hvalue]
    subst {variable}
    {proof}"""
        )
    return "\n".join(branches)


def render_pair_cover(
    a: int,
    b: int,
    owner: dict[Triple, str],
) -> str:
    cases = [
        (c, f"exact {owner[(a, b, c)]}.{slice_name(a, b, c)}")
        for c in range(b, WIDTH)
    ]
    return f"""/-- Every canonical third code for the fixed pair `{a},{b}` has a checked
final-code slice.  The bounded value enumeration is checked by Lean itself. -/
theorem {pair_theorem_name(a, b)} (c : Fin 32) (hbc : {b} <= c.val) :
    FastLastCodeSlice {a} {b} c.val {BOUND} := by
  have hlt : c.val < 32 := c.isLt
  interval_cases hvalue : c.val
{render_fin_value_cases("c", cases)}
"""


def emit_all_pair_covers(
    output_root: Path,
    owner: dict[Triple, str],
    theorems_per_module: int,
) -> dict[tuple[int, int], str]:
    modules: dict[tuple[int, int], str] = {}
    pairs = canonical_pairs()
    for start in range(0, len(pairs), theorems_per_module):
        shard = start // theorems_per_module
        module = pair_module(shard)
        batch = pairs[start : start + theorems_per_module]
        imports = sorted(
            {
                owner[(a, b, c)]
                for a, b in batch
                for c in range(b, WIDTH)
            }
        )
        declarations = "\n".join(
            render_pair_cover(a, b, owner) for a, b in batch
        )
        text = f"""-- Generated proof-only pair-coverage shard.
-- At most {theorems_per_module} independent theorems; heartbeat limits reset per command.
{chr(10).join(f'import {imported}' for imported in imports)}

namespace {module}

open MainTheory.BinaryDetFiveFast

{declarations}
end {module}
"""
        write_if_changed(module_path(output_root, module), text)
        for pair in batch:
            if pair in modules:
                raise RuntimeError(f"duplicate pair-cover owner for {pair}")
            modules[pair] = module
    if set(modules) != set(pairs):
        raise RuntimeError("pair-cover ownership is incomplete")
    return modules


def render_first_cover(
    a: int,
    pairs: dict[tuple[int, int], str],
) -> str:
    cases = [
        (b, f"exact {pairs[(a, b)]}.{pair_theorem_name(a, b)} c hbc")
        for b in range(a, WIDTH)
    ]
    return f"""/-- Every canonical second and third code above `{a}` is covered. -/
theorem {first_theorem_name(a)} (b c : Fin 32)
    (hab : {a} <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice {a} b.val c.val {BOUND} := by
  have hlt : b.val < 32 := b.isLt
  interval_cases hvalue : b.val
{render_fin_value_cases("b", cases)}
"""


def emit_all_first_covers(
    output_root: Path,
    pairs: dict[tuple[int, int], str],
    theorems_per_module: int,
) -> dict[int, str]:
    owners: dict[int, str] = {}
    values = list(range(WIDTH))
    for start in range(0, len(values), theorems_per_module):
        shard = start // theorems_per_module
        module = first_module(shard)
        batch = values[start : start + theorems_per_module]
        imports = sorted(
            {
                pairs[(a, b)]
                for a in batch
                for b in range(a, WIDTH)
            }
        )
        declarations = "\n".join(
            render_first_cover(a, pairs) for a in batch
        )
        text = f"""-- Generated proof-only first-code coverage shard.
-- At most {theorems_per_module} independent theorems; heartbeat limits reset per command.
{chr(10).join(f'import {imported}' for imported in imports)}

namespace {module}

open MainTheory.BinaryDetFiveFast

{declarations}
end {module}
"""
        write_if_changed(module_path(output_root, module), text)
        for a in batch:
            owners[a] = module
    if set(owners) != set(values):
        raise RuntimeError("first-code coverage ownership is incomplete")
    return owners


def emit_certificate(output_root: Path, firsts: dict[int, str]) -> str:
    module = certificate_module()
    imports = sorted(set(firsts.values()))
    root_cases = [
        (a, f"exact {firsts[a]}.{first_theorem_name(a)} b c hab hbc")
        for a in range(WIDTH)
    ]
    text = f"""-- Generated semantic endpoint for the fully kernel-checked beta-five bound.
{chr(10).join(f'import {m}' for m in imports)}
import MainTheory.BinaryBetaSmallLower

namespace {module}

open MainTheory.BinaryBeta
open MainTheory.BinaryDetFiveFast
open MainTheory.BinaryBetaSmallSemantic

/-- Every weakly increasing triple of five-bit row codes owns its complete
final-code arithmetic slice.  Coverage is by three nested `Fin 32`
enumerations in Lean, not by trusting the generator's list length. -/
theorem allCanonical (a b c : Fin 32)
    (hab : a.val <= b.val) (hbc : b.val <= c.val) :
    FastLastCodeSlice a.val b.val c.val {BOUND} := by
  have hlt : a.val < 32 := a.isLt
  interval_cases hvalue : a.val
{render_fin_value_cases("a", root_cases)}

/-- The complete fast table proves the exact sorted-prefix interface. -/
theorem monotonePrefix : MonotonePrefixCertificate 4 {BOUND} := by
  intro f hf
  have h01 : (f 0).toNat <= (f 1).toNat :=
    hf (show (0 : Fin 4) <= 1 by decide)
  have h12 : (f 1).toNat <= (f 2).toNat :=
    hf (show (1 : Fin 4) <= 2 by decide)
  have h23 : (f 2).toNat <= (f 3).toNat :=
    hf (show (2 : Fin 4) <= 3 by decide)
  have h0lt : (f 0).toNat < 32 := by simpa using (f 0).isLt
  have h1lt : (f 1).toNat < 32 := by simpa using (f 1).isLt
  have h2lt : (f 2).toNat < 32 := by simpa using (f 2).isLt
  have h3lt : (f 3).toNat < 32 := by simpa using (f 3).isLt
  let a : Fin 32 := ⟨(f 0).toNat, h0lt⟩
  let b : Fin 32 := ⟨(f 1).toNat, h1lt⟩
  let c : Fin 32 := ⟨(f 2).toNat, h2lt⟩
  have hs : FastLastCodeSlice a.val b.val c.val {BOUND} :=
    allCanonical a b c (by simpa [a, b] using h01)
      (by simpa [b, c] using h12)
  have hp : FastPrefixBound
      ![a.val, b.val, c.val, (f 3).toNat] {BOUND} :=
    hs.lookup (by simpa [c] using h23) h3lt
  apply FastPrefixBound.toReducedAtRowBits
  have hcodes : (fun i => (f i).toNat) =
      ![(f 0).toNat, (f 1).toNat, (f 2).toNat, (f 3).toNat] := by
    funext i
    fin_cases i <;> rfl
  rw [hcodes]
  simpa [a, b, c] using hp

theorem upper : BetaBound 5 {BOUND} := by
  simpa using betaBound_of_monotonePrefixCertificate monotonePrefix

theorem betaExact : BetaExact 5 {BOUND} :=
  ⟨upper, MainTheory.BinaryBetaSmallLower.Five.betaFiveAttained⟩

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
        help="filesystem root corresponding to the MainTheory.Generated namespace",
    )
    parser.add_argument(
        "--fresh-staging-root",
        type=Path,
        help=(
            "new empty workspace-local root corresponding to MainTheory.Generated; "
            "overrides --output-root and cannot overlap the live root"
        ),
    )
    parser.add_argument(
        "--slices-per-module",
        type=int,
        default=DEFAULT_SLICES_PER_MODULE,
        help="independent slice theorems per arithmetic module (1..8)",
    )
    parser.add_argument(
        "--pair-theorems-per-module",
        type=int,
        default=DEFAULT_PAIR_THEOREMS_PER_MODULE,
        help="independent proof-only pair theorems per module (1..8)",
    )
    parser.add_argument(
        "--first-theorems-per-module",
        type=int,
        default=DEFAULT_FIRST_THEOREMS_PER_MODULE,
        help="independent proof-only first-code theorems per module (1..8)",
    )
    parser.add_argument(
        "--confirm-full-generation",
        action="store_true",
        help="required acknowledgement that roughly 820 source files are emitted",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if not args.confirm_full_generation:
        raise SystemExit(
            "refusing bulk output without --confirm-full-generation; "
            "the script never invokes Lean or Lake"
        )
    if not 1 <= args.slices_per_module <= 8:
        raise SystemExit("--slices-per-module must lie in 1..8")
    if not 1 <= args.pair_theorems_per_module <= 8:
        raise SystemExit("--pair-theorems-per-module must lie in 1..8")
    if not 1 <= args.first_theorems_per_module <= 8:
        raise SystemExit("--first-theorems-per-module must lie in 1..8")
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
    triples = all_triples()
    module_order = expected_module_order(
        triples,
        args.slices_per_module,
        args.pair_theorems_per_module,
        args.first_theorems_per_module,
    )
    manifest, build_order = prepare_output(args.output_root, module_order)
    owner = emit_arithmetic(
        args.output_root, triples, args.slices_per_module
    )
    pairs = emit_all_pair_covers(
        args.output_root, owner, args.pair_theorems_per_module
    )
    firsts = emit_all_first_covers(
        args.output_root, pairs, args.first_theorems_per_module
    )
    final_module = emit_certificate(args.output_root, firsts)
    finish_output(
        args.output_root,
        module_order,
        manifest,
        build_order,
    )
    arithmetic_count = (
        len(triples) + args.slices_per_module - 1
    ) // args.slices_per_module
    pair_module_count = (
        len(canonical_pairs()) + args.pair_theorems_per_module - 1
    ) // args.pair_theorems_per_module
    first_module_count = (
        WIDTH + args.first_theorems_per_module - 1
    ) // args.first_theorems_per_module
    total_files = len(module_order)
    print(
        f"emitted {final_module}: {len(triples)} slices, "
        f"{arithmetic_count} arithmetic modules, {pair_module_count} pair modules, "
        f"{first_module_count} first-code modules, {total_files} files total; "
        f"manifest={manifest}; build_order={build_order}"
    )


if __name__ == "__main__":
    main()
