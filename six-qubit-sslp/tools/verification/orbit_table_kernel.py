"""Check current TeX values against the kernel-proved complete orbit table."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

from mkmanifest import DEFAULT_SOURCE, REPO, build_manifest

FIELDS = {
    "q": "paperQ", "m": "paperM", "n0": "paperN0", "n1": "paperN1",
    "r_star": "paperRank", "lp_dimension": "paperDimension",
    "multiplicity": "paperMultiplicity",
}


def vector(values):
    return "![" + ", ".join(map(str, values)) + "]"


def render_harness(manifest, *, data_only=False):
    rows = [manifest[str(i)] for i in range(1, 67)]
    module = "OrbitTableNumericData" if data_only else "OrbitTableNumeric"
    source = f"import MainTheory.Generated.{module}\n\n"
    source += "open MainTheory.Generated.OrbitTableNumericData\n"
    source += "set_option maxRecDepth 40000\nset_option maxHeartbeats 4000000\n\n"
    for field, name in FIELDS.items():
        source += f"example : {name} = {vector(row[field] for row in rows)} := by decide\n"
    source += f"example : paperAngle = {vector(vector(row['a']) for row in rows)} := by decide\n"
    if not data_only:
        source += "\n#check MainTheory.Generated.OrbitTableNumericData.all_rows\n"
        source += "#check MainTheory.Generated.OrbitTableNumericData.all_faces_valid\n"
        source += "#check MainTheory.Generated.OrbitTableNumeric.all_statistics\n"
        source += "#check MainTheory.Generated.OrbitTableNumeric.all_real_statistics\n"
        source += "#check MainTheory.Generated.OrbitTableActiveRanks.all_maximum_support_ranks\n"
        source += "#check MainTheory.Generated.OrbitTableNumeric.all_labeled_equivalences\n"
    return source


def check_harness(manifest, name, *, data_only=False, directory=None):
    directory = directory or REPO / "tmp/verification/orbit-table-kernel"
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / (name + ".lean")
    path.write_text(render_harness(manifest, data_only=data_only), encoding="utf-8")
    result = subprocess.run(
        ["lake", "env", "lean", "-j", "1", "-DwarningAsError=true", str(path)],
        cwd=REPO, capture_output=True, text=True, encoding="utf-8", errors="replace")
    output = result.stdout + result.stderr
    path.with_suffix(".log").write_text(output, encoding="utf-8")
    return result.returncode, output


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--manifest", type=Path, default=REPO / "tools/manifest.json")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args(argv)
    try:
        saved = json.loads(args.manifest.read_text(encoding="utf-8"))
        current = build_manifest(args.source_dir, saved)
        if current != saved:
            raise ValueError("current manuscript does not match the reviewed manifest")
        code, output = check_harness(current, "current", directory=args.output_dir)
        if code:
            raise ValueError("current kernel correspondence failed: " + output[-2500:])
        if args.selftest:
            for field in ("r_star", "lp_dimension", "multiplicity"):
                mutated = copy.deepcopy(current)
                mutated["1"][field] += 1
                code, output = check_harness(mutated, "mutated-" + field,
                                             data_only=True, directory=args.output_dir)
                if code == 0 or "is false" not in output:
                    raise ValueError("mutation was not rejected by kernel evaluation: " + field + "\n" + output[-1500:])
        print("PASS: current 66 rows match full-fibre kernel semantics" +
              ("; all three numeric-column mutations rejected" if args.selftest else ""))
        return 0
    except (OSError, UnicodeError, ValueError) as exc:
        print("FAIL: " + str(exc))
        return 1


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    raise SystemExit(main())
