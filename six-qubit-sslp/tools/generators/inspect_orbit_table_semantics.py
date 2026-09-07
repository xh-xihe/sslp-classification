"""Prepare all three numeric columns of the 66-orbit table for Lean certificates.

This is an exact, independent data audit, not itself a Lean proof.  It reads the
complete current manuscript rows and the existing certificate bundle, preserving
r_star, LP dimension and record multiplicity.  No numerical LP solver is used.
"""
from collections import Counter
import json
from pathlib import Path
import sys

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "verification"))
from mkmanifest import ROW, parse_table


def feature(k):
    bits = [(k >> j) & 1 for j in range(6)]
    return bits + [bits[i] * bits[j] for i in range(6) for j in range(i + 1, 6)]


def mask(a, q, residue):
    return sum(1 << k for k in range(64)
               if sum(a[j] for j in range(6) if (k >> j) & 1) % q == residue)


def inspect():
    manuscript = (ROOT / "documents/20260905/supplementary.tex").read_text(encoding="utf-8")
    parsed = parse_table(manuscript)
    pipeline = json.loads((ROOT / "results/main-pipeline-certificates.json").read_text())
    orbit = json.loads((ROOT / "results/finite-orbit-certificates.json").read_text())
    pair_ids = {tuple(p): i for i, p in enumerate(pipeline["pair_table"])}
    ranks = {r["pair"]: (i, r) for i, r in enumerate(pipeline["rank_certificates"])}
    pair_orbit = {w["pair_id"]: w["orbit_id"] for w in orbit["cube_witnesses"]}
    multiplicities = Counter(pair_orbit[p] for p in pipeline["record_pair_ids"] if p in pair_orbit)
    rows = []
    for line in manuscript.splitlines():
        m = ROW.fullmatch(line)
        if not m:
            continue
        values = m.groups()
        oid = int(values[0])
        row = dict(parsed[oid][0])
        row.update(id=oid, r_star=int(values[6]), lp_dimension=int(values[7]),
                   multiplicity=int(values[8]), status=values[9])
        key = (row["q"], row["m"], mask(row["a"], row["q"], 0),
               mask(row["a"], row["q"], row["d"]))
        pid = pair_ids[key]
        rank_index, cert = ranks[pid]
        active = [(b, k) for b in range(2) for k in range(64)
                  if (cert["active" + str(b)] >> k) & 1]
        matrix = sp.Matrix([[int(b == 0) for b, k in active],
                            [int(b == 1) for b, k in active]] +
                           [[(-1 if b else 1) * feature(k)[j] for b, k in active]
                            for j in range(21)])
        matrix_rank = matrix.rank()
        actual_rank = min(cert["rank0"]["rank"], cert["rank1"]["rank"])
        actual_dimension = len(active) - matrix_rank
        actual_multiplicity = multiplicities[pair_orbit[pid]]
        assert actual_rank == row["r_star"], (oid, "r_star", actual_rank, row)
        assert actual_dimension == row["lp_dimension"], (oid, "dimension", actual_dimension, row)
        assert actual_multiplicity == row["multiplicity"], (oid, "multiplicity", actual_multiplicity, row)
        row.update(pair_id=pid, rank_row_index=rank_index,
                   certified_orbit_index=pair_orbit[pid], active_columns=active,
                   restricted_moment_rank=matrix_rank)
        rows.append(row)
    assert len(rows) == 66
    assert sum(r["multiplicity"] for r in rows) == 216
    return rows


if __name__ == "__main__":
    rows = inspect()
    destination = ROOT / "tmp/orbit_table_semantic_inputs.json"
    destination.write_text(json.dumps(rows, indent=2) + "\n")
    print("PASS: all 66 r_star, actual active moment-matrix dimensions, and record multiplicities agree.")
    print("Certificate-generation inputs:", destination)
