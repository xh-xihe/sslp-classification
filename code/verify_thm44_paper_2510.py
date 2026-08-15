"""Verify Theorem 4.4 (Two-anchor Bell-flag ladder theorem) of dyadic_lifts.tex
against the 10 explicit ((7, 2, 3)) BD16 distance-3 codes from
arXiv:2510.20728 Appendix F (He, Lu, Zeng 2026).

These 10 codes use the SAME weight vectors as bd16_01..10 from
arXiv:2504.20847, but with DIFFERENT amplitude representatives drawn from
the 2-parameter / discrete-family / uniform-magnitude / phase-only closed
forms in 2510.20728 Appendix F. We expect all 10 to CONFIRM Theorem 4.4
(same arithmetic hypotheses; closed-form constructions are by definition
distance-3 KL-satisfying).

The 2 no-go cases from Appendix G (w = (1,1,1,2,2,2,6) and (0,1,1,2,3,3,5))
have no codeword, so the dyadic Bell lift is vacuous; we record their data
separately (not run through the verifier).

Outputs:
  outputs_thm44/thm44_verification_results_2510_20728.json
  outputs_thm44/thm44_verification_results_2510_20728.csv
  outputs_thm44/thm44_verification_results_2510_20728.md
"""
from __future__ import annotations

import csv
import json
import os
import time
from typing import Any, Dict, List

from paper_seeds_2510_20728 import (
    get_all_2510_seeds, CODE_META_2510, NO_GO_CASES,
)
import verify_thm44_paper as v44

# Monkey-patch CODE_META so evaluate_seed picks up the new entries.
v44.CODE_META.update(CODE_META_2510)


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-rungs", type=int, default=5)
    ap.add_argument("--tol", type=float, default=1e-8)
    ap.add_argument("--out-dir", type=str, default="outputs_thm44")
    args = ap.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)

    seeds = get_all_2510_seeds()
    print(f"[Theorem 4.4 verification on arXiv:2510.20728] "
          f"{len(seeds)} seeds (App F.a..F.j)")
    print(f"  max_rungs={args.max_rungs}, tol={args.tol}")
    print()

    t0 = time.time()
    results: List[Dict[str, Any]] = []
    for seed in seeds:
        t1 = time.time()
        r = v44.evaluate_seed(seed, max_rungs=args.max_rungs, tol=args.tol)
        t1 = time.time() - t1
        r["elapsed_sec"] = t1
        results.append(r)
        h = r["hypotheses"]
        st = r["thm44_status"]
        cmr = r.get("consecutive_max_rung", -1)
        print(
            f"  [{r['name']:>12s}]  {r['paper_section']:>22s}  "
            f"all_hyp={h['all_hypotheses_hold']!s:>5s}  "
            f"r_max={cmr:>2d}  worst={r.get('worst_violation_across_rungs', 0.0):.2e}  "
            f"{st}  ({t1:.1f}s)"
        )

    total = time.time() - t0
    print()
    print(f"Total elapsed: {total:.1f}s")
    print()

    # ---- Aggregate ----
    n_total = len(results)
    n_confirms = sum(1 for r in results if r["thm44_status"] == "CONFIRMS")
    n_counterex = sum(1 for r in results
                      if r["thm44_status"] == "COUNTEREXAMPLE")
    n_inappl = sum(1 for r in results
                   if r["thm44_status"].startswith("INAPPLICABLE"))

    summary = {
        "source": "arXiv:2510.20728 Appendix F (10 codes) + Appendix G (2 no-go)",
        "appendix_F_codes_tested": n_total,
        "appendix_G_no_go_cases": len(NO_GO_CASES),
        "max_rungs": args.max_rungs,
        "tol": args.tol,
        "CONFIRMS": n_confirms,
        "COUNTEREXAMPLE": n_counterex,
        "INAPPLICABLE": n_inappl,
    }
    print("=" * 64)
    print("Summary")
    print("=" * 64)
    for k, val in summary.items():
        print(f"  {k:>32s}: {val}")
    print()
    print("Note: the 2 Appendix-G cases are infeasible by published Lean")
    print("      proofs; they have no codeword, so Theorem 4.4 is vacuous.")
    print()

    # ---- Write JSON ----
    out_json = os.path.join(args.out_dir,
                            "thm44_verification_results_2510_20728.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"summary": summary,
                   "appendix_F_results": results,
                   "appendix_G_no_go_cases": NO_GO_CASES},
                  f, indent=2)
    print(f"[saved] {out_json}")

    # ---- Write CSV ----
    out_csv = os.path.join(args.out_dir,
                           "thm44_verification_results_2510_20728.csv")
    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "name", "paper_section", "transversal_group", "n", "m",
            "a_vector", "b_list", "sum_a", "2m-1", "max_a", "m-2",
            "bell_liftable", "strong_sum", "bounded_entries",
            "unique_bot_anchor_i", "unique_top_anchor_ii",
            "seed_d3", "rung1_d3", "all_hypotheses",
            "conclusion_all_rungs_d3", "consecutive_max_rung",
            "worst_violation_across_rungs", "thm44_status", "notes",
        ])
        for r in results:
            h = r["hypotheses"]
            rungs = r["rungs"]
            seed_d3 = rungs[0].get("passed", False) if rungs else False
            rung1_d3 = (len(rungs) >= 2 and rungs[1].get("passed", False))
            w.writerow([
                r["name"], r["paper_section"], r["transversal_group"],
                r["n"], r["m"],
                " ".join(str(x) for x in r["a"]),
                " ".join(str(x) for x in r["b_list"]),
                sum(r["a"]), 2 * r["m"] - 1,
                max(r["a"]), r["m"] - 2,
                r["bell_liftable"],
                h["strong_sum"], h["bounded_entries"],
                h["i_unique_bottom_anchor"], h["ii_unique_top_anchor"],
                seed_d3, rung1_d3, h["all_hypotheses_hold"],
                r["conclusion_all_rungs_distance3"],
                r.get("consecutive_max_rung", -1),
                f"{r.get('worst_violation_across_rungs', 0.0):.3e}",
                r["thm44_status"], r.get("notes", ""),
            ])
    print(f"[saved] {out_csv}")

    # ---- Write Markdown ----
    out_md = os.path.join(args.out_dir,
                          "thm44_verification_results_2510_20728.md")
    with open(out_md, "w", encoding="utf-8") as f:
        f.write("# Theorem 4.4 verification on arXiv:2510.20728\n\n")
        f.write("Source: He, Lu, Zeng 2026, *Co-Designing Quantum Codes "
                "with Transversal Diagonal Gates via Multi-Agent Systems*, "
                "Appendices F (10 feasible BD16 codes) and G (2 no-go cases).\n\n")
        f.write(f"Tested {n_total} Appendix-F codes; "
                f"recorded {len(NO_GO_CASES)} Appendix-G no-go cases.\n\n")
        f.write("## Aggregate verdict\n\n")
        f.write(f"| Status | Count |\n|---|---|\n")
        f.write(f"| CONFIRMS | {n_confirms} |\n")
        f.write(f"| COUNTEREXAMPLE | {n_counterex} |\n")
        f.write(f"| INAPPLICABLE | {n_inappl} |\n")
        f.write(f"| Appendix-G no-go (vacuous) | {len(NO_GO_CASES)} |\n\n")
        f.write("## Per-code results (Appendix F)\n\n")
        f.write("| Code | weight vector w | all hyp | r_max | worst viol | "
                "status |\n")
        f.write("|---|---|---|---|---|---|\n")
        for r in results:
            avec = "(" + ",".join(str(x) for x in r["a"]) + ")"
            f.write(f"| `{r['name']}` | {avec} | "
                    f"{r['hypotheses']['all_hypotheses_hold']} | "
                    f"{r.get('consecutive_max_rung', -1)} | "
                    f"{r.get('worst_violation_across_rungs', 0.0):.2e} | "
                    f"**{r['thm44_status']}** |\n")
        f.write("\n## Appendix-G no-go cases (vacuous; no codeword exists)\n\n")
        f.write("| Code | weight vector w | |C_0| | # eqs | Lean proof |\n")
        f.write("|---|---|---|---|---|\n")
        for ng in NO_GO_CASES:
            avec = "(" + ",".join(str(x) for x in ng["a"]) + ")"
            f.write(f"| `{ng['name']}` | {avec} | {len(ng['C0'])} | "
                    f"{ng['n_eqs']} | {ng['proof_section']} |\n")
    print(f"[saved] {out_md}")
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
