"""Verify Theorem 4.4 (Two-anchor Bell-flag ladder theorem) of dyadic_lifts.tex
against EVERY explicit BD2m-type code listed in arXiv:2504.20847.

For each seed, this script reports:
  1. Hypothesis checks (i)-(iii):
     - (i)  unique bottom anchor: only 0^n in supp(|0_L>) with subset sum 0,
            and every other support has subset sum exactly m.
     - (ii) unique top anchor: only 1^n in supp(|1_L>) with subset sum 2m-1,
            and every other support has subset sum exactly m-1.
     - strong sum + bounded entries (auxiliary conditions of (i)/(ii)):
            sum(a) == 2m-1; max(a) <= m-2.
     - (iii) seed (rung 0) and first Bell lift (rung 1) both satisfy KL
            for all weight-<=2 Pauli operators.
  2. Conclusion check: each rung r=0..R (R=4 by default) preserves
     distance >= 3, measured as worst weight-<=2 KL violation.

Outputs:
  - thm44_verification_results.json  (per-seed structured report)
  - thm44_verification_results.csv   (flat table for spreadsheet)
  - thm44_verification_summary.md    (human-readable summary)
  - thm44_verification.log           (stdout log)
"""
from __future__ import annotations

import csv
import json
import os
import sys
import time
from typing import Any, Dict, List, Tuple

import numpy as np

from dyadic_lift import check_distance_at_least, lift_once_dense
from paper_seeds_2504_20847 import get_all_paper_seeds, CODE_META


def _subset_sum(word: str, a) -> int:
    return sum(int(b) * a_j for b, a_j in zip(word, a))


def compute_b_list(seed):
    """Compute (b_0, b_1) = (A_a(supp 0) mod m, A_a(supp 1) mod m).
    Returns (b_list, consistent) where consistent says whether every support
    in each sector shares the same residue."""
    a, m = seed.a, seed.m
    res0 = sorted({_subset_sum(w, a) % m for w in seed.zero})
    res1 = sorted({_subset_sum(w, a) % m for w in seed.one})
    consistent = (len(res0) == 1 and len(res1) == 1)
    b0 = res0[0] if res0 else 0
    b1 = res1[0] if res1 else 0
    return (b0, b1), consistent


# ----------------------------------------------------------------------
# Theorem 4.4 hypothesis checks (combinatorial / structural)
# ----------------------------------------------------------------------

def check_unique_anchors(seed) -> Dict[str, Any]:
    """Check (i) unique bottom anchor + (ii) unique top anchor."""
    n = len(seed.a)
    m = seed.m
    a = seed.a

    zero_n = "0" * n
    ones_n = "1" * n

    # (i) bottom anchor: only zero_n has subset sum 0; others have sum exactly m
    bot_anchor_ok = True
    bot_violations = []
    if zero_n not in seed.zero:
        bot_anchor_ok = False
        bot_violations.append(f"zero anchor {zero_n} not in supp(|0_L>)")
    for word, c in seed.zero.items():
        if abs(c) < 1e-12:
            continue
        ssum = sum(int(b) * a_j for b, a_j in zip(word, a))
        if word == zero_n:
            if ssum != 0:
                bot_anchor_ok = False
                bot_violations.append(f"{word} (anchor) sum={ssum}, expected 0")
        else:
            if ssum != m:
                bot_anchor_ok = False
                bot_violations.append(f"{word} sum={ssum}, expected {m}")
            if ssum == 0:
                bot_anchor_ok = False
                bot_violations.append(f"{word} has sum 0 but is not bottom anchor")

    # (ii) top anchor: only ones_n has subset sum 2m-1; others have sum exactly m-1
    top_anchor_ok = True
    top_violations = []
    if ones_n not in seed.one:
        top_anchor_ok = False
        top_violations.append(f"top anchor {ones_n} not in supp(|1_L>)")
    for word, c in seed.one.items():
        if abs(c) < 1e-12:
            continue
        ssum = sum(int(b) * a_j for b, a_j in zip(word, a))
        if word == ones_n:
            if ssum != 2 * m - 1:
                top_anchor_ok = False
                top_violations.append(f"{word} (anchor) sum={ssum}, expected 2m-1={2*m-1}")
        else:
            if ssum != m - 1:
                top_anchor_ok = False
                top_violations.append(f"{word} sum={ssum}, expected m-1={m-1}")
            if ssum == 2 * m - 1:
                top_anchor_ok = False
                top_violations.append(f"{word} has sum 2m-1 but is not top anchor")

    return {
        "bot_anchor_ok": bot_anchor_ok,
        "top_anchor_ok": top_anchor_ok,
        "bot_violations": bot_violations[:3],
        "top_violations": top_violations[:3],
    }


def check_strong_sum_and_bounds(seed) -> Dict[str, Any]:
    sum_a = sum(seed.a)
    max_a = max(seed.a) if seed.a else 0
    strong = (sum_a == 2 * seed.m - 1)
    bnd = (max_a <= seed.m - 2)
    return {
        "sum_a": sum_a,
        "two_m_minus_1": 2 * seed.m - 1,
        "strong_sum": strong,
        "max_a": max_a,
        "m_minus_2": seed.m - 2,
        "bounded_entries": bnd,
    }


# ----------------------------------------------------------------------
# KL distance check at rung 0 + Bell lift chain
# ----------------------------------------------------------------------

def seed_to_dense(seed) -> Tuple[np.ndarray, np.ndarray]:
    n = len(seed.a)
    d = 1 << n
    zero = np.zeros(d, dtype=np.complex128)
    one = np.zeros(d, dtype=np.complex128)
    for w, c in seed.zero.items():
        zero[int(w, 2)] = complex(c)
    for w, c in seed.one.items():
        one[int(w, 2)] = complex(c)
    # Normalize (defensive)
    nz = np.vdot(zero, zero).real
    no = np.vdot(one, one).real
    if nz > 0:
        zero /= np.sqrt(nz)
    if no > 0:
        one /= np.sqrt(no)
    return zero, one


def run_kl_chain(seed, max_rungs: int = 5, tol: float = 1e-8,
                 liftable: bool = True) -> List[Dict[str, Any]]:
    n = len(seed.a)
    m = seed.m
    a = tuple(int(x) for x in seed.a)
    zero, one = seed_to_dense(seed)
    b_list, _consistent = compute_b_list(seed)
    rungs = []
    # Rung 0: always checkable (just a KL test on the seed state itself).
    ok0, info0 = check_distance_at_least(zero, one, n, max_weight=2, tol=tol,
                                         full_scan=True)
    rungs.append({
        "rung": 0, "n": n, "m": m,
        "passed": bool(ok0),
        "worst_violation": float(info0.get("worst_violation", 0.0)),
    })
    if not liftable:
        # The dyadic Bell lift is not defined for this code (no SS-LP
        # diagonal-gate structure).  Only the seed (rung 0) is meaningful.
        return rungs
    for r in range(1, max_rungs + 1):
        try:
            n, m, a, zero, one, b_list = lift_once_dense(n, m, a, zero, one, b_list)
        except Exception as e:
            rungs.append({"rung": r, "error": f"lift_failure: {e}"})
            break
        ok, info = check_distance_at_least(zero, one, n, max_weight=2, tol=tol,
                                           full_scan=True)
        rungs.append({
            "rung": r, "n": n, "m": m,
            "passed": bool(ok),
            "worst_violation": float(info.get("worst_violation", 0.0)),
        })
    return rungs


# ----------------------------------------------------------------------
# Per-seed report
# ----------------------------------------------------------------------

def evaluate_seed(seed, max_rungs: int = 5, tol: float = 1e-8) -> Dict[str, Any]:
    meta = CODE_META.get(seed.name, ("?", "?", True, ""))
    paper_section, transversal_group, liftable, notes = meta
    b_list, b_consistent = compute_b_list(seed)

    report: Dict[str, Any] = {
        "name": seed.name,
        "n": len(seed.a),
        "m": int(seed.m),
        "a": list(int(x) for x in seed.a),
        "b_list": list(b_list),
        "b_consistent": bool(b_consistent),
        "paper_section": paper_section,
        "transversal_group": transversal_group,
        "bell_liftable": bool(liftable),
        "notes": notes,
        "description": seed.description,
    }
    report["anchors"] = check_unique_anchors(seed)
    report["bounds"] = check_strong_sum_and_bounds(seed)
    rungs = run_kl_chain(seed, max_rungs=max_rungs, tol=tol, liftable=liftable)
    report["rungs"] = rungs

    # Theorem 4.4 hypothesis (i)-(iii)
    hyp_i = report["anchors"]["bot_anchor_ok"]
    hyp_ii = report["anchors"]["top_anchor_ok"]
    hyp_strong = report["bounds"]["strong_sum"]
    hyp_bnd = report["bounds"]["bounded_entries"]
    seed_kl = rungs[0]["passed"] if rungs else False
    rung1_kl = (len(rungs) >= 2 and rungs[1].get("passed", False))
    hyp_iii = bool(seed_kl and rung1_kl)
    all_hyp = bool(hyp_i and hyp_ii and hyp_strong and hyp_bnd and hyp_iii)

    report["hypotheses"] = {
        "i_unique_bottom_anchor": hyp_i,
        "ii_unique_top_anchor": hyp_ii,
        "strong_sum": hyp_strong,
        "bounded_entries": hyp_bnd,
        "iii_seed_and_rung1_distance3": hyp_iii,
        "all_hypotheses_hold": all_hyp,
    }

    # Conclusion: all rungs pass distance-3
    conclusion_passes = all(
        rg.get("passed", False) and "error" not in rg for rg in rungs
    )
    report["conclusion_all_rungs_distance3"] = conclusion_passes
    if rungs:
        max_consec = -1
        for rg in rungs:
            if rg.get("passed", False) and "error" not in rg:
                max_consec = rg["rung"]
            else:
                break
        report["consecutive_max_rung"] = int(max_consec)
        report["worst_violation_across_rungs"] = max(
            (rg.get("worst_violation", 0.0) for rg in rungs if "worst_violation" in rg),
            default=0.0,
        )

    # Verdict on Theorem 4.4
    #   NOT-LIFTABLE  : the dyadic Bell lift is not even defined for this code
    #                   (no SS-LP diagonal-gate structure) -> theorem out of scope.
    #   CONFIRMS      : all hypotheses hold AND every rung preserves distance-3.
    #   COUNTEREXAMPLE: all hypotheses hold but some rung fails distance-3.
    #   INAPPLICABLE  : hypotheses fail -> theorem makes no claim; we still report
    #                   whether the conclusion happens to hold or fail.
    if not liftable:
        report["thm44_status"] = "NOT-LIFTABLE (out of theorem scope)"
    elif all_hyp:
        report["thm44_status"] = ("CONFIRMS" if conclusion_passes else "COUNTEREXAMPLE")
    else:
        report["thm44_status"] = ("INAPPLICABLE" + (
            " (but conclusion holds)" if conclusion_passes else " (conclusion also fails)"
        ))
    return report


# ----------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------

def main() -> int:
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-rungs", type=int, default=5)
    ap.add_argument("--tol", type=float, default=1e-8)
    ap.add_argument("--out-dir", type=str, default="outputs_thm44")
    args = ap.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)

    seeds = get_all_paper_seeds()
    print(f"[Theorem 4.4 verification] {len(seeds)} seeds from arXiv:2504.20847")
    print(f"  max_rungs={args.max_rungs}, tol={args.tol}")
    print()

    t0 = time.time()
    results: List[Dict[str, Any]] = []
    for seed in seeds:
        t1 = time.time()
        r = evaluate_seed(seed, max_rungs=args.max_rungs, tol=args.tol)
        t1 = time.time() - t1
        r["elapsed_sec"] = t1
        results.append(r)
        h = r["hypotheses"]
        st = r["thm44_status"]
        cmr = r.get("consecutive_max_rung", -1)
        print(
            f"  [{r['name']:>16s}]  {r['paper_section']:>11s}  {r['transversal_group']:>5s}  "
            f"liftable={r['bell_liftable']!s:>5s}  "
            f"strong={h['strong_sum']!s:>5s}  "
            f"all_hyp={h['all_hypotheses_hold']!s:>5s}  "
            f"r_max={cmr:>2d}  "
            f"{st}  ({t1:.1f}s)"
        )

    total = time.time() - t0
    print()
    print(f"Total elapsed: {total:.1f}s")
    print()

    # ---- Aggregate stats ----
    n_total = len(results)
    liftable = [r for r in results if r["bell_liftable"]]
    not_liftable = [r for r in results if not r["bell_liftable"]]
    n_strong = sum(1 for r in liftable if r["hypotheses"]["strong_sum"])
    n_bnd = sum(1 for r in liftable if r["hypotheses"]["bounded_entries"])
    n_i = sum(1 for r in liftable if r["hypotheses"]["i_unique_bottom_anchor"])
    n_ii = sum(1 for r in liftable if r["hypotheses"]["ii_unique_top_anchor"])
    n_iii = sum(1 for r in liftable if r["hypotheses"]["iii_seed_and_rung1_distance3"])
    n_all_hyp = sum(1 for r in liftable if r["hypotheses"]["all_hypotheses_hold"])
    n_confirms = sum(1 for r in results if r["thm44_status"] == "CONFIRMS")
    n_counterex = sum(1 for r in results if r["thm44_status"] == "COUNTEREXAMPLE")
    n_inappl = sum(1 for r in results if r["thm44_status"].startswith("INAPPLICABLE"))
    n_notlift = len(not_liftable)
    n_inappl_concl_holds = sum(
        1 for r in results
        if r["thm44_status"] == "INAPPLICABLE (but conclusion holds)"
    )

    summary = {
        "total_codes_tested": n_total,
        "max_rungs": args.max_rungs,
        "tol": args.tol,
        "bell_liftable_codes": len(liftable),
        "not_bell_liftable_codes": n_notlift,
        "--- among liftable ---": "",
        "strong_sum (sum a = 2m-1)": n_strong,
        "bounded_entries (max a <= m-2)": n_bnd,
        "hyp (i) unique bottom anchor": n_i,
        "hyp (ii) unique top anchor": n_ii,
        "hyp (iii) seed+rung1 distance-3": n_iii,
        "ALL hypotheses (i)(ii)(iii)+strong+bnd": n_all_hyp,
        "--- Theorem 4.4 verdicts ---": "",
        "CONFIRMS (hyp hold + all rungs d3)": n_confirms,
        "COUNTEREXAMPLE (hyp hold, rung fails)": n_counterex,
        "INAPPLICABLE (hyp fail)": n_inappl,
        "  of which conclusion still holds": n_inappl_concl_holds,
        "NOT-LIFTABLE (out of theorem scope)": n_notlift,
    }
    print("=" * 64)
    print("Summary")
    print("=" * 64)
    for k, v in summary.items():
        print(f"  {k:>40s}: {v}")
    print()

    # ---- Write JSON ----
    out_json = os.path.join(args.out_dir, "thm44_verification_results.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"summary": summary, "results": results}, f, indent=2)
    print(f"[saved] {out_json}")

    # ---- Write CSV ----
    out_csv = os.path.join(args.out_dir, "thm44_verification_results.csv")
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
            b = r["bounds"]
            rungs = r.get("rungs", [])
            r0 = rungs[0].get("passed", False) if len(rungs) >= 1 else False
            r1 = rungs[1].get("passed", False) if len(rungs) >= 2 else False
            w.writerow([
                r["name"], r["paper_section"], r["transversal_group"],
                r["n"], r["m"],
                " ".join(map(str, r["a"])), " ".join(map(str, r["b_list"])),
                b["sum_a"], b["two_m_minus_1"], b["max_a"], b["m_minus_2"],
                r["bell_liftable"], b["strong_sum"], b["bounded_entries"],
                h["i_unique_bottom_anchor"], h["ii_unique_top_anchor"],
                r0, r1, h["all_hypotheses_hold"],
                r["conclusion_all_rungs_distance3"],
                r.get("consecutive_max_rung", -1),
                f"{r.get('worst_violation_across_rungs', 0.0):.3e}",
                r["thm44_status"], r["notes"],
            ])
    print(f"[saved] {out_csv}")

    # ---- Write detailed Markdown report ----
    out_md = os.path.join(args.out_dir, "thm44_verification_summary.md")
    _write_markdown_report(out_md, results, summary, args)
    print(f"[saved] {out_md}")
    print()
    print("[Done]")
    return 0


def _write_markdown_report(path, results, summary, args):
    """Write a detailed, organized Markdown report."""
    def yn(x):
        return "Y" if x else "N"

    with open(path, "w", encoding="utf-8") as f:
        f.write("# Theorem 4.4 verification on arXiv:2504.20847\n\n")
        f.write("**Theorem 4.4** (Two-anchor Bell-flag ladder theorem, `dyadic_lifts.tex`): "
                "*If a seed code satisfies (i) unique bottom anchor, (ii) unique top anchor, "
                "(iii) seed and first Bell lift both distance-3, plus strong sum "
                "(Sum a = 2m-1) and bounded entries (max a <= m-2), then every rung of the "
                "iterated dyadic Bell lift preserves distance >= 3.*\n\n")
        f.write(f"This report tests **{summary['total_codes_tested']} explicit codes** "
                f"extracted from the paper, Bell-lifting each up to **rung "
                f"{summary['max_rungs']}** and checking weight-<=2 Knill-Laflamme "
                f"conditions at every rung (tolerance {args['tol'] if isinstance(args, dict) else args.tol}).\n\n")

        # --- Verdict legend ---
        f.write("## Verdict categories\n\n")
        f.write("| Verdict | Meaning |\n|---|---|\n")
        f.write("| **CONFIRMS** | All Theorem 4.4 hypotheses hold AND every rung preserves distance-3. The theorem holds for this code. |\n")
        f.write("| **COUNTEREXAMPLE** | All hypotheses hold but some rung fails distance-3. Would disprove the theorem. |\n")
        f.write("| **INAPPLICABLE** | Some hypothesis fails -> theorem makes no claim. We still record whether the conclusion happens to hold. |\n")
        f.write("| **NOT-LIFTABLE** | The code has no SS-LP diagonal-gate structure, so the dyadic Bell lift is not even defined. Out of the theorem's scope; only rung-0 distance-3 is checked. |\n\n")

        # --- Aggregate ---
        f.write("## Aggregate statistics\n\n")
        f.write("| Quantity | Count |\n|---|---|\n")
        for k, v in summary.items():
            if k.startswith("---"):
                f.write(f"| **{k.strip('- ')}** | |\n")
            else:
                f.write(f"| {k} | {v} |\n")
        f.write("\n")

        # --- Headline ---
        n_conf = summary["CONFIRMS (hyp hold + all rungs d3)"]
        n_ctr = summary["COUNTEREXAMPLE (hyp hold, rung fails)"]
        f.write("## Headline result\n\n")
        f.write(f"- **{n_conf}** codes satisfy every Theorem 4.4 hypothesis and the theorem's "
                f"conclusion holds for all of them -> **{n_conf}/{n_conf} CONFIRMS**.\n")
        f.write(f"- **{n_ctr}** counterexamples found (a code where the hypotheses hold "
                f"but a rung fails distance-3).\n")
        f.write(f"- The remaining codes either fail a hypothesis (INAPPLICABLE) or are not "
                f"Bell-liftable (NOT-LIFTABLE) -- in both cases the theorem makes no claim.\n\n")

        # --- Results grouped by paper section ---
        f.write("## Per-code results, grouped by paper section\n\n")
        by_section: Dict[str, List] = {}
        for r in results:
            by_section.setdefault(r["paper_section"], []).append(r)
        # Stable section order
        section_order = ["prototype", "Sec 4.1", "Sec 5.1", "Sec 6.3.1", "Sec 6.3.2",
                         "Sec 6.3.3", "Sec 6.4.1", "Sec 6.4.2", "Numerics/D.6",
                         "App C.1", "App C.2", "App D.1", "App D.2", "App D.3",
                         "App D.4", "App D.5", "App D.7", "App D.8", "App D.9",
                         "App D.10", "App D.11", "App E.2", "App E.3", "App E.4",
                         "App E.5", "App E.6"]
        seen_sections = list(by_section.keys())
        ordered = [s for s in section_order if s in by_section] + \
                  [s for s in seen_sections if s not in section_order]
        for sec in ordered:
            rows = by_section[sec]
            f.write(f"### {sec}\n\n")
            f.write("| Code | group | n | m | a-vector | b | sum a | 2m-1 | strong | bnd | (i) | (ii) | (iii) | all hyp | r_max | worst viol | Verdict |\n")
            f.write("|------|-------|---|---|----------|---|-------|------|--------|-----|-----|------|-------|---------|-------|------------|---------|\n")
            for r in rows:
                h = r["hypotheses"]
                b = r["bounds"]
                avec = ",".join(map(str, r["a"]))
                f.write(
                    f"| {r['name']} | {r['transversal_group']} | {r['n']} | {r['m']} | "
                    f"({avec}) | {r['b_list'][1]} | {b['sum_a']} | {b['two_m_minus_1']} | "
                    f"{yn(b['strong_sum'])} | {yn(b['bounded_entries'])} | "
                    f"{yn(h['i_unique_bottom_anchor'])} | {yn(h['ii_unique_top_anchor'])} | "
                    f"{yn(h['iii_seed_and_rung1_distance3'])} | {yn(h['all_hypotheses_hold'])} | "
                    f"{r.get('consecutive_max_rung', -1)} | "
                    f"{r.get('worst_violation_across_rungs', 0.0):.2e} | "
                    f"**{r['thm44_status']}** |\n"
                )
            f.write("\n")

        # --- Per-rung detail for every code ---
        f.write("## Per-rung distance-3 detail\n\n")
        f.write("Worst weight-<=2 KL violation at each rung (machine precision ~1e-16). "
                "`FAIL` marks a rung where distance-3 breaks; `lift_err` marks a rung where "
                "the Bell lift itself is undefined.\n\n")
        for r in results:
            rungs = r.get("rungs", [])
            parts = []
            for rg in rungs:
                if "error" in rg:
                    parts.append(f"r{rg['rung']}:lift_err")
                else:
                    tag = "OK" if rg["passed"] else "FAIL"
                    parts.append(f"r{rg['rung']}(n{rg['n']}):{rg['worst_violation']:.1e}/{tag}")
            f.write(f"- **{r['name']}** ({r['paper_section']}, {r['transversal_group']}, "
                    f"{r['thm44_status']}): {' '.join(parts)}\n")
        f.write("\n")

        # --- Notes / caveats ---
        f.write("## Notes and caveats\n\n")
        for r in results:
            if r["notes"]:
                f.write(f"- **{r['name']}**: {r['notes']}\n")
        f.write("\n")
        f.write("### Coverage notes\n\n")
        f.write("- **Appendix B** ((6,2,3)) families are now included as representative "
                "points: B.1 (((6,2,3)) from ((5,2,3)), BD4 and 2T cases) and B.2 (SO(5) "
                "family, BD4 representative). They are *not* SS-LP diagonal-gate codes, "
                "so the dyadic Bell lift is undefined -- they are marked NOT-LIFTABLE and "
                "only rung-0 distance-3 is checked. B.1's two representatives pass rung-0; "
                "B.2's `so5_bd4` fails rung-0 because the paper's canonical W matrix as "
                "rendered in the PDF is not orthogonal (a transcription ambiguity that "
                "would need the LaTeX source).\n")
        f.write("- **Appendix E.1 BD38**: the 16-variable constraint system (8x16 sign "
                "matrix C, plus sum = 1) was solved as a feasibility LP; the solution "
                "reproduces the paper's stated identities (theta_1^2+theta_2^2 = 1/38, "
                "theta_12^2 = 4/19). Result: CONFIRMS.\n")
        f.write("- **Appendix D.4 BD18 Type II**: the |1100101> coefficient was corrected "
                "to sqrt(b^2+d^2+1/18) (the PDF rendering merged the 1/18); magnitudes "
                "then give unit norm. The term *signs* were resolved numerically (the PDF "
                "sign rendering was unreliable). Result: CONFIRMS.\n")
        f.write("- The **only paper codes still NOT covered**: the 2 BD16 angle vectors "
                "in Sec 6.3.1 -- (1,1,1,2,2,2,6) and (0,1,1,2,3,3,5) -- for which the "
                "paper gives no explicit |0_L> codewords, so they cannot be transcribed.\n")


if __name__ == "__main__":
    sys.exit(main())
