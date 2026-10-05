# Reproducing

For the six-qubit classification project, use [its reproduction guide](six-qubit-sslp/docs/reproduce.md). The commands below concern the dyadic Bell ladder.

Every numeric claim in this repository is re-derivable from it. This file gives
the commands, the expected output, and the environment.

`paper/dyadic_lifts.tex` is the development note and will be replaced by a
publication version. It proves the ladder theorem in the abstract; the explicit
seed, the unconditional family, and the exact-distance result are established by
`code/` and `lean/`.

---

## Environment

| | |
|---|---|
| OS | Windows 11 (10.0.26200); nothing here is Windows-specific |
| Python | 3.12.7 |
| numpy | 1.26.4 |
| scipy | 1.13.1 |
| sympy | 1.14.0 |
| Lean toolchain | `leanprover/lean4:v4.27.0`, pinned in `lean/lean-toolchain` |
| Mathlib | `fc278a179e431ed10630af63fc05481680c0c7bd`, pinned in `lean/lake-manifest.json` |
| TeX | TeX Live 2025 (the note needs only `article` and standard packages) |

```bash
pip install -r requirements.txt
```

`gmpy2` is optional; without it the exact-rational path falls back to
`fractions.Fraction`, which is slower and gives the same values.

---

## 1. The numeric claims

```bash
cd paper
python tools/run_all_checks.py
```

Runs six verifiers and exits **nonzero** if any of them no longer holds. Takes
about a minute. The first five are self-contained computations; they do not read
the note, so they stay valid when the note is replaced.

| script | certifies |
|---|---|
| `check_bell_table.py` | the Bell-pair Pauli table, all sixteen Paulis |
| `check_rung1.py` | the rung-1 code of the explicit seed: norms, sectors mod `m₁=16`, the `D₁₆` action, 352 weight-≤2 Paulis |
| `check_exact_distance.py` | the weight-three witness `XXZ` at rungs 0–4 |
| `check_witness_detail.py` | the rung-0 detail of the exactness argument |
| `check_sweep.py` | every number of the theorem-hypothesis sweep, including where the failures occur |
| `prose_audit.py` | prose tics in the note; the scope-disclaimer counts are inactive for it |

Expected last line: `all 6 verification scripts passed`.

---

## 2. The note itself

```bash
cd paper
latexmk -pdf dyadic_lifts
```

Expect 0 errors, 0 undefined references, 18 pages. The note is self-contained:
`article` class, an inline `thebibliography` with 18 entries, no `\input` and no
external figures, so no BibTeX pass is required.

---

## 3. The Lean formalization

```bash
cd lean
lake exe cache get      # prebuilt Mathlib artifacts; see the note below
lake build
```

`lake build` is the whole verification: it checks every proof and runs both
axiom guards. A change in the axiom footprint of any of the 25 guarded results
is a **build error**, not a warning.

Budget about **three hours** for a first build. Nearly all of it is one module:
`DyadicLifts/Seed/Checks.lean` measured 10,487 s (2.9 h) on a 24-core machine.
The rest of the development takes about 1.5 minutes once Mathlib is in place.
Rebuilds after an edit outside `Seed/Checks.lean` replay that module from cache
and finish in seconds.

The seed's checks enumerate `Finset.univ` over `BitString 9` by structural
recursion, which overflows the default 8 MB thread stack. The package raises it
itself (`moreLeanArgs := #["-s", "2000000"]` in `lakefile.lean`), so plain
`lake build` suffices.

*Windows note.* `lake exe cache get` may report a `tar` error while unpacking
the optional ProofWidgets blob. That blob is editor decoration; proof checking
is unaffected. If it blocks the fetch, unpack it once by hand and re-run:

```bash
tar -xz -f .lake/packages/proofwidgets/.lake/ProofWidgets4.tar.gz \
    -C .lake/packages/proofwidgets/.lake/build
```

### Checking the trust base yourself

```bash
cd lean
grep -rn "native_decide" DyadicLifts SS          # documentation comments only
grep -rnw "sorry\|admit\|axiom\|unsafe" DyadicLifts SS
```

For the axiom footprint of any theorem, ask Lean directly:

```lean
import DyadicLifts
#print axioms BD16Kernel.exists_distance3_family
-- 'BD16Kernel.exists_distance3_family' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

`DyadicLifts/Seed/Checks.lean` is generated. `python gen_checks.py` from the
`lean/` directory rewrites it and reproduces the committed file byte for byte.

---

## 4. The seed lift check

```bash
cd code
python verify_paper_seeds.py
```

Lifts all 14 published seeds four times and checks distance 3 at every rung, in
floating point, independently of Lean. Exit 0 on success; expect worst
violations around `5e-16`.

---

## 5. The theorem-hypothesis sweep

```bash
cd code
python verify_thm44_paper.py --max-rungs 5 --tol 1e-8 --out-dir outputs
```

Must produce **30** `CONFIRMS` / **0** `COUNTEREXAMPLE` / **9** `INAPPLICABLE`
/ **4** `NOT-LIFTABLE`, and write `thm44_verification_results.{json,csv}`.

The copy in `data/` is the run that `results/sweep_report.tex` reports. To
confirm a fresh run agrees with it:

```bash
python -c "import json,io; a=json.load(io.open('outputs/thm44_verification_results.json',encoding='utf-8')); b=json.load(io.open('../data/thm44_verification_results.json',encoding='utf-8')); ka={r['name']:r['thm44_status'] for r in (a if isinstance(a,list) else a['results'])}; kb={r['name']:r['thm44_status'] for r in (b if isinstance(b,list) else b['results'])}; print('verdicts identical:', ka==kb)"
```

This was checked. A fresh run on the machine described above reproduced the
shipped file exactly: all 43 codes, identical verdicts, identical per-rung
pass/fail, identical hypothesis flags, and `worst_violation_across_rungs` equal
to the last bit (largest difference `0.0`). The only field that differed was
`elapsed_sec`, the timing itself.

Across *different* machines or BLAS builds, expect the floating-point fields to
differ in the last digits. The verdicts and the per-rung pass/fail pattern
should not.

---

## 5b. Two checks against self-confirmation

```bash
cd code
python verify_thm44_paper_2510.py     # ~3 min
python _adv_bd12_typeII.py            # seconds
```

The first re-runs the theorem over the ten Appendix-F codes of
arXiv:2510.20728, which use the same weight vectors as `bd16_01..10` but
different amplitude representatives. Expect **10 CONFIRMS / 0 COUNTEREXAMPLE /
0 INAPPLICABLE**; the two Appendix-G cases are infeasible by published proofs,
have no codeword, and make the theorem vacuous. Results are checked in as
`data/thm44_verification_results_2510_20728.{json,csv}`.

The second re-verifies `bd12_type_II` without importing the distance checker
used elsewhere. Expect `r0 PASS`, then `r1`–`r5 FAIL` — matching the main
sweep's row for that code.

---

## 6. The sweep report

```bash
cd results
python check_sweep_report.py
latexmk -pdf sweep_report.tex
```

The checker parses `sweep_report.tex` with comments stripped and re-derives
every table from `data/thm44_verification_results.json`: the scoreboard, the
three verdict tables against their captions, all 43 per-rung rows cell by cell,
and the first-failing-rung distribution. It exits nonzero on any disagreement.

Expect 10 pages from `latexmk`.

---

## What is not pinned

Floating-point results depend on hardware and BLAS. On one machine the sweep is
bit-reproducible (see §5); across machines, expect agreement in the verdicts and
the pass/fail pattern rather than in the last digits. Differences observed
between the accelerated and CPU reference implementations were bounded by
`2.1e-13` absolute.

Runtime is not pinned either: the sweep took 8.5 min of compute on an idle
machine and about 12.5 min with another job competing for the CPU.

The Lean build is fully pinned: the toolchain by `lean-toolchain`, Mathlib by
`lake-manifest.json`.
