# Numerics

Nine modules, the complete import closure of the four entry points. Nothing
else from the working tree is needed.

| file | role |
|---|---|
| `dyadic_lift.py` | the Bell lift and the weight-≤2 distance-3 check |
| `generate_lift_codewords.py` | builds rung-`r` codewords from a seed |
| `paper_seeds_2504_20847.py` | the 43 seeds of arXiv:2504.20847, with provenance per code |
| `paper_seeds_2510_20728.py` | the 10 Appendix-F codes of arXiv:2510.20728, plus 2 no-go cases |
| `sslp_utils.py` | bitstrings, supports, exact-rational helpers |
| `verify_paper_seeds.py` | **entry** — lifts 14 seeds ×4, checks `d ≥ 3` |
| `verify_thm44_paper.py` | **entry** — the 43-instance hypothesis sweep |
| `verify_thm44_paper_2510.py` | **entry** — the same theorem on a second amplitude family |
| `_adv_bd12_typeII.py` | **entry** — adversarial re-verification of one failing code |

## The four runs

```bash
python verify_paper_seeds.py                 # ~2 min, exit 0 on success
python verify_thm44_paper.py --max-rungs 5 --tol 1e-8 --out-dir outputs
python verify_thm44_paper_2510.py            # ~3 min
python _adv_bd12_typeII.py                   # seconds
```

`verify_thm44_paper.py` must report 30 CONFIRMS / 0 COUNTEREXAMPLE /
9 INAPPLICABLE / 4 NOT-LIFTABLE.

`verify_thm44_paper_2510.py` re-runs the theorem on the ten Appendix-F codes of
arXiv:2510.20728. Those use the **same weight vectors** as `bd16_01..10` of
arXiv:2504.20847 but **different amplitude representatives**, drawn from the
closed-form families of that appendix. All ten confirm, which is evidence that
the theorem's verdicts track the arithmetic hypotheses rather than a particular
choice of amplitudes.

`_adv_bd12_typeII.py` re-verifies `bd12_type_II` from scratch **without
importing the distance checker used everywhere else**: it transcribes the
codewords independently from the source LaTeX, builds every weight-≤2 Pauli as
an explicit Kronecker product, and recomputes the hypothesis arithmetic. It
reproduces the main sweep's verdict — rung 0 passes, rung 1 onward fails — so
that verdict does not rest on a single implementation.

See `../REPRODUCE.md` for how to diff a fresh run against the checked-in
`../data/`.
