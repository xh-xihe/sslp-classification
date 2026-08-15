# Theorem-hypothesis sweep report

`sweep_report.tex` is one document merged from what used to be a main report and
a separate supplement. Where the two overlapped, the supplement's tables were
kept: they are the ones corrected against the sweep data. The old main-report
copies were stale (missing `bd20`, `bd24` shown as failing at rung 0, and a
mechanism paragraph built on that error).

```bash
python check_sweep_report.py      # re-derives every table from ../data/
latexmk -pdf sweep_report.tex     # 10 pages
```

`check_sweep_report.py` parses the report with LaTeX comments stripped and
checks the scoreboard, the three verdict tables against their captions, all 43
per-rung rows cell by cell, and the first-failing-rung distribution against
`../data/thm44_verification_results.json`. It exits nonzero on any mismatch.
