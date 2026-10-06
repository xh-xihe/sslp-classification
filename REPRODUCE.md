# Reproducing the classification proofs

Use `main` and run commands from the active package:

```console
cd six-qubit-sslp
lake exe cache get
python tools/build_lean.py
python tools/verify.py --paper-version 20261003 --only sources generated audit-names axioms
python tools/repository_index.py --check
```

The [package reproduction guide](six-qubit-sslp/docs/reproduce.md) documents
the pinned Lean/Mathlib environment, Python checks, resource settings,
dependency-stamp validation and private-source correspondence gates.
Use [verification status](six-qubit-sslp/docs/status.md) to distinguish
accepted proof snapshots from manuscript correspondence and open claims.

The independent dyadic project's reproduction instructions are retained in
its [historical archive](HISTORY.md).
