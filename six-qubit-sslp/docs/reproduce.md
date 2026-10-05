# Reproducing the six-qubit formalization

Use the `sixqubit-classification` branch. From the GitHub repository root:

```console
cd six-qubit-sslp
lake exe cache get
python tools/build_lean.py
python tools/verify.py --paper-version 20261003 --only sources generated audit-names axioms
python tools/repository_index.py --check
python -m unittest discover -s tools/tests -p test_certification_tools.py -v
python -m unittest discover -s tools/tests -p test_paper_release.py -v
```

Lean is pinned by `lean-toolchain` and Mathlib by `lake-manifest.json`.
The serial builder checks the active proof libraries, validates source and
dependency hashes before reusing compiled files, and records its successful
module inventory under `.lake/build/certification/`. This is an incremental
build; a checkout without compiled artifacts must elaborate the finite
certificates. Build duration depends strongly on the available cache.

The source gate rejects proof placeholders and compiler-backed proof escapes.
The generated gate checks exact certificate coverage, hashes and build order.
The axiom gate checks the transitive footprint of all selected audit roots and
permits only `propext`, `Classical.choice` and `Quot.sound`.

These commands do not require the private manuscripts. Python tooling tests
may skip controls that require unavailable private sources or optional tiny
Lean checks; their test output reports those skips explicitly.

## Focused orbit checks

```console
python tools/build_lean.py --module MainTheory.Orbit2FullImage --module MainTheory.Orbit3FullImage --module MainTheory.OrbitCertificationFinalAudit
lake env lean -j 1 -DwarningAsError=true MainTheory/OrbitCertificationFinalAudit.lean
python tools/rebuild_orbit_certificates.py
```

The certificate regeneration check independently reconstructs finite rational
payloads. The actual-encoder semantics and final interval statements are Lean
theorems, audited separately.

## Private-source correspondence checks

Authors who have the current private sources can place them in
`documents/20261003/` or use the supported `--source-dir` option:

```console
python tools/paper_claims.py check --paper-version 20261003
python tools/named_results_doc.py --paper-version 20261003 --check
python tools/verify.py --paper-version 20261003 --only release named-results
```

The full manuscript acceptance command is:

```console
python tools/verify.py --paper-version 20261003
```

It is expected to fail the incomplete correspondence/prose/errata gates until
those reviews and held author decisions are complete. See [status](status.md).
Successful source, build and axiom checks must not be presented as a successful
full manuscript release.
