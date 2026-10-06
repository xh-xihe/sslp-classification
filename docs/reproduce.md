# Reproducing the six-qubit formalization

Use the `main` branch. From the GitHub repository root:

```console
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

## Current literal correspondence proof sources

Reproduce the forty source generators for the current support, block, moment,
physical phase and enumerator batch:

```console
python tools/verification/check_orbit31_reproduction.py
```

This checks exact source provenance. Kernel acceptance still requires the
serial whole build and transitive axiom audit above. The proof layers are
indexed by mathematical topic in [proof-index.md](proof-index.md).

## Literal physical orbit-30 sources

Reconstruct its eight finite source certificates with:

```console
python tools/verification/check_orbit30_reproduction.py
```

These exact source checks supplement the whole kernel build and axiom audit.
The physical graph and determinant entry points appear in [proof-index.md](proof-index.md).

## Split and physical matrix sources

Reconstruct the three finite source certificates with:

```console
python tools/verification/check_split_matrix_reproduction.py
```

This checks exact source reconstruction; the separate whole kernel build and
standard-axiom audit remain required.

## Shell and parity-frame sources

```console
python tools/verification/check_frame_anchor_reproduction.py
```

This checks the exact shell/parity source reconstruction and hashes the ten
accepted frame/anchor sources. Whole kernel building and the transitive
standard-axiom audit remain separate required checks.

## Matching and parity source snapshot

```console
python tools/verification/check_matching_parity_snapshot.py
```

This checks the LF hashes of the fifteen matching/parity sources against
their recorded snapshot. It does not replace whole kernel building,
fresh transitive standard-axiom auditing or manuscript type review.

## Scalar and spinor source snapshot

```console
python tools/verification/check_scalar_spinor_snapshot.py
```

This checks the LF hashes of the twelve scalar/spinor sources against
their recorded snapshot. It does not replace whole kernel building,
fresh transitive standard-axiom auditing or manuscript type review.

## Display-route source snapshot

```console
python tools/verification/check_display_route_snapshot.py
```

This checks the canonical LF hashes of all twenty display-route modules
against their strict-pilot snapshot. Whole kernel building, transitive
standard-axiom auditing and manuscript type review remain separate checks.

## Final SI correspondence sources

```console
python tools/verification/check_final_bridge_snapshot.py
```

This checks the nine final bridge LF source hashes against their strict-pilot
snapshot. The whole kernel build and standard-axiom audit remain required.
With the exact current private manuscript sources also available, run:

```console
python tools/verification/check_si_correspondence.py
```

This checks all 1,622 SI mathematical entries, three scope-only remarks and
the complete running-context review. The combined main/SI claims, prose and
errata completeness gates deliberately retain the five frozen main issues.
See [manuscript correspondence](manuscript-correspondence.md).

## Finite certificate data

The supplementary manuscript describes the mathematical reductions and
identities. The complete coefficient data and implementation details are
available here, using paths relative to `six-qubit-sslp`:

| Certificate | Exact calculation | Complete data |
| --- | --- | --- |
| Orbit 2: quartic matrix and positive character blocks | [orbit2_exact_certificate.py](../tools/certificates/orbit2_exact_certificate.py) | [gram-blocks.json](../results/orbit2-kernel/gram-blocks.json) |
| Orbit 3: six scalar dual certificates | [orbit3_scalar_certificate.py](../tools/certificates/orbit3_scalar_certificate.py) | [scalar-certificate.json](../results/orbit3-kernel/scalar-certificate.json) |
| Orbit 3: degree-six identity and positive cubic square | [orbit3_exact_sextic_certificate.py](../tools/certificates/orbit3_exact_sextic_certificate.py) | [certificate.json](../results/orbit3-kernel/certificate.json), [reduced-coefficients.json](../results/orbit3-kernel/reduced-coefficients.json) |

These finite calculations use the Python standard library. To reconstruct
each payload and compare it with the stored data, run:

```console
python tools/rebuild_orbit_certificates.py --only orbit2
python tools/rebuild_orbit_certificates.py --only scalar
python tools/rebuild_orbit_certificates.py --only orbit3
```

The orbit-2 calculation reconstructs the integer matrix from its polynomial
and verifies every block by rational `LDL^T` elimination. Its exported block
data are supporting records, not inputs to the matrix reconstruction. The
scalar calculation reconstructs the rational duals, including all equality
multipliers, inequality multipliers and variable remainders.

The degree-six calculation takes the rational certificate terms as input,
reconstructs the moment coordinates and constraint rows, and compares all
269 coefficients. To also sum all 120 target rows independently, run:

```console
python tools/certificates/orbit3_exact_sextic_certificate.py --exhaustive-target
```

Its `--json PATH` option writes verification metadata, not a newly discovered
certificate. The output includes a digest of the target, square and final
coefficient arrays. Numerical controls are separate from these exact checks.
For the enumeration and other orbit proofs, follow the modules in the
[proof index](proof-index.md) and the [source inventory](../results/proof-modules.json).

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
