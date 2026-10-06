# Six-qubit classification and general SSLP formalization

The canonical branch is **`main`**. This project lives in
`six-qubit-sslp/` in the GitHub repository and combines the main-text theory,
the supplementary classification, and the complete orbit-2/3 image proofs.

Start with [current status](docs/status.md), [proof entry points](docs/proof-index.md),
[modules by topic](docs/proof-modules.md), and [reproduction instructions](docs/reproduce.md).
The [architecture guide](docs/architecture.md) explains the library boundaries.

## Verification scope

The complete orbit-2 and orbit-3 normalized enumerator images, including
converse and attainment for actual full-KL encoders, are proved in
[Orbit2FullImage](MainTheory/Orbit2FullImage.lean) and
[Orbit3FullImage](MainTheory/Orbit3FullImage.lean).

The trust target is the Lean kernel with only `propext`, `Classical.choice`
and `Quot.sound`. Source/build/generated-data/axiom checks and manuscript
correspondence checks have separate recorded outcomes. **Full manuscript
certification remains open:** current source-context review and held main-text
errata are recorded in [status](docs/status.md). Orbit-1/4 full enumerator
image questions also remain open.

## Reproduce the proof checks

Run from `six-qubit-sslp/` in a remote checkout, or from this directory locally:

```console
lake exe cache get
python tools/build_lean.py
python tools/verify.py --paper-version 20261003 --only sources generated audit-names axioms
python tools/repository_index.py --check
```

Lean and Mathlib are pinned by `lean-toolchain` and `lake-manifest.json`.
The serial builder validates content and dependency stamps before reusing a
compiled module. See [reproduce](docs/reproduce.md) for tests, focused checks,
private-source correspondence gates and the meaning of each result.

## Layout

| Directory | Role |
| --- | --- |
| [`SS/`](SS) | Shared Pauli, bitstring and KL foundations |
| [`QECC/`](QECC/README.md) | Section III formalization and its port provenance |
| [`MainTheory/`](MainTheory) | General theory, physical semantics and paper-facing bridges |
| [`SixQubit/`](SixQubit) | Orbit classifications, constructions and generated certificates |
| [`Orbit2/`](Orbit2) | Imported orbit-2 proof package |
| [`docs/`](docs/architecture.md) | Current navigation and verification instructions |
| [`tools/`](tools/README.md) | Generators, verification tools and regression tests |
| [`results/`](results/README.md) | Current status, source catalog and review records |
| [`artifacts/`](artifacts) | Dated acceptance and integration evidence |
| [`archive/`](archive/README.md) | Superseded stages, reviews and documentation |

The private manuscripts are excluded from the public repository. Version-bound
records refer to their hashes and labels. Earlier progress counts are preserved
in [the archived README](archive/documentation/README-pre-20261004.md);
[current status](docs/status.md) is the current entry point.
