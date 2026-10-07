# Explore SSLP Classification

[Repository home](../README.md) · [Reproduce](reproduce.md) · [Status](status.md)

Use the curated entry points to read the mathematics, then the complete catalog
to find supporting modules. Generated certificate shards are grouped by family
in the catalog.

## Choose a reading path

| Path | Read first | Then follow |
| --- | --- | --- |
| General theory | [Main-text proof map](proof-index.md#main-text-theory) | [QECC provenance](../QECC/README.md) and [physical bridges](../MainTheory/QECCFrameBridge.lean) |
| Six-qubit classification | [Supplementary proof map](proof-index.md#supplementary-material) | [SixQubit entry module](../SixQubit.lean) and the relevant orbit |
| Orbit 2 and orbit 3 | [Orbit2FullImage](../MainTheory/Orbit2FullImage.lean) · [Orbit3FullImage](../MainTheory/Orbit3FullImage.lean) | [Focused reproduction](reproduce.md#focused-orbit-checks) and [exact data](reproduce.md#finite-certificate-data) |
| Manuscript review | [Reviewer guide](review-guide.md) | [Version-bound correspondence](manuscript-correspondence.md) and [held main issues](status.md#current-manuscript-review) |
| Development | [Architecture](architecture.md) | [Contribution guide](../CONTRIBUTING.md) and [tool overview](../tools/README.md) |

## Documentation shelf

| Guide | Purpose |
| --- | --- |
| [Proof index](proof-index.md) | Selected theorem entry points and the detailed main/SI map |
| [Modules by topic](proof-modules.md) | Generated inventory of all active Lean modules |
| [Reproduction](reproduce.md) | Setup, kernel checks, exact data checks, and private-source review |
| [Reviewer guide](review-guide.md) | How to follow a claim to its theorem and acceptance evidence |
| [Status](status.md) | Recorded outcomes, manuscript version, held issues, and open questions |
| [Manuscript correspondence](manuscript-correspondence.md) | What the accepted source-specific correspondence covers |
| [Architecture](architecture.md) | Library responsibilities, dependencies, and supporting directories |
| [Historical archive](../HISTORY.md) | Fixed tags for the dyadic project and the earlier repository layout |

The status records concern the `20261003` manuscript snapshot. New manuscript
versions need their own review; a later repository commit alone does not extend
the scope of those records.
