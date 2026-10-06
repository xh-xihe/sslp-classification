# Repository architecture

The canonical branch is `main`. In the GitHub repository,
this project lives in `six-qubit-sslp/`; run its commands from that directory.
The earlier independent dyadic-lift project is preserved in the
[historical archive](https://github.com/xh-xihe/sslp-classification/blob/main/HISTORY.md),
outside the active classification tree.

## Active proof libraries

| Library | Responsibility | Entry point |
| --- | --- | --- |
| `SS/` | Bitstrings, Pauli operators, KL detection and shared enumerator identities | [SS.lean](../SS.lean) |
| `QECC/` | Section III: diagonal logical groups, SSLP normal form and physical-order bounds | [QECC.lean](../QECC.lean) |
| `MainTheory/` | General theory, code/projector semantics, paper bridges and classification statements | [MainTheory.lean](../MainTheory.lean) |
| `SixQubit/` | Six-qubit orbit proofs, constructions and finite certificates | [SixQubit.lean](../SixQubit.lean) |
| `Orbit2/` | Imported orbit-2 proof package, retaining its original namespace and provenance | [Orbit2.lean](../Orbit2.lean) |

`MainTheory/Generated/` and `SixQubit/Generated/` contain kernel-checked
certificate transcriptions. Their size reflects finite proof payloads;
[the topic index](proof-modules.md) groups them by family.

`Orbit2/` and `MainTheory/Orbit2*.lean` have different roles: the former is
the imported proof, while the latter connects actual physical encoders and
the SI conventions to that proof. Orbit 3 uses `MainTheory/Orbit3*.lean` for
these analytic connections and `SixQubit/Generated/Orbit3*` for its finite data.

## Dependency flow

The shared `SS` infrastructure feeds the physical code semantics. `QECC`
provides the Section III abstractions; `MainTheory` connects them to concrete
frames and paper-facing statements. Orbit libraries and generated certificates
feed the final classification and full-image theorems. Audit modules inspect
the resulting declaration dependencies and introduce no mathematical assumptions.

The module filenames remain stable. Subject navigation is supplied by
[proof entry points](proof-index.md) and the generated topic index, avoiding
an import-path migration across thousands of certificate files.

## Supporting directories

| Directory | Contents |
| --- | --- |
| `docs/` | Current architecture, proof navigation, status and reproduction instructions |
| `tools/generators/`, `tools/certificates/` | Exact source generators and certificate inputs/checkers |
| `tools/verification/` | Mathematical, source, manifest and manuscript correspondence checks |
| `tools/tests/` | Regression tests for verification and release tooling |
| `results/` | Current machine-readable status, proof inventory and version-bound review records |
| `artifacts/repository-acceptance-20261004/` | Final whole-project acceptance evidence |
| `artifacts/orbit-certification-20261003/` | Historical orbit-2/3 integration evidence |
| `archive/` | Superseded stage sources, documentation and review snapshots |
| `notes/` | Working notes and provenance; dated progress is historical |
| `scratch/`, `alternatives/` | Exploratory material outside the active proof libraries |

The old `__beta5_stage2`, `__beta6_old_cover` and `__beta6_stage` trees are
preserved under `archive/stages/`. The build and source gates inspect only
the five active libraries above. Archive files are not certification targets.

The private manuscript sources remain excluded by `documents/` in
`.gitignore`. Public review records contain hashes, labels, locators and
our review descriptions. Private TeX sources are needed only for manuscript
correspondence checks, not for rebuilding the proof libraries.
