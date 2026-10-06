# SSLP Classification

*Finite Classification of Transversal Diagonal Gates Beyond Stabilizer Codes*

This repository contains the Lean proofs, exact certificate data and
verification tools accompanying the main paper and supplementary information.
The active project is in [`six-qubit-sslp/`](six-qubit-sslp/README.md) on `main`.

## Start here

| Entry | Contents |
| --- | --- |
| [Verification status](six-qubit-sslp/docs/status.md) | Accepted proof snapshots, manuscript correspondence and unresolved items |
| [Proof entry points](six-qubit-sslp/docs/proof-index.md) | Main-text theory and SI statements mapped to Lean declarations |
| [Proof modules](six-qubit-sslp/docs/proof-modules.md) | Active libraries and generated certificate families |
| [Reproduction guide](six-qubit-sslp/docs/reproduce.md) | Pinned environment, build commands and verification gates |
| [Architecture](six-qubit-sslp/docs/architecture.md) | Library responsibilities and dependency flow |

The active libraries are `SS`, `QECC`, `MainTheory`, `SixQubit` and `Orbit2`.
They include the general SSLP theory, six-qubit orbit classifications and
complete actual-encoder image proofs for orbits 2 and 3.

## Verification scope

The proof trust target is the Lean kernel with only `propext`,
`Classical.choice` and `Quot.sound`. Source/build/axiom acceptance and
manuscript correspondence are recorded separately in the project status.
The recorded manuscript acceptance concerns the `20261003` sources;
subsequent manuscript changes require a version-specific correspondence review.
Open statements and author-held main-text issues remain identified there.
Private manuscript sources are excluded from the repository.

## Reproduce

From the repository root:

```console
cd six-qubit-sslp
lake exe cache get
python tools/build_lean.py
python tools/verify.py --paper-version 20261003 --only sources generated audit-names axioms
python tools/repository_index.py --check
```

See the [reproduction guide](six-qubit-sslp/docs/reproduce.md) for the meaning
of each gate, cache handling and manuscript-source requirements.

## Historical work

The earlier independent dyadic Bell ladder is preserved in a fixed
[archive tag](https://github.com/xh-xihe/sslp-classification/tree/archive/dyadic-ladder-20261006).
See [the historical archive entry](HISTORY.md) to retrieve its proofs and data.
