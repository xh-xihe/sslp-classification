# Contributing

[Home](README.md) · [Architecture](docs/architecture.md) · [Reproduction](docs/reproduce.md)

Changes should make a mathematical statement, its proof, or its reproducibility
easier to inspect. Use a focused pull request and identify the affected theorem,
certificate family, documentation page, or verification tool.

## Set up

Follow [the setup guide](docs/reproduce.md#setup). Keep `lean-toolchain` and
`lake-manifest.json` pinned unless the pull request explicitly proposes a
toolchain migration. Build an affected module with its dependencies using:

```console
python tools/build_lean.py --module MainTheory.Orbit2FullImage
```

Replace the example module with the module you changed. Stable namespaces and
import paths connect thousands of certificate shards and manuscript mappings.
For library responsibilities, consult [architecture](docs/architecture.md).

## Match the checks to the change

| Change | Validation to report |
| --- | --- |
| Navigation or presentation | `python tools/check_navigation.py` |
| Lean statements or proofs | Affected dependency build, source checks, and the relevant transitive axiom audit; whole proof acceptance for integration |
| Generated certificate | Exact regeneration, manifest and build-order checks, then the Lean build and audit |
| Verification tooling | Relevant regression tests, including negative controls when acceptance behavior changes |
| Manuscript correspondence | Exact manuscript version/hash, locator, declaration type, hypotheses, and full context review |

If active Lean sources change, regenerate the catalog with
`python tools/repository_index.py`, then check it with `--check`.
Do not edit [the generated module index](docs/proof-modules.md) by hand.
The [reproduction guide](docs/reproduce.md) supplies the detailed commands.

## Preserve proof and review provenance

The active proof libraries target kernel checking with only `propext`,
`Classical.choice`, and `Quot.sound`. Proof placeholders, custom axioms, and
compiler-backed proof escapes are rejected by the source gate.

Keep dated acceptance records and archived snapshots intact. Record new
outcomes separately, identify the exact sources checked, and distinguish kernel
acceptance from manuscript coverage. A successful build does not certify a
changed manuscript sentence automatically.

Private manuscript sources stay outside Git. Use their public locators and
hash-bound review records to discuss correspondence. The five held main-text
issues remain subject to author decisions documented in [status](docs/status.md).

## Report a problem

Use [a reproduction issue](https://github.com/xh-xihe/sslp-classification/issues/new?template=reproduction.yml)
for a failing command, with the commit, platform, command, and relevant output.
Use [a correspondence issue](https://github.com/xh-xihe/sslp-classification/issues/new?template=correspondence.yml)
for a mathematical mismatch. The pull-request template asks for the problem,
resulting behavior, validation, and any effect on certification scope.
