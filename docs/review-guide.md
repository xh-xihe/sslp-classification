# Reviewer guide

[Home](../README.md) · [Documentation](README.md) · [Proof index](proof-index.md) · [Status](status.md)

The main paper and supplementary information have two separate verification
layers: mathematical proofs checked by Lean, and a version-specific review of
the manuscript statements against those proofs. This guide follows both.

## Find the statement

Start with the [proof index](proof-index.md). It maps general theory,
constructions, orbit exclusions, and enumerator images to readable entry
modules. For example, the complete orbit-2 and orbit-3 actual-encoder images
are in [Orbit2FullImage](../MainTheory/Orbit2FullImage.lean) and
[Orbit3FullImage](../MainTheory/Orbit3FullImage.lean).

Read the Lean theorem's hypotheses and conclusion. Supporting imports,
generated certificates, and audit modules establish its dependencies; they
do not by themselves identify which manuscript sentence it proves.

For manuscript locators, consult the
[named-results map](../results/named-results-20261003.md) and
[claim ledger](../results/paper-claims-20261003.json). The
[correspondence guide](manuscript-correspondence.md) explains the reviewed
scope and paragraph-context records.

## Follow the evidence

| Question | Record to inspect |
| --- | --- |
| Which manuscript bytes were reviewed? | [Run record](../artifacts/manuscript-certification-20261005/run.json) and [source hashes](../results/repository-status.json) |
| Did all active Lean modules build? | [16,227-module acceptance](../artifacts/manuscript-certification-20261005/proof-acceptance-16227.json) |
| What axioms do the audited declarations depend on? | [9,375-root transitive audit](../artifacts/manuscript-certification-20261005/axioms-9375.json) |
| Are the published sources the accepted sources? | [Publication binding](../artifacts/manuscript-certification-20261005/publication-binding-16227.json) |
| What remains unresolved? | [Current status](status.md), [remaining obligations](../artifacts/manuscript-certification-20261005/remaining-obligations.json), and [held errata](../notes/main-errata-hold-20261003.md) |
| Did moving the project to the root preserve its files? | [Migration verification](../artifacts/repository-root-migration-20261006/verification.json) and [complete file ledger](../artifacts/repository-root-migration-20261006/migration-manifest.json) |

The correspondence records are bound to **`20261003`**, including SI edits
through 2026-10-05. The SI has 1,622 covered mathematical assertions and three
scope remarks. Five held main-text issues prevent complete certification of
the combined manuscript. Orbit-1/4 full enumerator images remain open. Later
manuscript versions, including `20261006`, need separate correspondence checks.

## The trust boundary

The intended mathematical trust boundary is the **Lean kernel**. The selected
audit roots have transitive footprints containing only `propext`,
`Classical.choice`, and `Quot.sound`.

Python generators and numerical explorations help construct and independently
check finite data. Mathematical acceptance comes from the committed Lean
statements and proofs, their successful build, and the axiom audit. Regenerating
data and checking hashes supply provenance checks alongside kernel verification.

Private manuscript TeX sources are excluded. Readers can rebuild the proof
package and inspect the public review records; repeating the byte-bound
manuscript correspondence checks requires the matching private sources.

## Reproduce a check

Follow [setup](reproduce.md#setup), then choose
[focused orbit checks](reproduce.md#focused-orbit-checks), the
[whole proof package](reproduce.md#whole-proof-package), or
[exact rational certificate reconstruction](reproduce.md#finite-certificate-data).
The reproduction guide distinguishes each command's scope and outputs.

For a suspected mismatch, open a
[manuscript correspondence issue](https://github.com/xh-xihe/sslp-classification/issues/new?template=correspondence.yml)
with the repository commit, manuscript version and locator, relevant Lean
declaration, and differing hypotheses or conclusion.
