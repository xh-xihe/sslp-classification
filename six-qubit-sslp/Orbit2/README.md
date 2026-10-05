# Imported orbit-2 proof package

This directory retains the reviewed upstream `Orbit2` namespace. The source
revision is `f84bbd39451a3e0648fd1bd4ccf0ad38f558245a`, recorded in
[the source review](../artifacts/orbit-certification-20261003/colleague-orbit2-source-review.json)
and [the integration ledger](../artifacts/orbit-certification-20261003/orbit2-integration-sources.json).

[Orbit2.lean](../Orbit2.lean) imports the package and lists audit roots.
[Complete.lean](Complete.lean) supplies its complete encoder theorem.
The shared-definition adapters are `PhysicalMacWilliams.lean`,
`PhysicalShadow.lean` and `PhysicalB.lean`; their integration changes are
recorded in the ledger. Other recorded adjustments suppress style linters.

The main library's [Orbit2FullImage.lean](../MainTheory/Orbit2FullImage.lean)
connects the actual directory encoders and enumerator conventions to this
package. That connection and the imported proof are compiled and audited together.

No upstream checkout is needed to build the published sources. The historical
import tool accepts `--upstream-dir` if the authors repeat the provenance step.
See [reproduction](../docs/reproduce.md) and [architecture](../docs/architecture.md).
