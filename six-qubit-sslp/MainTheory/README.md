# General theory and physical proof bridges

The entry point is [MainTheory.lean](../MainTheory.lean). This library contains
general SSLP theory, code/projector semantics, six-qubit classification statements
and connections from actual encoders to finite certificates.

Use [the proof entry-point map](../docs/proof-index.md) for final statements
and [the topic index](../docs/proof-modules.md) for supporting modules.
`Generated/` contains exact finite certificates; it is indexed by family.

The orbit-2 and orbit-3 actual-image endpoints are
[Orbit2FullImage.lean](Orbit2FullImage.lean) and
[Orbit3FullImage.lean](Orbit3FullImage.lean). Their supporting physical bridges
remain here, while the imported orbit-2 proof is in [Orbit2/](../Orbit2/README.md).

[Audit.lean](Audit.lean), [OrbitCertificationFinalAudit.lean](OrbitCertificationFinalAudit.lean)
and [ReviewedDeclarationsAudit.lean](ReviewedDeclarationsAudit.lean) check
transitive declaration dependencies. See [status](../docs/status.md) for the
separate manuscript review and [reproduce](../docs/reproduce.md) for commands.
