# Proof entry points

Start with these final statements, then follow their imports. The full source
inventory is [proof modules by topic](proof-modules.md). Verification scope and
the outstanding manuscript review are recorded in [current status](status.md).

## Main text

| Subject | Entry point |
| --- | --- |
| Section III: diagonal logical groups | [QECC/FirstTheorem.lean](../QECC/FirstTheorem.lean) |
| Section III: SSLP normal form | [QECC/SecondTheorem.lean](../QECC/SecondTheorem.lean) |
| Section III: physical-order bounds | [QECC/ThirdTheorem.lean](../QECC/ThirdTheorem.lean) |
| Frame/projector distance correspondence | [MainTheory/QECCFrameBridge.lean](../MainTheory/QECCFrameBridge.lean) |
| Bounded normal form for the supplied physical gate | [MainTheory/QECCBoundedNormalForm.lean](../MainTheory/QECCBoundedNormalForm.lean) |
| General colored SSLP converse | [MainTheory/PaperGeneralSSLPConverse.lean](../MainTheory/PaperGeneralSSLPConverse.lean) |
| Physical colored-lift and Smith bound | [MainTheory/PaperColoredFiniteLift.lean](../MainTheory/PaperColoredFiniteLift.lean) |
| Common-mean replacement | [MainTheory/CommonMeanReplacement.lean](../MainTheory/CommonMeanReplacement.lean) |
| Positive affine moment geometry | [MainTheory/PositiveAffineMoments.lean](../MainTheory/PositiveAffineMoments.lean) |
| Common Clifford basis for bounded projective subgroups | [MainTheory/BoundedProjectiveCliffordGroup.lean](../MainTheory/BoundedProjectiveCliffordGroup.lean) |
| Minimum length for the non-Clifford example | [MainTheory/SmallNonCliffordMinimum.lean](../MainTheory/SmallNonCliffordMinimum.lean) |
| Seven-qubit example and exact minimum physical order | [MainTheory/SevenQubitMinimumOrder.lean](../MainTheory/SevenQubitMinimumOrder.lean) |
| Order-five minimum length and uniqueness | [MainTheory/MinimumLengthOrderFive.lean](../MainTheory/MinimumLengthOrderFive.lean) |

## Supplementary material

| SI role | Entry point |
| --- | --- |
| Enumeration and directory | [MainTheory/PaperReductionChain.lean](../MainTheory/PaperReductionChain.lean), [MainTheory/DirectoryOrbitStatus.lean](../MainTheory/DirectoryOrbitStatus.lean) |
| Actual-projector enumerator transport and existing images | [MainTheory/DirectoryEnumeratorImages.lean](../MainTheory/DirectoryEnumeratorImages.lean) |
| Orbit 2: complete actual-encoder image | [MainTheory/Orbit2FullImage.lean](../MainTheory/Orbit2FullImage.lean) |
| Orbit 2: imported proof and exact attainment | [Orbit2/Complete.lean](../Orbit2/Complete.lean) |
| Orbit 2: physical quartic spectral tables | [SixQubit/Generated/Orbit2PhysicalSpectra.lean](../SixQubit/Generated/Orbit2PhysicalSpectra.lean) |
| Orbit 3: complete actual-encoder image | [MainTheory/Orbit3FullImage.lean](../MainTheory/Orbit3FullImage.lean) |
| Orbit 3: scalar constraints | [MainTheory/Orbit3ScalarEqualities.lean](../MainTheory/Orbit3ScalarEqualities.lean) |
| Orbit 3: sextic certificate identity | [SixQubit/Generated/Orbit3SexticIdentity.lean](../SixQubit/Generated/Orbit3SexticIdentity.lean) |
| Orbit 45: printed derivation and attainment | [MainTheory/Orbit45PrintedConsequences.lean](../MainTheory/Orbit45PrintedConsequences.lean), [MainTheory/Orbit45PrintedAttainment.lean](../MainTheory/Orbit45PrintedAttainment.lean) |
| No-go proofs and constructions | [SixQubit.lean](../SixQubit.lean), [SixQubit/Audit.lean](../SixQubit/Audit.lean) |

The two full-image endpoints are
`MainTheory.Orbit2FullImage.directory_image` and
`MainTheory.Orbit3FullImage.directory_image`. Both prove the full interval,
including converse and attainment, for actual full-KL encoders.

## Audits and manuscript correspondence

- [MainTheory/Audit.lean](../MainTheory/Audit.lean): main-theory audit roots.
- [QECC/Audit.lean](../QECC/Audit.lean): Section III audit roots.
- [MainTheory/OrbitCertificationFinalAudit.lean](../MainTheory/OrbitCertificationFinalAudit.lean): physical certificate and completed bridge roots.
- [MainTheory/ReviewedDeclarationsAudit.lean](../MainTheory/ReviewedDeclarationsAudit.lean): declarations cited by the pre-reorganization review, retained for kernel auditing without transferring manuscript coverage.
- [Current named-results map](../results/named-results-20261003.md): locators and review status for the current private sources.
- [Historical correspondence candidates](../results/correspondence-candidates-20261004.json): prior reviewed declarations matched by label or unchanged statement hash, awaiting context review.

A compiled module or a candidate mapping alone does not certify a manuscript
assertion. Coverage requires reviewing its full hypotheses and context against
the Lean statement. The SI's unresolved orbit-1/4 image questions remain open.
