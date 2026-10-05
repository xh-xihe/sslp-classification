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
| SI Section 10: literal split-qubit matrices | [MainTheory/PrimitiveSplitDisplays.lean](../MainTheory/PrimitiveSplitDisplays.lean) |
| SI Section 10: actual cat encoder and full KL conditions | [MainTheory/PrimitiveOrderTwoCatEncoder.lean](../MainTheory/PrimitiveOrderTwoCatEncoder.lean), [MainTheory/PrimitiveOrderTwoCatKL.lean](../MainTheory/PrimitiveOrderTwoCatKL.lean) |
| SI Section 10: physical cat Pauli coefficients and A1/A2 | [MainTheory/PrimitiveOrderTwoCatEnumerator.lean](../MainTheory/PrimitiveOrderTwoCatEnumerator.lean) |
| SI Section 10: cat logical actions and spin flip | [MainTheory/PrimitiveOrderTwoCatLogicals.lean](../MainTheory/PrimitiveOrderTwoCatLogicals.lean), [MainTheory/PrimitiveOrderTwoCatSpinFlip.lean](../MainTheory/PrimitiveOrderTwoCatSpinFlip.lean) |
| Orbit 2: complete actual-encoder image | [MainTheory/Orbit2FullImage.lean](../MainTheory/Orbit2FullImage.lean) |
| Orbit 2: imported proof and exact attainment | [Orbit2/Complete.lean](../Orbit2/Complete.lean) |
| Orbit 2: physical quartic spectral tables | [SixQubit/Generated/Orbit2PhysicalSpectra.lean](../SixQubit/Generated/Orbit2PhysicalSpectra.lean) |
| Orbit 3: complete actual-encoder image | [MainTheory/Orbit3FullImage.lean](../MainTheory/Orbit3FullImage.lean) |
| Orbit 3: scalar constraints | [MainTheory/Orbit3ScalarEqualities.lean](../MainTheory/Orbit3ScalarEqualities.lean) |
| Orbit 3: sextic certificate identity | [SixQubit/Generated/Orbit3SexticIdentity.lean](../SixQubit/Generated/Orbit3SexticIdentity.lean) |
| Orbit 3: printed common-norm homogeneous target | [MainTheory/Orbit3PrintedHomogeneousTarget.lean](../MainTheory/Orbit3PrintedHomogeneousTarget.lean) |
| Orbit 45: printed derivation and attainment | [MainTheory/Orbit45PrintedConsequences.lean](../MainTheory/Orbit45PrintedConsequences.lean), [MainTheory/Orbit45PrintedAttainment.lean](../MainTheory/Orbit45PrintedAttainment.lean) |
| Orbit 45: triangle, matched-probability and physical coefficient algebra | [MainTheory/Orbit45PrintedAlgebra.lean](../MainTheory/Orbit45PrintedAlgebra.lean) |
| Orbit 33: literal rational reflection and inverse | [MainTheory/Orbit33PrintedReflection.lean](../MainTheory/Orbit33PrintedReflection.lean) |
| No-go proofs and constructions | [SixQubit.lean](../SixQubit.lean), [SixQubit/Audit.lean](../SixQubit/Audit.lean) |
| Orbit 31: exact literal support geometry and residual triangles | [MainTheory/Orbit31RelativeInterior.lean](../MainTheory/Orbit31RelativeInterior.lean), [MainTheory/Orbit31PrintedMinor.lean](../MainTheory/Orbit31PrintedMinor.lean), [MainTheory/Orbit31ResidualTriangles.lean](../MainTheory/Orbit31ResidualTriangles.lean) |
| Orbit 32: complete real moment form and literal exclusion | [MainTheory/Orbit32PrintedMomentNormal.lean](../MainTheory/Orbit32PrintedMomentNormal.lean), [MainTheory/Orbit32PrintedMinor.lean](../MainTheory/Orbit32PrintedMinor.lean), [MainTheory/Orbit32PrintedLocalAlgebra.lean](../MainTheory/Orbit32PrintedLocalAlgebra.lean) |
| Orbit 33: normalized physical block and projector argument | [MainTheory/Orbit33NormalizedPairs.lean](../MainTheory/Orbit33NormalizedPairs.lean), [MainTheory/Orbit33PhysicalReflection.lean](../MainTheory/Orbit33PhysicalReflection.lean), [MainTheory/Orbit33ProjectorArgument.lean](../MainTheory/Orbit33ProjectorArgument.lean) |
| Order two: moment forms, ranks, half-angle exclusions and shell projectors | [MainTheory/OrderTwoPrintedMoments.lean](../MainTheory/OrderTwoPrintedMoments.lean), [MainTheory/OrderTwoPrintedRanks.lean](../MainTheory/OrderTwoPrintedRanks.lean), [MainTheory/OrderTwoPrintedWalsh.lean](../MainTheory/OrderTwoPrintedWalsh.lean), [MainTheory/OrderTwoShellProjectors.lean](../MainTheory/OrderTwoShellProjectors.lean) |
| Order three: moment forms, signed rank minors and physical cross rows | [MainTheory/OrderThreePrintedMoments.lean](../MainTheory/OrderThreePrintedMoments.lean), [MainTheory/OrderThreePrintedRanks.lean](../MainTheory/OrderThreePrintedRanks.lean), [MainTheory/OrderThreePrintedCrossRows.lean](../MainTheory/OrderThreePrintedCrossRows.lean) |
| Orbits 49, 50 and 51: full literal physical exclusions | [MainTheory/Orbit49PhysicalCompletion.lean](../MainTheory/Orbit49PhysicalCompletion.lean), [MainTheory/Orbit50PhysicalTriangle.lean](../MainTheory/Orbit50PhysicalTriangle.lean), [MainTheory/Orbit51PhysicalCompletion.lean](../MainTheory/Orbit51PhysicalCompletion.lean) |
| Arbitrary complex-isometry physical split construction | [MainTheory/ArbitrarySplitPerfectCode.lean](../MainTheory/ArbitrarySplitPerfectCode.lean), [MainTheory/ArbitrarySplitSixQubit.lean](../MainTheory/ArbitrarySplitSixQubit.lean) |
| Standard five-qubit code: joint projector space and literal syndromes | [MainTheory/StandardFiveJointSpace.lean](../MainTheory/StandardFiveJointSpace.lean), [MainTheory/StandardFiveSyndromeDisplays.lean](../MainTheory/StandardFiveSyndromeDisplays.lean) |
| Orbit 29: actual full moment polytope and all simplex faces | [MainTheory/Orbit29MomentPolytope.lean](../MainTheory/Orbit29MomentPolytope.lean), [MainTheory/Orbit29SimplexRelativeInterior.lean](../MainTheory/Orbit29SimplexRelativeInterior.lean), [MainTheory/Orbit29SimplexDimensions.lean](../MainTheory/Orbit29SimplexDimensions.lean) |
| Orbit 29: actual ratios, physical gauge and eta equations | [MainTheory/Orbit29PhysicalRatios.lean](../MainTheory/Orbit29PhysicalRatios.lean), [MainTheory/Orbit29PhysicalPairGauge.lean](../MainTheory/Orbit29PhysicalPairGauge.lean), [MainTheory/Orbit29PrintedEta.lean](../MainTheory/Orbit29PrintedEta.lean) |
| Orbit 45: physical canonical form and complete printed enumerators | [MainTheory/Orbit45PhysicalCanonicalForm.lean](../MainTheory/Orbit45PhysicalCanonicalForm.lean), [MainTheory/Orbit45PrintedEnumerator.lean](../MainTheory/Orbit45PrintedEnumerator.lean) |
| Orbit 30: actual physical moment rank and literal probabilities | [MainTheory/Orbit30MomentRank.lean](../MainTheory/Orbit30MomentRank.lean), [MainTheory/Orbit30PrintedMoments.lean](../MainTheory/Orbit30PrintedMoments.lean), [MainTheory/Orbit30ProbabilityLabels.lean](../MainTheory/Orbit30ProbabilityLabels.lean) |
| Orbit 30: actual Pauli rows, phases and support graph | [MainTheory/Orbit30PhysicalRows.lean](../MainTheory/Orbit30PhysicalRows.lean), [MainTheory/Orbit30PhysicalPhases.lean](../MainTheory/Orbit30PhysicalPhases.lean), [MainTheory/Orbit30PhysicalGraph.lean](../MainTheory/Orbit30PhysicalGraph.lean), [MainTheory/Orbit30TwoPointDisplays.lean](../MainTheory/Orbit30TwoPointDisplays.lean), [MainTheory/Orbit30BoundaryDisplays.lean](../MainTheory/Orbit30BoundaryDisplays.lean) |
| Orbit 30: hafnians, all ten proper graphs and relabeling | [MainTheory/Orbit30PhysicalHafnians.lean](../MainTheory/Orbit30PhysicalHafnians.lean), [MainTheory/Orbit30GraphClassification.lean](../MainTheory/Orbit30GraphClassification.lean), [MainTheory/Orbit30GraphTypes.lean](../MainTheory/Orbit30GraphTypes.lean), [MainTheory/Orbit30GraphRelabel.lean](../MainTheory/Orbit30GraphRelabel.lean), [MainTheory/Orbit30PhysicalProperSupport.lean](../MainTheory/Orbit30PhysicalProperSupport.lean) |
| Orbit 30: nonzero vertex scaling and literal determinant minus 32 | [MainTheory/Orbit30VertexScaling.lean](../MainTheory/Orbit30VertexScaling.lean), [MainTheory/Orbit30NormalizedDeterminant.lean](../MainTheory/Orbit30NormalizedDeterminant.lean), [MainTheory/Orbit30FullSupport.lean](../MainTheory/Orbit30FullSupport.lean), [MainTheory/Orbit30PhysicalFullSupport.lean](../MainTheory/Orbit30PhysicalFullSupport.lean) |

The two full-image endpoints are
`MainTheory.Orbit2FullImage.directory_image` and
`MainTheory.Orbit3FullImage.directory_image`. Both prove the full interval,
including converse and attainment, for actual full-KL encoders.

## Audits and manuscript correspondence

- [MainTheory/Audit.lean](../MainTheory/Audit.lean): main-theory audit roots.
- [QECC/Audit.lean](../QECC/Audit.lean): Section III audit roots.
- [MainTheory/OrbitCertificationFinalAudit.lean](../MainTheory/OrbitCertificationFinalAudit.lean): physical certificate and completed bridge roots.
- [MainTheory/ReviewedDeclarationsAudit.lean](../MainTheory/ReviewedDeclarationsAudit.lean): declarations cited by the pre-reorganization review, retained for kernel auditing without transferring manuscript coverage.
- [MainTheory/ManuscriptCertificationAudit20261005.lean](../MainTheory/ManuscriptCertificationAudit20261005.lean): current candidate and physical-formula audit roots.
- [Current named-results map](../results/named-results-20261003.md): locators and review status for the current private sources.
- [Current correspondence candidates](../results/correspondence-candidates-20261005.json): prior declarations matched to the authoritative source snapshot; coverage still requires current context and type review.

A compiled module or a candidate mapping alone does not certify a manuscript
assertion. Coverage requires reviewing its full hypotheses and context against
the Lean statement. The SI's unresolved orbit-1/4 image questions remain open.
