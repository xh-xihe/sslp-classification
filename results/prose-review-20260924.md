# Prose review of the 20260924 manuscripts

Review status: **partial**.

Targeted single-agent semantic review on 2026-09-26 of the 19 new/changed named statements, their immediate context, and the four historical errata. This is not the historical two-agent prose audit; no historical prose review is automatically transferred. Follow-up single-agent semantic review closes the minimum-length corollaries and proof at supplementary lines 5992-6034 using new Lean matrix-level theorems; see results/minimum-length-20260924/review.json. Other review gaps are unchanged. Follow-up arbitrary-subspace review closes the converse paragraph at main lines 1000-1007; see results/colored-subspaces-20260924/review.json. Follow-up common-witness review closes the binary-pivot/Smith/physical-lift claim at main lines 1336-1343; see results/colored-lift-smith-20260924/review.json.

This is a version-bound review record, not a successful kernel run.
No previous-version coverage is transferred. No manuscript text is reproduced.

Generated from `results/prose-review-20260924.json`.

## main.tex:284 — gap

The surrounding scope of eq:quantum-Singleton remains unqualified. The recorded rank-one counterexample applies; author previously requested no manuscript edit.

- `MainTheory.SingletonRankOneCounterexample.violates_unrestricted_singleton`

## supplementary.tex:5340 — tracked

The former existence/open-status mismatch is corrected here and at lines 61, 893 and 5686: only weight-enumerator images of classes 1--4 remain unresolved; physical realizations are acknowledged.

- `MainTheory.OpenOrbitsRealized.openKeys_hasCompletion`

## supplementary.tex:6003 — covered

The minimum-length proof chain is now explicit: literal zero-ancilla projector, full KL preservation, unchanged logical matrix, exact A1 identity and positivity, arbitrary local-unitary diagonalization, quotient order, contradiction and canonical attainment/uniqueness. Exact distance three at six qubits is independently certified by the MacWilliams weight-three obstruction; the unrestricted Singleton display is not used. This review ends at line 6034; the next Clifford paragraph remains a gap.

- `MainTheory.TransversalDiagonalization.exists_diagonal_normal_form`
- `MainTheory.AncillaPadding.compression_snocPauli`
- `MainTheory.AncillaPadding.hasDistance_padFrame`
- `MainTheory.AncillaGatePadding.intertwining_padFrame`
- `MainTheory.AncillaPadding.AWeight_padFrame_one`
- `MainTheory.AncillaPadding.AWeight_padFrame_one_pos`
- `MainTheory.SixQubitExactDistance.exactCode_distance_three`
- `MainTheory.MinimumLengthOrderFive.minimum_length`
- `MainTheory.MinimumLengthOrderFive.canonical_attains`
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`

## supplementary.tex:6036 — gap

The following full-transversal-group/Clifford consequence uses finite rotation-group classification and a common logical-basis conjugacy. Neither follows just from separate diagonal-element order bounds. No accepted Lean correspondence for this new prose consequence has been recorded.


## main.tex:1000 — covered

The converse paragraph at lines 1000-1007 now has an arbitrary-subspace entrance: the same supplied direct sum is the rank-K code, its complete KL equations give the target distance, and the displayed D(a;q) has exact intrinsic order m. No orthonormal frame is required from the caller. This is a bounded review of that paragraph, not the remainder of the subsequent forward proof.

- `MainTheory.PaperGeneralSSLP.general_sslp_converse`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.independent`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.sectorSpace_eq`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.finrank_sum`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.frame_hasDistance`

## main.tex:1336 — covered

The common-construction claim at lines 1336-1343 is now explicit: the representative comes from the solved binary pivot whose actual Smith factor is divisible by its modulus. The same witness also carries the actual eigenvalue-count bound and original projective action. This bounded review does not mark all subsequent normalization/common-mean proof prose complete.

- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`
- `MainTheory.BinaryPivotLift.rationalLift_augmented_eq_binarySolution`
- `MainTheory.BinaryPivotLift.rationalLift_order_dvd_smithLastFactor`

## Remaining review

The remainder of both manuscripts, including 1450 unchanged-statement candidates and the new construction narratives, still requires context-sensitive review. The 20260908 prose audit is background only, not evidence of completed 20260924 prose review.
