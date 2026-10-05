# Prose review of the 20261003 manuscripts

Review status: **partial**.

Explicit review of the frozen 20261003 main source and current SI. Reviewed prose blocks bind their exact current line ranges and kernel-inspected physical theorem types. All other running text still requires review. Five author-held main issues remain gaps; the main source is unchanged. No source-wide coverage is inherited.

This is a version-bound review record, not a successful kernel run.
No previous-version coverage is transferred. No manuscript text is reproduced.

Generated from `results/prose-review-20261003.json`.

## main.tex:172 — gap

Author-held frozen main issue: the introductory diagonal-group finiteness claim needs the fixed-product-basis and single-site detection hypotheses used by the actual theorem.


## main.tex:269 — gap

Author-held frozen main issue: probability moment rows implement diagonal Z detection; full X/Y KL conditions also involve complex phases.


## main.tex:274 — gap

Author-held frozen main issue: the unrestricted Singleton statement includes rank one and is false there. The repository carries both the corrected rank-at-least-two theorem and a kernel counterexample. A proof of a corrected statement cannot certify this frozen wording.


## main.tex:684 — gap

Author-held frozen main issue: rational homogeneous replacement preserves the specified image/kernel information; this must not be read as equality of the entire homogeneous component.


## main.tex:1825 — gap

Author-held frozen main issue: physical-order minimization in this sentence has a broader representative scope than the reduced diagonal definition used by its corresponding result.


## supplementary.tex:4369 — covered

The literal cat coefficients give two orthonormal actual physical columns under the printed real quadratic parameter constraint.

- `MainTheory.PrimitiveOrderTwoCatEncoder.encoder_apply`
- `MainTheory.PrimitiveOrderTwoCatEncoder.encoder_isometry`

## supplementary.tex:4373 — covered

The actual five-cat embedding kills all nonidentity single-site Paulis. The only nonzero two-site types are ZZ and equal XX/YY; constructive support classification exhausts all weight-at-most-two labels.

- `MainTheory.PrimitiveOrderTwoCatCompression.cats`
- `MainTheory.PrimitiveOrderTwoCatCompression.single_zero`
- `MainTheory.PrimitiveOrderTwoCatCompression.ZZ`
- `MainTheory.PrimitiveOrderTwoCatCompression.XX_YY`
- `MainTheory.PrimitiveOrderTwoCatCompression.mixed_zero`
- `MainTheory.PrimitiveOrderTwoCatKL.small_label`

## supplementary.tex:4406 — covered

Tail-only, first-site-only and first/tail Pauli factors exhaust the actual weight-at-most-two matrix compressions. The constructive proof retains all real normalized parameters and uses no nonzero individual amplitude premise or division by an amplitude.

- `MainTheory.PrimitiveOrderTwoCatKL.real_tail_KL`
- `MainTheory.PrimitiveOrderTwoCatKL.first_pauli_KL`
- `MainTheory.PrimitiveOrderTwoCatKL.one_tail_zero`
- `MainTheory.PrimitiveOrderTwoCatKL.weight_split`
- `MainTheory.PrimitiveOrderTwoCatKL.full_KL`

## supplementary.tex:4440 — covered

The actual six-qubit code projector is orthogonal to its conjugate six-Y spin flip and their product has zero trace. The subsequent enumerator conclusion is outside this reviewed prose block.

- `MainTheory.PrimitiveOrderTwoCatSpinFlip.overlap_zero`
- `MainTheory.PrimitiveOrderTwoCatSpinFlip.projectors_orthogonal`
- `MainTheory.PrimitiveOrderTwoCatSpinFlip.spin_trace_zero`

## supplementary.tex:5607 — covered

The target identity retains arbitrary raw amplitudes and only divides by the positive common column norm. No amplitude or Schmidt coefficient is required to be nonzero.

- `MainTheory.Orbit3PrintedHomogeneousTarget.raw_expectation`
- `MainTheory.Orbit3PrintedHomogeneousTarget.homogeneous_target`

## supplementary.tex:5594 — covered

The actual six-Y bilinear is symmetric. Its same-parity terms vanish under the actual odd orbit-three involution, including zero amplitudes. The preceding shadow-saturation sentence is outside this narrowly reviewed block.

- `MainTheory.Orbit3PrintedSpinTrace.pairing_symmetric`
- `MainTheory.Orbit3PrintedSpinTrace.pairing_diagonal_zero`
- `MainTheory.Orbit3PrintedSpinTrace.raw_parity`
- `MainTheory.Orbit3PrintedSpinTrace.orbit3_odd`

## supplementary.tex:16129 — covered

The three final table stages still count the actual primitive angle records. Distinct records mapped to the same pair remain distinct in these actual survivor sets.

- `MainTheory.SupplementarySectorCountBase.recordCount`
- `MainTheory.Generated.SupplementarySectorWitnesses.coarseRecords_complete`
- `MainTheory.Generated.SupplementarySectorWitnesses.feasibleRecords_complete`
- `MainTheory.Generated.SupplementarySectorWitnesses.compatibleRecords_complete`
- `MainTheory.SupplementarySectorCounts.angle_table`

## supplementary.tex:16164 — covered

The second table counts distinct actual full labelled fibre-pair payloads after hashing, and inequivalent actual directory keys in its final column. Both q and m are retained throughout.

- `MainTheory.SupplementarySectorCountBase.pairCount`
- `MainTheory.Generated.FinitePairDistinctness.pairAtId_injective`
- `MainTheory.Generated.FiniteOrbitCertificate.directory_valid`
- `MainTheory.SupplementarySectorCounts.pair_table`

## supplementary.tex:10743 — covered

The literal two-normalization, five-first-moment and ten-second-moment matrix is checked against the actual bottom/top tail-bit coordinates. Its rational kernel is linearly equivalent to two free parameters; rank-nullity therefore proves rank fourteen. An independent affine equivalence proves that every rational solution, and only those solutions, has the printed two-parameter form. Physical real probabilities are connected separately by physical_probabilities; they are not assumed to be rational.

- `MainTheory.Orbit26PrintedMoments.actual`
- `MainTheory.Orbit26PrintedMoments.rows`
- `MainTheory.Orbit26PrintedMoments.actual_rows`
- `MainTheory.Orbit26PrintedMoments.M`
- `MainTheory.Orbit26PrintedMoments.kernel_iff`
- `MainTheory.Orbit26PrintedMoments.affine_iff`
- `MainTheory.Orbit26PrintedMoments.kernel_dimension`
- `MainTheory.Orbit26PrintedMoments.rank_fourteen`

## Remaining review

Complete all other current prose and mathematical correspondence. Preserve the five author-held frozen main issues. Kernel build and axiom acceptance are recorded separately.
