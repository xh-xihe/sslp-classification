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

## Remaining review

Complete all other current prose/context review and the remaining display/named-result obligations. Preserve the five frozen main issues until the author changes their disposition.
