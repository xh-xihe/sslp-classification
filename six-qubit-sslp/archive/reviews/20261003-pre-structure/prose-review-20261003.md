# Prose review of the 20261003 manuscripts

Review status: **partial**.

Fresh scoped review of the corrected SI and new library bridges on 2026-10-03. This does not replace the historical full Section III correspondence review or claim a complete review of all prose. Main text is frozen at the author instruction. Exact matrix/coordinate certificates and encoder semantics are recorded separately. Updated on 2026-10-04 only for completed actual orbit images, physical spectral tables, the seven-qubit example and two generic geometric bridges. Unreviewed claims and author-held main errata remain outside a completion claim.

This is a version-bound review record, not a successful kernel run.
No previous-version coverage is transferred. No manuscript text is reproduced.

Generated from `results/prose-review-20261003.json`.

## supplementary.tex:2839 — covered

The corrected physical gate acts by the stated logical matrix on the entire theta family. Its logical order is exactly three. This record covers the corrected action and order, not the subsequent product-basis diagonalization correspondence.

- `MainTheory.CitedCorrectedFamily.action`
- `MainTheory.CitedCorrectedLogicalGate.logical_matrix`
- `MainTheory.CitedCorrectedLogicalGate.logical_cube`
- `MainTheory.CitedCorrectedLogicalGate.logical_not_scalar`
- `MainTheory.CitedCorrectedLogicalGate.logical_square_not_scalar`

## supplementary.tex:3551 — covered

The stated rightmost-qubit-one convention matches the existing literal coefficient witness and its complete distance-three proof.

- `MainTheory.Orbit9LiteralWitness.literal_code`

## supplementary.tex:7556 — covered

Normalized images on literal fibers equal the images over their entire physical cube orbit; every coordinate is preserved. Instantiation at each of the 66 generated representatives is still separate.

- `MainTheory.EnumeratorOrbitTransport.WImage_eq_orbitImage`
- `MainTheory.EnumeratorOrbitTransport.completionImage_actFibers`

## supplementary.tex:5419 — covered

Actual full-KL complex encoders map into the integrated root orbit-two proof. Its full normalized FI image, both containment and attainment, is kernel checked. All 111 physical quartic blocks are identified and have the seven stated SI spectral patterns.

- `MainTheory.Orbit2FullImage.actual_A3_zero`
- `MainTheory.Orbit2FullImage.actual_enumerator`
- `MainTheory.Orbit2FullImage.directory_image`
- `SixQubit.Generated.Orbit2PhysicalSpectra.physical_characteristic_polynomials`

## supplementary.tex:6303 — covered

Actual full-KL complex encoders satisfy every KL, spin and Hadamard primitive row. All 120 actual target Paulis yield the 269-coordinate sextic target; its vanishing gives the actual A3=0 and full FI interval image, with attainment.

- `MainTheory.Orbit3FullImage.all_primitive_rows_zero`
- `MainTheory.Orbit3FullImage.target_coordinates`
- `MainTheory.Orbit3FullImage.target_zero`
- `MainTheory.Orbit3FullImage.actual_enumerator`
- `MainTheory.Orbit3FullImage.directory_image`

## main.tex:277 — gap

Five main-text issues remain deliberately unchanged pending author discussion; see notes/main-errata-hold-20261003.md.


## supplementary.tex:1 — covered

The 51 empty images and 11 exact nonempty images are transported with actual state norms, all KL conditions and the complete A enumerator. This covers the earlier 62 images, not the newly added orbit-2/3 converses.

- `MainTheory.DirectoryEnumeratorImages.empty_of_noGo`
- `MainTheory.DirectoryEnumeratorImages.orbit7_image`
- `MainTheory.DirectoryEnumeratorImages.orbit8_image`
- `MainTheory.DirectoryEnumeratorImages.orbit9_image`
- `MainTheory.DirectoryEnumeratorImages.orbit10_image`
- `MainTheory.DirectoryEnumeratorImages.orbit11_image`
- `MainTheory.DirectoryEnumeratorImages.orbit16_image`
- `MainTheory.DirectoryEnumeratorImages.orbit21_image`
- `MainTheory.DirectoryEnumeratorImages.orbit22_image`
- `MainTheory.DirectoryEnumeratorImages.orbit23_image`
- `MainTheory.DirectoryEnumeratorImages.orbit36_image`
- `MainTheory.DirectoryEnumeratorImages.orbit45_image`

## main.tex:1069 — covered

Uses the same bounded representative for colors, canonical transport and sector moments. The sharper general beta index remains the source-sector count of the support system; equality with the new representative sector count is not asserted here.

- `MainTheory.QECCFrameBridge.hasDistance_iff`
- `MainTheory.QECCBoundedNormalForm.bounded_full_normal_form`
- `MainTheory.QECCBoundedNormalForm.distanceThree_for_supplied_gate`

## main.tex:1 — covered

The new actual seven-qubit complex code has logical group ZMod 6, the stated actual eigenvalues and irrational infinite-order representatives. Its exact minimum physical order for the target class is twelve.

- `MainTheory.SevenQubitLogicalAction.family_eigenvalues`
- `MainTheory.SevenQubitRationalFamily.family_infinite_order`
- `MainTheory.SevenQubitMinimumOrder.minimum_physical_order`
- `MainTheory.SevenQubitLogicalCharacter.projectiveEquiv`

## main.tex:1 — covered

The common-mean argument and its exact physical exponential scalar hold for arbitrary finite supports, distributions and supported subspaces, without rational-probability or KL assumptions.

- `MainTheory.CommonMeanReplacement.support_value`
- `MainTheory.CommonMeanReplacement.replacement_on_direct_sum`

## main.tex:1 — covered

The positive-square-moment lemma is now proved for arbitrary finite real point sets of different cardinalities, including its affine annihilator argument; it is not restricted to computational-basis supports.

- `MainTheory.PositiveAffineMoments.affineSpan_eq`

## Remaining review

Complete the source-wide prose review.
