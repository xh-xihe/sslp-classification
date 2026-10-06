# Current verification status

Canonical branch: **`main`**. Package: repository root.
Private manuscript version: `20261003`, including the SI edits through
2026-10-05. The current SI mathematical correspondence review is complete.
The frozen main remains partial because of five author-held issues. Its [run record](../artifacts/manuscript-certification-20261005/run.json)
binds the frozen main text and current supplementary source hashes.

The 20261004 whole-project proof acceptance was **PASS**: 15,923 active Lean modules
(one newly compiled audit module, 15,922 content-validated cached modules),
2,764 transitive axiom roots and 10,085 manifest-bound generated sources.
The publication snapshot contains every active proof source, bound to that
successful build with LF normalization. Both local and publication snapshots
pass 61 regression tests each, with 11 explicitly configured skips each.
Archive migration preserves 3,211 files. Current documentation links and
private-source portability also pass. Evidence is recorded in
[acceptance.json](../artifacts/repository-acceptance-20261004/acceptance.json).
That dated acceptance does not cover all subsequently added proof sources.
The current local proof snapshot passes the whole build: **16,227 modules**.
Its fresh transitive audit passes **9,375 roots**, using only `propext`,
`Classical.choice` and `Quot.sound`. Evidence is recorded in
[proof-acceptance-16227.json](../artifacts/manuscript-certification-20261005/proof-acceptance-16227.json).
The SI mathematical correspondence is complete. Complete certification of the
combined frozen main and SI remains unavailable while the five main issues are held.
The accepted current proof snapshot is published in
[`14fe906e`](https://github.com/xh-xihe/sslp-classification/commit/14fe906e1fed48aca0b6fe37607fa006ba37e3a6).
Its [publication binding](../artifacts/manuscript-certification-20261005/publication-binding-16227.json)
checks every one of the 16,227 active proof sources against the local
successful build. Earlier publication bindings are retained unchanged.
Machine-readable current status is in
[repository-status.json](../results/repository-status.json).

## Completed mathematical proof packages

- Orbit 2 and orbit 3: full actual-encoder enumerator images, converse,
  interval attainment and exact distance three.
- Existing Section III theory, six-qubit no-gos, constructions and images.
- Previously local proof increments: seven-qubit example, bounded projective
  Clifford groups, QECC/frame normal-form bridges, common-mean and affine
  moment lemmas, and the printed orbit-45 derivation.

The individual entry points are in [proof-index.md](proof-index.md).
Kernel source/build/axiom verification and manuscript statement matching are
separate. Completed proof packages do not imply that every current manuscript
sentence has been matched to its precise Lean theorem.

## Current manuscript review

The current review inventories 1,830 mathematical assertions: 205 in the
main text and 1,625 in the SI. Previous reviews are retained in
[archive/reviews/20261005-before-current-source](../archive/reviews/20261005-before-current-source).

The current claim ledger is bound to the updated source hashes and line numbers.
The 1,823 unchanged statement candidates are retained in
[correspondence-candidates-20261005.json](../results/correspondence-candidates-20261005.json).
The SI comparisons normalize CRLF to LF for candidate matching; the ledger
itself binds the exact authoritative bytes. Candidates require current type
and context review before being classified as covered. The
767 additional previously cited declarations remain explicit kernel audit roots
in [ReviewedDeclarationsAudit.lean](../MainTheory/ReviewedDeclarationsAudit.lean).
The current audit contains 6,611 distinct selected roots in
[ManuscriptCertificationAudit20261005.lean](../MainTheory/ManuscriptCertificationAudit20261005.lean),
including candidate declarations and newly checked physical bridges. Roots
already present in another audit are retained there rather than duplicated.

The current ledger has **1,821 covered assertions**, five scope-only
statements, three stated conjectures and one explicitly partial main Singleton
assertion. There are **zero unreviewed assertions**. In the SI, 1,622 mathematical
assertions have kernel correspondences and three remarks state only scope.
Current kernel type inspection covers **4,806 declarations**.
The source inventory contains **16,227 active Lean modules**.

The full fixed-source prose pass read 251 main and 1,622 SI remaining blocks,
in addition to the earlier 89 localized reviews. Every recorded paragraph hash
is checked against its exact current lines. The SI has no unread or pending
mathematical context. The five frozen main gaps remain explicit.

The final nine modules provide singular-safe complex Schmidt decomposition,
actual positive orthogonal slice frames and all four literal split-family
encoders, physical KL conditions, sorted records and logical actions. Their
[batch record](../artifacts/manuscript-certification-20261005/final-bridge-work-in-progress.json)
binds the strict source snapshots, whole build and fresh evidence.

The [correspondence guide](manuscript-correspondence.md),
[claim ledger](../results/paper-claims-20261003.json),
[prose record](../results/prose-review-20261003.json) and
[remaining obligations](../artifacts/manuscript-certification-20261005/remaining-obligations.json)
state the current mathematical scope and held main issues.

The main text is unchanged. Its five held issues remain for author discussion:
rank-one Singleton scope, hypotheses for diagonal-group finiteness, the
distinction between probability moments and phase-dependent KL conditions,
the representative class in physical-order minimization, and the meaning of
homogeneous rational replacement. See
[the held-errata record](../notes/main-errata-hold-20261003.md).

Full enumerator images for orbits 1 and 4 remain mathematical open questions.
The SI prose/context review is complete; the held main author decisions remain unresolved.
The full manuscript release gate is therefore expected to remain open even
when all public proof checks pass.

The sections below describe earlier proof batches at their dated acceptances.
Their pending-review wording applies to those historical snapshots.

## Literal physical orbit-30 proof route

Twenty-one new modules prove the literal physical K5 labels and moments,
support degrees, synchronized phases and hafnians, all ten pairwise distinct
proper complement types under actual vertex relabeling, and the full-support
determinant obstruction. Separate conditional theorems establish the two-point
and exceptional-branch amplitude and mass formulas without deriving them from
a previously proved no-code theorem.

All eight source-reconstruction checks, the canonical type inspection,
whole build and fresh transitive axiom audit pass. Forty-eight current-source
correspondences were explicitly reviewed; twenty-two previously unreviewed
assertions are now covered. The
[batch record](../artifacts/manuscript-certification-20261005/orbit30-work-in-progress.json)
retains the evidence and publication scope.

## Actual split enumerators and physical matrices

Twelve modules derive normalized actual-encoder Pauli sums for arbitrary
complex isometries and both printed orbit-three output conventions, all seven
split-family enumerators, orbit-26 KL matrix entries in the SI group order,
the complete orbit-28 probabilities and support, and literal orbit-32 parity
labels. Sixteen correspondences were explicitly reviewed, including twelve
previously unreviewed assertions and four strengthened matrix bridges.

The whole build, fresh standard-axiom audit, canonical type inspection and
three source-reconstruction checks pass. The
[batch record](../artifacts/manuscript-certification-20261005/split-matrix-work-in-progress.json)
states the limited proof scope. Later isolated draft proofs are excluded from
this acceptance until a new canonical build and audit pass.

## Physical anchors and parity frames

Ten modules prove the literal orbit-19 shell indicators and eight isolated
physical anchor products; the actual orbit-26 singular anchors, unit-phase
dependent columns, normalized projectors and nonmatching branch; and the
literal effective-coordinate spinors and full physical frames of orbits
14, 15 and 24. Thirty formerly pending assertions and four strengthened
correspondences have explicit current type/context review.

The whole build, fresh standard-axiom audit, canonical type inspection and
two source-reconstruction checks pass. The
[batch record](../artifacts/manuscript-certification-20261005/frame-anchor-work-in-progress.json)
states the accepted scope. Generic matching-row algebra in this batch does
not by itself close the later physical matching-branch intermediates.
Subsequent isolated drafts require a separate canonical build and audit.

## Matching anchors, orbit-17 moments and physical parity blocks

Fifteen modules supply actual orbit-26 matching-anchor and mixed-row
consequences, orbit-17 rational moment equations and unit conjugate phases,
orbit-13/14 physical block frames, literal order-two residues, orbit-24
repetition-Pauli compressions, and the orbit-19 tail identity. Forty-one
formerly pending displayed assertions have explicit current type review.
The overlap-preserving anchor gauge and weighted-line frame identities are
generic algebra; their hypotheses remain explicit, and generic line frames
do not alone certify the remaining actual orbit-14 line-frame display.

Whole kernel building, fresh standard-axiom auditing, canonical type
inspection and the fifteen-source snapshot check pass. The
[batch record](../artifacts/manuscript-certification-20261005/matching-parity-work-in-progress.json)
states the accepted scope. Remaining manuscript correspondences still
require their own proofs and review.

## Actual scalar moments and spinor matrix identities

Twelve modules derive orbit-5/6/12/20 physical row data before their final
obstructions, orbit-5 partial traces and marginal expectation, orbit-6/12
rational moment consequences, all five orbit-6 spinor matrix identities,
orbit-12 cross-block and frame equations, and parity character determinants.
Twenty formerly pending displayed assertions have explicit fresh type review.

Whole kernel building, fresh standard-axiom auditing, canonical type
inspection and the twelve-source snapshot check pass. The
[batch record](../artifacts/manuscript-certification-20261005/scalar-spinor-work-in-progress.json)
states the accepted scope. Remaining manuscript obligations retain their
own incomplete status.

## Actual matrix, scalar and supported-basis displays

Twenty modules certify actual orbit-5/6/12/13/17/20 basis expansions,
spinor lines, independently derived edge frames, scalar cancellation and
elimination, arbitrary matrix tests, phase triangles and normalized Pauli
coordinates. Thirty-five previously pending manuscript displays have fresh
kernel type and context review.

The whole kernel build, fresh standard-axiom audit, canonical type inspection
and the twenty-source snapshot check pass. The
[batch record](../artifacts/manuscript-certification-20261005/display-route-work-in-progress.json)
records this scope. Three SI obligations and the frozen main issues retain
their incomplete status; draft proofs are separate from accepted evidence.

## Historical records

The orbit-specific [2026-10-04 acceptance](../artifacts/orbit-certification-20261003/unified-acceptance-20261004.json)
checked the full local proof tree and bound the published orbit-2/3 closure.
The current repository acceptance additionally binds every active published
proof source. Dated records retain their original commit and snapshot scope.

The localized SI qualification and explicit unchanged-context revalidation are
recorded in [nonempty-mask-context-revalidation.json](../artifacts/manuscript-certification-20261005/nonempty-mask-context-revalidation.json).
Historical proof and publication snapshots retain their original source bindings.
