# Current verification status

Canonical branch: **`sixqubit-classification`**. Package: `six-qubit-sslp/`.
Private manuscript version: `20261003`, including the SI edits through
2026-10-05. The comprehensive current-source correspondence review is in
progress. Its [run record](../artifacts/manuscript-certification-20261005/run.json)
binds the frozen main text and current supplementary source hashes.

The previous whole-project proof acceptance was **PASS**: 15,923 active Lean modules
(one newly compiled audit module, 15,922 content-validated cached modules),
2,764 transitive axiom roots and 10,085 manifest-bound generated sources.
The publication snapshot contains every active proof source, bound to that
successful build with LF normalization. Both local and publication snapshots
pass 61 regression tests each, with 11 explicitly configured skips each.
Archive migration preserves 3,211 files. Current documentation links and
private-source portability also pass. Evidence is recorded in
[acceptance.json](../artifacts/repository-acceptance-20261004/acceptance.json).
That dated acceptance does not cover all subsequently added proof sources.
The complete local proof snapshot passes the whole build: **15,951 modules**,
with three rebuilt and 15,948 content-validated cached modules. Its fresh
transitive audit passes **4,471 roots**, using only `propext`, `Classical.choice`
and `Quot.sound`. The current source, declaration-name and navigation gates
also pass. The unchanged 10,085 generated-source bindings and all 66 orbit rows
passed in the preceding current-source verification. The scoped proof acceptance
is recorded in [proof-acceptance-15951.json](../artifacts/manuscript-certification-20261005/proof-acceptance-15951.json).
The preceding accepted proof snapshot is published on the canonical branch in
[`d8c38263`](https://github.com/xh-xihe/dyadic-lifts/commit/d8c382635cbd8c569f0a76ac1b47a85d3511cfdf).
The [publication binding](../artifacts/manuscript-certification-20261005/publication-binding-15942.json)
checks all 15,942 proof sources against the accepted local snapshot.
The accepted 15,951-module snapshot is awaiting canonical publication, as
recorded in [run.json](../artifacts/manuscript-certification-20261005/run.json).
The
machine-readable current status is
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
Another 1,707 roots now enter the shared audit through
[ManuscriptCertificationAudit20261005.lean](../MainTheory/ManuscriptCertificationAudit20261005.lean),
including candidate declarations and the newly checked physical bridges.

The current ledger has **1,473 covered assertions**, five scope-only statements,
three stated conjectures, **348 unreviewed SI assertions**, and one explicitly
partial main-text Singleton assertion. Kernel type inspection covers 3,108
named declarations. The new proofs include the actual cat isometry and
six-qubit tensor encoder, its compressions, the closed parameter path, the
literal binary encoding, the orbit-three `DE`/`iDE` expectation identities,
the orbit-45 triangle and zero-amplitude algebra, the orbit-33 rational
reflection, and the normalized physical standard perfect-code projector.
The literal cat family now has proofs of full physical weight-at-most-two KL,
its physical projector-trace coefficients and A1/A2 formulas, spin-flip
orthogonality, and weight-three/six logical actions. Both printed split
matrices have isometry, projector and logical-action proofs. The orbit-three
target identity retains the arbitrary positive common column norm.
Both detailed count tables now have proofs for every row and total, using
actual angle-record sets, distinct full fibre-pair payloads and orbit keys.
The new bridges also cover the order-two 25-to-11 reduction, the actual
orbit-three spin trace, and orbit-26 physical probabilities and rational rank.
The remaining SI assertions include intermediate derivations; final image/no-go
results do not automatically certify them.
The [remaining-obligation inventory](../artifacts/manuscript-certification-20261005/remaining-obligations.json)
gives every unfinished statement's current locator. These locators denote
pending reviews, not findings that the corresponding mathematics is false.
The [prose review](../results/prose-review-20261003.md) is partial: nine SI
blocks have current type/context evidence and the five frozen main issues
remain explicit gaps. Other running text still requires review.

The main text is unchanged. Its five held issues remain for author discussion:
rank-one Singleton scope, hypotheses for diagonal-group finiteness, the
distinction between probability moments and phase-dependent KL conditions,
the representative class in physical-order minimization, and the meaning of
homogeneous rational replacement. See
[the held-errata record](../notes/main-errata-hold-20261003.md).

Full enumerator images for orbits 1 and 4 remain mathematical open questions.
The current prose/context review and held author decisions remain incomplete.
The full manuscript release gate is therefore expected to remain open even
when all public proof checks pass.

## Historical records

The orbit-specific [2026-10-04 acceptance](../artifacts/orbit-certification-20261003/unified-acceptance-20261004.json)
checked the full local proof tree and bound the published orbit-2/3 closure.
The current repository acceptance additionally binds every active published
proof source. Dated records retain their original commit and snapshot scope.
