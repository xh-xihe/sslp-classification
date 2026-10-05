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
The current local proof snapshot passes the whole build: **16,128 modules**.
Its fresh transitive audit passes **8,189 roots**, using only `propext`,
`Classical.choice` and `Quot.sound`. The scope and evidence are recorded in
[proof-acceptance-16128.json](../artifacts/manuscript-certification-20261005/proof-acceptance-16128.json).
This local acceptance does not declare complete manuscript correspondence.
The accepted current proof snapshot is published in
[`abc13b21`](https://github.com/xh-xihe/dyadic-lifts/commit/abc13b21f76a7e562231432882a08a3fc5e4c8d1).
Its [publication binding](../artifacts/manuscript-certification-20261005/publication-binding-16128.json)
checks every one of the 16,128 active proof sources against the local
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
The current audit contains 5,425 distinct selected roots in
[ManuscriptCertificationAudit20261005.lean](../MainTheory/ManuscriptCertificationAudit20261005.lean),
including candidate declarations and newly checked physical bridges. Roots
already present in another audit are retained there rather than duplicated.

The current ledger has **1,658 covered assertions**, five
scope-only statements, three stated conjectures, **163 unreviewed
SI assertions**, and one explicitly partial main-text Singleton assertion.
Current kernel type inspection covers **6,387 declarations**.
The source inventory contains **16,128 active Lean modules**. The new
correspondence proofs include:

- Orbit 31: the exact support-count chain, all sixteen representatives and
  orbit sizes, all 204 vertices, coordinate-face convex hulls, the literal
  type-9/14/16 triangle arguments, rank minors and nonempty-mask relative
  interiors. The SI's empty-mask qualification remains an explicit gap.
- Orbit 32: the complete real moment normal form, rank minor and literal
  physical exclusion. Orbit 33: all six rational-reflection blocks, normalized
  phase pairs and the physical projector argument, including boundary cases.
- Order two and three: literal moment systems and signed maximal minors,
  half-angle flips and shell projectors, complete real normal forms and all
  six order-three physical cross exclusions, including synchronization and
  pinning for orbits 49 and 51.
- The arbitrary complex-isometry split construction, physical full KL,
  exact distance, the orbit-three output order and all fifteen standard-code
  syndrome entries.
- Orbit 45: actual physical rows and spin flip, zero-amplitude boundaries,
  physical phase gauges and canonical form, cross factors, logical actions
  and complete printed enumerators. Orbit 29: the physical pair reduction,
  dimension-eight full moment polytope, all fifteen simplex relative interiors
  and face dimensions, physical phase gauge and final eta equations.

The proof entry points and reproducible source checks are listed in
[proof-index.md](proof-index.md) and [reproduce.md](reproduce.md).

The remaining SI assertions include intermediate derivations; final image/no-go
results do not automatically certify them.
The [remaining-obligation inventory](../artifacts/manuscript-certification-20261005/remaining-obligations.json)
gives every unfinished statement's current locator. These locators denote
pending reviews, not findings that the corresponding mathematics is false.
The [prose review](../results/prose-review-20261003.md) is partial:
74 SI blocks have current type/context evidence, one SI qualification
remains open, and the five frozen main issues remain explicit gaps. Other
running text still requires review.

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
