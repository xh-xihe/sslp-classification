# Current verification status

Canonical branch: **`sixqubit-classification`**. Package: `six-qubit-sslp/`.
Private manuscript version: `20261003`, including the 2026-10-04 SI structural edit.

The whole-project proof acceptance is **PASS**: 15,923 active Lean modules
(one newly compiled audit module, 15,922 content-validated cached modules),
2,764 transitive axiom roots and 10,085 manifest-bound generated sources.
The publication snapshot contains every active proof source, bound to that
successful build with LF normalization. Both local and publication snapshots
pass 61 regression tests each, with 11 explicitly configured skips each.
Archive migration preserves 3,211 files. Current documentation links and
private-source portability also pass. Evidence is recorded in
[acceptance.json](../artifacts/repository-acceptance-20261004/acceptance.json).
The machine-readable current status is
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

The SI was reorganized and its abstract was edited after the earlier source
snapshot. All original 119 theorem/lemma/proposition/corollary statements and
1501 reference labels were preserved in that structural edit. The old review
is retained in [archive/reviews/20261003-pre-structure](../archive/reviews/20261003-pre-structure).

The current claim ledger is bound to the updated source hashes and line numbers.
The previous 712 usable matches are retained in
[correspondence-candidates-20261004.json](../results/correspondence-candidates-20261004.json).
They require current context review before being classified as covered. The
767 additional previously cited declarations remain explicit kernel audit roots
in [ReviewedDeclarationsAudit.lean](../MainTheory/ReviewedDeclarationsAudit.lean).

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
