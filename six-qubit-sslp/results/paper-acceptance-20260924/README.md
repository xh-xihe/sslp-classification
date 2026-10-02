# 20260924 acceptance migration — validated 2026-09-26

The version-specific acceptance entry point and first semantic review pass are
implemented. This release is **not fully certified**. The executed partial suite
correctly fails the incomplete claims, prose and errata gates.

The first 19 new/changed named statements have individual review records:
12 reviewed correspondences and 7 partial correspondences. The Singleton
display is separately partial. The 1652-entry ledger therefore contains
12 covered, 8 partial and 1632 unreviewed entries. These counts include nested
displays; unreviewed does not mean a mathematical proof is absent.

Actual Windows validation:

- The audit dependency closure passed content validation: 14,088 cached local
  modules reused, zero rebuilt. This was not a clean rebuild of the repository.
- The kernel axiom audit passed for 1,452 declarations. The transitive union is
  exactly `Classical.choice`, `Quot.sound`, `propext`.
- All 66 current manuscript table rows matched the kernel-proved table. Three
  deliberately corrupted columns (active rank, LP dimension and multiplicity)
  were each rejected by Lean.
- Selected-release source-name resolution and named-report freshness passed.
- 35 acceptance/release unit tests passed; eight opt-in tiny Lean controls were
  skipped. The real kernel audit and table controls above were executed.
- The 56 Explorer regression tests passed. Four migration tests were also
  rerun after adding context-change invalidation. Historical 20260908 report
  freshness checks still passed.

`report.json` is intentionally `passed: false` and `full_suite: false`.
`validation.json` records the scope, file hashes and validation totals.
`audit-dependency-build.json` retains the content-addressed module record;
`axioms.json` binds the audit to the selected claims and prose records.
`orbit-table-kernel/` contains the actual successful and negative harnesses
with their logs.

The prior existence-status erratum for classes 1--4 is resolved in the new
wording. Singleton, the literal cited class-7 gate convention and class-9 bit
order remain recorded as outstanding. No manuscript text was changed.

Commands and next proof obligations are in
[`notes/paper-acceptance-20260924.md`](../../notes/paper-acceptance-20260924.md).
This increment changes the local certification tooling and review records;
it does not publish a new Site or extend an old case certificate's scope.
