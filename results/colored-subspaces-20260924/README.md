# General SSLP converse from arbitrary subspaces

This increment completes the missing arbitrary-subspace entrance to
`thm:general-sslp-normal-form` in the unchanged 20260924 manuscript. It does
not establish full manuscript certification.

The public theorem is
`MainTheory.PaperGeneralSSLP.general_sslp_converse` in
[`PaperGeneralSSLPConverse.lean`](../../MainTheory/PaperGeneralSSLPConverse.lean).
Its inputs are the sorted primitive angle, distinct primitive colors with
a designated zero, positive multiplicities summing to K, arbitrary subspaces
of those dimensions in the full computational fibers, and basis-independent
KL equations for all Pauli weights below the target distance.

It proves independence and dimension K and produces an exact code whose span
is precisely the supplied direct sum. Its actual diagonal symmetry is the
displayed D(a;q), and its intrinsic projective class has exact order m.
The original forward statement remains in `PaperGeneralSSLP.lean`.

The reusable components are:

- `SubspaceCode`: every finite-dimensional state subspace admits an
  orthonormal frame with exactly that span, including rank zero. Its KL
  predicate is equivalent to the established frame predicate, including
  the target-distance-zero boundary.
- `GeneralColoredSubspaceConverse`: distinct fibers give orthogonality and
  independent subspaces; concatenating the sector bases retains each original
  sector and the complete code span. Full KL and exact logical order follow.
- `PaperGeneralSSLPConverse`: accepts the manuscript's gcd and literal
  computational-span conditions directly.

Basis selection is noncomputable classical existence in Lean; it is not an
executable algorithm exposed by the Explorer. A future new-code workflow can
reuse these theorems after proving its dimension, fiber and KL obligations.
This increment does not automatically certify arbitrary user-entered codes.

`review.json` binds the general theorem, its three nested displays, the
bounded converse paragraph review and three new Lean modules to source hashes.
The ledger at this increment has **20 covered, 5 partial, 1627 unreviewed**
entries; 15 of the initial 19 priority named statements are covered and
4 remain partial. Singleton is a separate partial display. These are review
counts, not a proof-completion percentage.

To repeat validation from the repository root on Windows:

```text
python results/colored-subspaces-20260924/build-audit-dependencies.py
python tools/verify.py --paper-version 20260924 --only release axioms audit-names named-results readme claims prose-review errata
```

The first command builds and content-validates the current audit import
closure using the serial source driver. The second uses the shared-state
Lean axiom collector on the current source inventory; it deliberately does
not rely on older umbrella `.olean` files. The partial run must still fail
the claims, prose and errata gates while those release obligations remain.
Final measured results are archived in `validation.json` and its logs.

Completed validation on Windows:

- All three new modules compiled serially with warnings treated as errors;
  the build also content-validated 14,089 existing modules (14,092 total).
- The actual shared-state kernel audit passed for 1,490 declarations, with
  transitive axiom union exactly `Classical.choice`, `Quot.sound`, `propext`.
- Audit/claim names, documentation names and generated report freshness passed.
  The five changed Lean files have no forbidden proof tokens.
- Both manuscript hashes are unchanged. The partial acceptance report remains
  `passed: false`, `full_suite: false`: coverage, prose review and the three
  recorded errata correctly prevent a full-release pass.

`validation.json` therefore records `proof_increment_passed: true` and
`full_manuscript_certification: false`. The earlier minimum-length and
first-review archives remain unchanged. No application deployment was made.
