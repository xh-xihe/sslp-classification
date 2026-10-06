# 20260924 manuscript acceptance

The acceptance entry point now selects the complete set of manuscript review
inputs by version. It does not transfer coverage from 20260908. The historical
default remains 20260908 so existing commands cannot silently change meaning.

```text
python tools/paper_claims.py check --paper-version 20260924
python tools/named_results_doc.py --paper-version 20260924 --check
python tools/prose_review_doc.py --paper-version 20260924 --check
python tools/verify.py --paper-version 20260924 --only release paper claims named-results prose-review errata
python tools/verify.py --paper-version 20260924
```

The first three commands check inventory/report freshness, not full coverage.
The fourth is explicitly partial and currently fails the claims, prose and
errata gates. The last requests the complete suite, including the serial source
build and kernel axiom audit; it cannot pass while those review gaps remain.
Logs and reports are in `tmp/verification/20260924/`. A successful partial
check never reports `full_suite: true`.

Release selection binds both manuscript hashes, the claims ledger, the orbit
manifest, named-result report, prose record/report and errata dispositions.
The 20260924 orbit manifest has its own provenance and exactly the same 66
numeric rows and 51 no-go module mappings as the shared mathematical gates.
The binding check rejects future changes to that shared data until those gates
are migrated as well. An optional private source directory must contain the
same manuscript bytes as the selected release.

Refreshing after either source changes invalidates semantic review statuses
throughout the release. Even an unchanged theorem may depend on a changed
definition elsewhere. Prior candidates and historical reviews can guide a new
review but do not transfer certification.

## First priority review

The 19 priority named entries were read with their surrounding context and
relevant Lean statements. Twelve have reviewed correspondences; seven remain
partial. The Singleton display was also recorded as partial. This is a
single-agent review, not the historical multi-agent adversarial process.

- The new supplementary Results I--IV restate existing mathematical results.
  Their correspondences include attained orders (not only upper bounds), the
  fifteen realizations, the eleven exact enumerator sets and the stronger
  monomial rigidity clause in class 36.
- The new family-inclusion theorem uses existing exact closed-interval
  constructions in classes 1--4. This covers the statement and endpoints, not
  every step of the new split-qubit construction narrative.
- The arbitrary-subspace converse of the general normal form still needs an
  explicit bridge to the already proved arbitrary-rank colored-frame converse.
- The combined binary-pivot/physical-lift statement and the new support-rank
  definition require additional correspondence review; separate existential
  statements cannot be silently conjoined for the same witness.
- The expanded orbit-45 theorem includes the B enumerator and the triangle
  parameters; its older A-image theorem alone is insufficient.
- Both new minimum-length corollaries need arbitrary-length padding, KL/order
  preservation, the weight-one enumerator identity and arbitrary local-basis
  transport. Existing six-qubit uniqueness is not a proof of the lower bound.

The ledger has 1652 entries, including nested displays: 12 covered, 8 partial,
1632 unreviewed after this pass. These are review statuses, not a count of
missing mathematical theorems. Full prose review remains open.

Records:

- `results/paper-review-20260924-priority.json`
- `results/paper-claims-20260924.json`
- `results/named-results-20260924.md`
- `results/prose-review-20260924.json` and `.md`
- `results/errata-20260924.json`

The old existence-status erratum for classes 1--4 is resolved in the latest
text. The unqualified Singleton display, literal cited orbit-7 gate convention
and orbit-9 bit-order ambiguity remain recorded. The author instruction to
leave the manuscript unchanged still applies; no TeX was edited.

## Minimum-length proof completed

The follow-up proof increment on 2026-09-26 closes both minimum-length
corollaries and the two separately tracked padding displays. The current
ledger is **16 covered, 6 partial, 1630 unreviewed**. Among the original 19
priority named statements, 14 now have reviewed correspondences and 5 remain
partial; the Singleton display remains separately partial. These are review
counts, not proof-completion percentages.

`MainTheory.MinimumLengthOrderFive.minimum_length` takes an arbitrary
`ExactCode n 2 d` with `3 ≤ d`, actual local U(2) matrices, and their literal
tensor action on the frame. Projective logical order is defined by the
faithful adjoint representation of the logical unitary. It proves `6 ≤ n`
without a preselected diagonal basis or a supplied padding certificate.
The same module proves canonical attainment and LU/permutation uniqueness
with the original `d ≥ 3` scope.

The supporting modules prove the literal ancilla projector, full KL
preservation at any distance, unchanged logical matrix, and
`AWeight (padFrame F m) 1 = AWeight F 1 + m` for all positive ranks. The local
diagonalization construction now uses `LocalUnitaryKL.unitaryCode`, retaining
the full distance predicate. The matrix/quotient bridge establishes actual
order five in the intrinsic group used by the six-qubit classification.

The proof does not depend on the unqualified Singleton display. The separate
six-qubit exact-distance theorem supplies the weight-three obstruction.
No manuscript was edited. Review and validation artifacts are under
[`results/minimum-length-20260924/`](../results/minimum-length-20260924/README.md).

## Arbitrary-subspace converse completed

The next increment closes the general SSLP theorem and its three nested
outer-data/color/fiber displays. The ledger now has **20 covered, 5 partial,
1627 unreviewed** entries. Fifteen of the initial nineteen priority named
statements have reviewed correspondences; four remain partial, with the
Singleton display separately partial. These counts include nested displays
and measure review status, not the percentage of mathematics proved.

`MainTheory.PaperGeneralSSLP.general_sslp_converse` takes arbitrary subspaces
with the manuscript's dimensions, full computational-fiber containments,
gcd/color conditions and basis-independent KL equations for weights below
the target distance. It proves independence, total rank, equality of the
resulting code span with the supplied direct sum, and the exact intrinsic
order of the literal finite diagonal gate. It requires no preselected frame.

`SubspaceCode` provides the reusable subspace-to-frame and basis-independent
KL interface; the colored construction proves equality with every individual
input sector as well as the whole sum. It handles target distance zero without
strengthening the manuscript hypothesis. Orthonormal basis selection is a
classical existence construction, not an executable basis-generation service.
New codes still need proofs of their supplied fiber and KL conditions.

See [`results/colored-subspaces-20260924/`](../results/colored-subspaces-20260924/README.md)
for the bounded review and validation. Manuscripts remain unchanged.

## Common binary-pivot and physical-lift witness completed

The combined colored finite-lift theorem is now explicit in
`MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`. The
spectral count is the original operation's number of distinct eigenvalues,
and only single-site Z detection is assumed. A single pivot supplies its
binary matrix, actual solution, Smith witness and physical lift. The theorem
retains the original intrinsic class, both divisibilities, the size and beta
bounds, and an attained minimum primitive modulus bounded by that same lift.

`BinaryPivotLift` proves the literal binary system equation and identifies
the sign-restored, zero-extended solution with the lift's augmented solution.
Its Smith-divisibility theorem holds for every Smith witness of that binary
matrix. The construction reuses the canonical pivot, Smith existence and
physical-class bridges already present in the repository.

GitHub was checked using read-only remote queries and fetches. The observed
`sixqubit-classification` head is `7ac9a049a8cfb997427a24cb33547fb0592fc170`.
Its `six-qubit-sslp/{MainTheory,SixQubit,SS}` trees are identical to the local
committed proof trees. The remote `main` and `dev-zc` snapshots were also
inspected. The comparison and nine reused source blobs are recorded in
[`results/colored-lift-smith-20260924/`](../results/colored-lift-smith-20260924/README.md).
No branch checkout, merge, commit or push was performed.

The ledger is now **25 covered, 4 partial, 1623 unreviewed**: 16 of the initial
19 priority named statements have reviewed correspondences, with 3 partial;
Singleton remains a separate partial display. The newly reviewed claims are
the colored finite-lift theorem, its three nested bounds and the pivot-solve
equation. The remainder of the proof prose is not automatically accepted.

## Next mathematical and review work

- Connect the expanded support-rank definitions to the actual classification
  acceptance predicate, and finish the four-level equivalence review.
- Finish the expanded class-45 B-enumerator and triangle-parameter clauses.
- Formalize the subsequent common-logical-basis Clifford consequence. The
  minimum-length theorem does not supply finite rotation-group classification
  or simultaneous conjugacy into the Clifford group.
- Continue context-sensitive review of the remaining displays and prose;
  keep the existing manuscript errata and author decisions explicit.

For class 45, reuse `SixQubit.Orbit45Final.fully_certified`, which already
contains both directions of the raw A/B families. `Orbit45Universal.ConverseData`
retains the actual block masses and the equation t=2*(g1^2+g2^2+g3^2).
The next interface should explicitly convert beta=g1/4, gamma=g2/4,
sigma=g3/4 and normalize the A/B coefficients, retaining the same code and
parameter. This route has been identified but the revised theorem remains
partial until its full parameterization and attainment are checked.
