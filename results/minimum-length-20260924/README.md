# Minimum length for a projective order-five transversal gate

This increment closes the two minimum-length corollaries in the 20260924
manuscripts and the two padding displays. It does **not** complete full
manuscript certification.

The new results are:

- `MainTheory.MinimumLengthOrderFive.minimum_length`: an arbitrary exact
  rank-two qubit code of distance at least three, with a single-block product
  unitary of projective logical order five, has at least six physical qubits.
- `MainTheory.MinimumLengthOrderFive.canonical_attains`: the explicit canonical
  class-36 states attain six, using the same actual product-matrix interface.
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`:
  every six-qubit code with this property is LU/permutation equivalent to the
  canonical code, with the original distance-at-least-three hypothesis.

The hypotheses use actual one-qubit unitary matrices, literal tensor kernels,
their action on an orthonormal encoding, and the order of the logical unitary's
faithful adjoint representation. They do not assume a diagonal physical basis,
finite physical order, a padded-code certificate or a quotient-group witness.

Five modules supply the proof:

| Module | Content |
| --- | --- |
| `AncillaPadding` | Full KL preservation, normalization, raw enumerator recurrence and normalized A1 increase by m |
| `AncillaGatePadding` | Literal projector P tensor zero-ancilla projectors; identity extension keeps the same logical matrix |
| `TransversalDiagonalization` | Full-distance-preserving local eigenbasis change and one global unit scalar |
| `DiagonalLogicalMatrixBridge` | Logical unitary matrices and actual classes in the intrinsic diagonal quotient |
| `MinimumLengthOrderFive` | Positive padded A1 contradicts the six-qubit zero value; attainment and uniqueness |

The projector and enumerator identities hold for any number of ancillas,
including zero. The A1 identity assumes positive rank, as required by its
normalization. The lower-bound proof uses no unrestricted Singleton assertion.
The separate existing six-qubit exact-distance theorem supplies a physical
weight-three KL obstruction when exact, rather than at-least, distance is needed.

`review.json` binds the four reviewed claims and five new sources to the actual
manuscript hashes. The current ledger has 16 covered, 6 partial and 1630
unreviewed entries. Among the 19 initial priority named statements, 14 are now
covered and 5 partial; Singleton is a separate partial display. These counts
measure review status and include nested displays.

The following full-transversal-group/Clifford prose consequence remains open,
as do the other recorded review gaps and errata. Manuscripts and the deployed
Explorer were not changed by this proof increment.

Validation results are recorded separately in `validation.json` and the
associated build and axiom-audit artifacts. The historical first-pass artifacts
in `../paper-acceptance-20260924/` remain an unchanged snapshot of that earlier run.

Completed Windows validation:

- The five new proof modules compiled with one Lean thread and warnings treated
  as errors. The final audit dependency run content-validated all 14,089 modules
  and changed no compiled artifact. This was not a clean repository rebuild.
- The actual shared-state kernel axiom audit passed for 1,470 declarations;
  its transitive union is exactly `Classical.choice`, `Quot.sound`, `propext`.
- All 91 documentation/covered-claim names resolved in an actual Lean run.
  The checker now reads the current entry-point source imports, fixing a real
  stale-umbrella issue exposed by these new modules. `initial-report.json`
  preserves that initial failure; `readme-recheck.json` records its resolution.
- The tool test suite ran 100 tests: 92 passed and 8 opt-in Lean controls were
  skipped. The new stale-umbrella regression and the actual name check passed.
- All seven changed Lean source files passed the forbidden-proof-token sweep;
  both manuscript hashes still match the original review.

`report.json` combines the initial partial run with the successful name-check
recheck and remains `passed: false`, `full_suite: false`: the claims, prose and
errata gates correctly reject full release acceptance. `validation.json`
reports `proof_increment_passed: true`, `full_manuscript_certification: false`.

The attempted individual-print audit wrapper build was intentionally stopped
after the five new modules had been built. Its previous certificate recorded
1,886 seconds of repeated axiom traversals. The final validation instead uses
the existing shared-state collector against the current audit source inventory;
it does not rely on the old wrapper's printed output. See `build-route.json`.

To repeat the dependency validation from the repository root, run
`python results/minimum-length-20260924/build-audit-dependencies.py`, followed by
`python tools/verify.py --paper-version 20260924 --only release axioms audit-names named-results readme claims prose-review errata`.
The latter is expected to fail the three remaining whole-release gates.
