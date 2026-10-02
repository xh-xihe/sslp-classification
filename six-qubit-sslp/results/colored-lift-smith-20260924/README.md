# The same binary pivot, Smith factor and physical colored lift

This increment closes the combined-witness gap in `thm:colored-finite-lift`
of the unchanged 20260924 manuscript. It does not complete full manuscript
certification.

The public theorem is
`MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects` in
[`PaperColoredFiniteLift.lean`](../../MainTheory/PaperColoredFiniteLift.lean).
Its assumptions are single-site Z detection, an actual diagonal symmetry,
its real-angle representative and a nontrivial projective class. It does not
add a distance-two assumption. The color count is the operation's actual
number of distinct logical eigenvalues.

One construction retains all of the following:

- A nonsingular zero-one matrix from the same selected support rows/columns,
  with size equal to the colored-matrix rank and at most n+ell-1.
- The literal rational solution of that binary system. Restoring column signs
  and inserting zero at nonselected coordinates gives exactly the augmented
  solution used to construct the physical lift.
- An actual normalized Smith witness of the binary matrix, with q dividing
  its last factor. The supporting theorem holds for every such Smith witness.
- The primitive finite gate in the original intrinsic class, with m dividing q,
  q at most beta_(n+ell-1), and beta_(n+ell-1) at most beta_(n+K-1).
- An attained minimum over all primitive lifts of the original class, bounded
  by this same q and hence by beta_(n+ell-1).

The new algebraic bridge is
[`BinaryPivotLift.lean`](../../MainTheory/BinaryPivotLift.lean). Smith existence,
canonical pivot selection, rationalization, the spectral resolution and the
intrinsic-class bridge are reused from existing kernel proofs.

## GitHub comparison

The remote branch heads were queried with `git ls-remote` and fetched without
checking out or merging. The observed `sixqubit-classification` head was
[`7ac9a049`](https://github.com/xh-xihe/dyadic-lifts/tree/7ac9a049a8cfb997427a24cb33547fb0592fc170/six-qubit-sslp).
Its `MainTheory`, `SixQubit` and `SS` Git trees exactly match the local
committed proof trees, despite the different repository layout and commit
history. The `main` and `dev-zc` snapshots were also inspected; their observed
heads date to 2026-08-15 and 2026-08-26 respectively.

`github-comparison.json` records tree identities, the three observed remote
heads, nine reused source blobs and working-file hashes. The local 20260924
proof increments are additional uncommitted work. No branch checkout, merge,
commit or push was performed. These are observed snapshots, not a claim that
the remote heads will remain unchanged.

## Review and validation

`review.json` binds the theorem, its three nested bounds and `eq:pivot-solve`
to the exact manuscript/source hashes. The bounded prose entry checks the
combined-construction claim at main lines 1336-1343, without accepting all
subsequent proof prose.

The ledger now has **25 covered, 4 partial, 1623 unreviewed** entries.
Sixteen of the initial nineteen priority named statements have reviewed
correspondences; three remain partial, with Singleton separately partial.
These counts include nested displays and are not proof-completion percentages.

To repeat the dependency build and partial acceptance run from the repository
root on Windows:

```text
python results/colored-lift-smith-20260924/build-audit-dependencies.py
python tools/verify.py --paper-version 20260924 --only release axioms audit-names named-results readme claims prose-review errata
```

The source driver builds the current audit import closure and validates reused
artifacts by content. The audit uses the current source inventory and a shared
Lean axiom collector, without relying on older umbrella `.olean` files. The
coverage, prose and errata gates must still prevent a full-release pass.
Actual measured results are retained in `validation.json` and the accompanying
logs. Earlier proof-increment archives are preserved unchanged.

Completed validation on Windows:

- Both new modules compiled serially with warnings treated as errors. The
  complete audit import closure has 14,094 modules: 2 rebuilt and 14,092
  content-validated existing modules. This was not a clean rebuild.
- The actual shared-state Lean audit passed for 1,497 declarations. Its
  transitive axiom union is exactly `Classical.choice`, `Quot.sound`, `propext`.
- Audit names, documentation/covered-claim names and generated named-result
  freshness passed. The four changed Lean files passed the forbidden-token
  sweep. Both manuscript hashes and all nine reused GitHub source hashes
  remain unchanged.
- The partial acceptance run correctly failed its coverage, prose and errata
  gates. The archive therefore records `proof_increment_passed: true`,
  `full_manuscript_certification: false`, and `full_suite: false`.

The remaining errata are the unqualified Singleton display, the cited orbit-7
gate convention and orbit-9 bit ordering. No manuscript edits or application
deployment were made in this increment.
