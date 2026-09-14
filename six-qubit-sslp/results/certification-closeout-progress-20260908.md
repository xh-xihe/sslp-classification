# Certification closeout progress, 2026-09-08

This is an incremental progress record, **not a declaration of full certification**.
The target has been updated to `documents/20260908/main.tex` and `supplementary.tex`.
See `manuscript-20260908-review.md` and `paper-claims-20260908.json` for current
coverage and the author-requested separate Singleton erratum. The older ledger
and the historical coverage counts below refer to the 20260905 version.
The original full build (Python PID 30452, started 2026-09-06) remains running.
No development `.olean` has been adopted as a production content-fingerprinted build stamp.

## Completed and checked in this closeout

- The independently defined complete-KL SSLP output has an exact quotient/image theorem, and its
  bounded audit covers the actual intrinsic group. See `SSLPPipelineQuotient.pipeline_exact_beta`.
- The physical diagonal stabilizer on real angles modulo integers is identified with its matrix
  conjugation definition and the existing range-preserving symmetry group. Closedness, compactness,
  finite connected-component quotient, scalar identity-component action and surjective factorization
  are proved. `PhysicalComponentFactor.finite_intrinsic_of_z_detection` needs only the manuscript's
  Z-detection hypothesis, not an extra full-distance assumption.
- Literal sector-projector sum, eigen-equation, trace, positive-support probability normalization,
  number-operator compression and supported occupation-trace identities are connected to the
  existing general spectral extraction, including degenerate eigensectors.
- Actual tensor-X shifts, real angle/phase normalization, preservation of Z detection, protected
  rationalization and reduced integer numerator congruences are connected. Rationalization after
  the zero-support normalization preserves the actual physical angle on every supported string.
- The first-moment caveat has explicit probability/phase counterexamples. The raw outer loop has
  a kernel-checked all-zero, nonprimitive record with an empty second fibre.
- All 66 table row rank/semantics modules passed development compilation. The aggregate proves
  maximum attainable real support ranks, affine dimensions of the complete real nonnegative LP,
  and actual labelled record multiplicities. Every row's full fibres are connected to the key counted.
- `orbit_table_kernel.py --selftest` passed: current TeX's seven scalar columns and all six-angle
  vectors agree with the kernel data, and mutations of r_star, LP dimension and multiplicity are
  each rejected by Lean. Numeric capstone axiom audits list only the standard three axioms.
- All 28 certification-tool regression tests passed with `CERTIFICATION_LEAN_TESTS=1`, including
  real Lean negative controls. The mock audit count now derives from the configured inventory;
  the production checker was not relaxed.
- The complete size-seven sign-prefix DAG passed all 197 module compilations. `betaSevenExact`
  proves the universal bound and genuine attainment at 18, and `SixQubitDistanceTwoBound`
  applies it to the defined minimum lift modulus of actual six-qubit rank-two codes with d >= 2.
  `BetaExactValue` connects semantic exact certificates to the finite-supremum definition of beta.
- Uniform sign-prefix pruning and restricted row-chunk pruning now use proved recursive quadratic
  minima. The actual partial beta-nine benchmark passed kernel compilation. Three additional Lean
  controls passed: a valid minimum was accepted, an overstated bound and a wrong fixed-bit chunk
  were rejected. No native evaluation axiom is used.
- `ColoredJointOrder`, `ScaledColorPhases`, `ColoredSmithDisplays`, `NormalizedSupportCovariance`
  and `SparseSmithDisplays` explicitly connect the intermediate color-order, complex-exponential,
  full-coordinate Smith clearing, actual-support covariance-range and sparse-phase equations.
  Their capstone audits list only the standard three axioms. Twenty-nine further main-text
  displays now have individual statement reviews.
- Updated generated-source coverage, hashes and dependency checks passed for all seven families:
  819 + 1101 + 11 + 40 + 197 + 1466 + 5356 files.
- The order-nine fourteen-coordinate real moment polytope is proved to be exactly the
  singleton printed in the supplement, of affine dimension zero. Both means, the exact
  covariance matrix, determinant 5/157464, rank six, positive support and phase parametrization
  have direct proofs and standard-three-axiom audits.
- Orbit 36 now has a checked LU proof of its actual 12x12 character minor determinant
  -2^19, a real character-span theorem, and an explicit bridge from the complete 23-row
  real LP to the diagonal-moment normal form. This includes all boundary probability faces.
- All twelve cross pair relations and four star sums are derived from actual distance-three
  KL. The literal phase matrix has determinant -5 and induces a surjective map on seven unit
  phases; its exponent rows are tied to the actual basis words and common edge product.
- The orbit-36 adjugate argument is explicit: rank three, one-dimensional kernel, nonzero
  rank-one adjugate factorization, diagonal cofactor norms and a positive common p_i*s_i.
  The boundary ratios, graph classification and multiplicity-case equations are also checked.
- Orbit 36's canonical square-root amplitudes, actual antiunitary operator and arbitrary-Pauli
  expectation sign are proved. The positive-sign weight-three masks have a complete kernel
  classification. Both normalized trace definitions, the general six-qubit MacWilliams vector,
  the unique orbit-36 A/B vectors and its generating polynomial are connected explicitly.
- Orbit 7's full state expansions, shell equations, scalar degree identities and pair moments
  are proved on actual full-fiber states. The normalized two-qubit partial trace agrees with
  its block formula; the extreme rescalings are Hermitian idempotents and give the target blocks.
- Orbit 7's literal Jacobian is proved to be the derivative of the hafnian map, with the
  displayed nonzero minor, rank five and the exact vertex-tangent kernel. The six graph
  cases, normalized frame masses and affine-parameter equations are explicitly connected.
- The exceptional-vertex coefficient matrix has a checked right inverse and constant-vector
  kernel. Its actual hafnian equations, normalized rank-one projectors, family-mass cancellation,
  circle parametrization and endpoint identities passed compilation and capstone axiom audits.
- Twenty previously missing development oleans were compiled successfully. A combined audit
  of all 1114 declarations referenced by the 583 covered claims passed, with axiom union
  exactly propext, Quot.sound and Classical.choice. This remains development evidence and
  does not replace the final source-fingerprinted build or the outstanding claim reviews.

## Independent review, 2026-09-09

An independent pass over the accumulated work, checking rather than accepting
the record above. Everything below was measured.

Confirmed: label sweep 33/33 and 93/93 against the new manuscript; the ledger
validates against the current TeX hashes; 14177 Lean sources carry no
forbidden token; every audited `#print axioms` name and every ledger-cited
declaration resolves; only six modules lacked an olean and all six were
orphans; the gates `sources`, `generated`, `paper`, `table-kernel`,
`table-kernel-selftest`, `gate`, `gate-selftest`, `moments`,
`moments-selftest` and `audit-names` pass; the tool suite passes. The
verification harness was strengthened over the period, not relaxed.

Four defects were found and fixed.

- `tools/run.py` put only `core/` and `orbits/` on `sys.path`, not
  `verification/`. `orbit_table_kernel.py` imports `mkmanifest` directly, so
  both table-kernel gates died with ModuleNotFoundError through `verify.py`
  while passing standalone. Any full acceptance run would have failed there.
- The axiom gate could not execute. Its harness is built from
  `MainTheory/Audit.lean`'s own imports, and 957 of the 1843 declarations
  cited by covered claims lived in modules unreachable from it, so they would
  be reported as missing kernel declarations. The 254 modules owning them are
  now imported; the audit closure went 6614 -> 12615 of 14177.
- The same harness overflowed the code generator once the root inventory
  passed a few thousand names. It now emits one array literal per 200 roots
  joined by `++` under a raised recursion depth. `verify.py --only axioms`
  then passed: 2891 declarations, axiom union exactly propext,
  Classical.choice and Quot.sound.
- `MainTheory/OrderFour26DiagonalRows0..3` did not compile at all, failing
  with "ring failed". The cause was not mathematical: `norm_num` left some
  indices as `bottom 2` and others as `bottom ⟨2, ⋯⟩`, which `ring` treats as
  different atoms. Adding `Fin.reduceFinMk` to the following `simp only` fixed
  all sixteen sites. This mattered because the build plan comes from the
  lakefile globs, so a broken module fails the full build whether or not
  anything imports it. No ledger claim cited any declaration in them, so no
  coverage claim rested on broken work.

`beta_9 = 120` is now proved, which closes `eq:small-beta`. Its whole
size-nine sign-prefix DAG of 5374 modules had already compiled; only the
capstone reading that certificate as `BetaBound 9 120` had never been
compiled, which is why the value could not be claimed. `betaNineBound`,
`betaNineExact : BetaExact 9 120` and the new `BetaNineValue.betaOf_nine`
compile with the standard three axioms, over a closure with nothing stale or
mismatched. The ledger is 994 covered, 6 partial, 2 conjecture, 586
unreviewed.

Whole-root imports are deliberately not done, superseding the item below. The
build plan already covers all 14177 modules from the lakefile globs regardless
of what the roots import, and the axiom gate is built from the audit files,
whose closure now contains every declaration any covered claim cites. Making
the roots import everything would add only a coherence check, at the cost of a
Lean process loading about 14000 oleans.

A full source-fingerprinted build over all 14178 planned modules started on
2026-09-09 with the tree frozen at that commit.

## Acceptance, 2026-09-14

The full source-fingerprinted build finished and the whole gate was run against
it. Fourteen of the fifteen checks pass:

```
build                   PASS  0 serially rebuilt, 14178 content-validated cached modules
axioms                  PASS  3529 declarations; union = Classical.choice, Quot.sound, propext
sources                 PASS  14178 Lean sources clean
generated               PASS  coverage, SHA-256 and build order over 8990 generated files
paper                   PASS  66 orbit rows, 51 no-go mappings, both private-source hashes
table-kernel            PASS  66 rows match full-fibre kernel semantics
table-kernel-selftest   PASS  all three numeric-column mutations rejected
claims                  FAIL  320 incomplete assertions; 2 prose reviews not complete
gate                    PASS  every module matches the manifest and its headline ordering
gate-selftest           PASS  caught 3, missed 0
moments                 PASS
moments-selftest        PASS  every injected corruption rejected
readme                  PASS  all 2950 cited identifiers present
audit-names             PASS  all audited and ledger-cited names resolve
named-results           PASS  document current against the ledger
```

The build itself was `PASS: 7612 serially rebuilt, 6566 content-validated cached
modules`, zero errors and zero warnings, over 14,178 modules.

Two of these were never conclusive before and are now.

`axioms` could not run at all while any declaration a covered claim cites lived
outside the audit files' import closure; fifteen such declarations sat in seven
modules. `readme` was failing with what looked like widespread documentation
drift, and was not: `.lake/build/lib/lean/MainTheory.olean` was four days older
than `MainTheory.lean`, and `lake env lean` never rebuilds, so a stale root
olean silently hid its own imports. Adding the seven imports to
`MainTheory/Audit.lean` repaired both closures at once, because the root module
imports the audit file. The audit-closure debt is now zero.

The one failure is the honest one. `claims --require-complete` refuses while any
assertion is `partial` and while either prose review is open, and 320 displays
are partial. Its message previously named only the first offender, which read as
though a single assertion stood in the way; it now reports the full count and
the open prose reviews.

## Still outstanding

- **The three errata.** `eq:quantum-Singleton` is false as written and has a
  kernel-checked counterexample; `eq:o7knowntransversal` names a cited
  construction whose gate convention provably fails to preserve the span at
  theta = 0; the orbit-9 literal witness has an ambiguous printed bit order.
  These are author decisions on the text, not Lean work. The first is why
  `claims` names `main.tex:eq:quantum-Singleton` first.
- **Both prose reviews.** Running text is where an unformalized claim can hide,
  because nothing in the pipeline forces those sentences to be looked at. The
  review in progress has already found assertions no theorem carries, including
  the minimality claim in the abstract.
- **320 partial displays.** Not 320 gaps: five remarks and four tables carry a
  result name, the rest are displays, and a large group of those are steps of a
  manuscript route this development deliberately does not take. Every one has a
  declaration and a written reason. See `results/named-results-20260908.md`.
- **Two tables are close to closable.** `tab:angle-record-counts` and
  `tab:fiber-pair-counts` have most entries proved and lack only per-(q,m)
  splits of one or two columns. The cheap route is to reduce the survivor list
  to a literal once and bucket the small result, rather than to run one
  sharded `decide` per row.
- Universal beta bounds at 8 and 9 beyond what is already recorded.

## Build and source notes

Two pre-existing table aggregate sources had an ambiguous unqualified `multiplicity` name.
`Generated/OrbitTableMultiplicities.lean` and its generator now qualify the intended constant;
`OrbitTablePaperKey.lean` does the same. Both fixed sources passed development compilation.
The original build's source snapshot predates these necessary fixes, so a final new build pass
must validate the updated source graph even after the original process finishes.

Development evidence is in `tmp/`, notably:

- `orbit-table-development.log`, `orbit-table-numeric-development.log`
- `orbit-table-kernel-selftest.log`, `audit-completed-orbit-numeric.log`
- `audit-physical-all-z.log`, `audit-sector-projector-identities.log`
- `audit-normalized-phase-equations.log`, `audit-first-moment-and-outer-boundary.log`
- `certification-tools-full-unittest.log`
- `sign-beta7-single-node-build.log`, `audit-beta-seven-and-chunk-prune.log`
- `audit-main-arithmetic-displays.log`, `audit-sparse-geometry-displays.log`
- `audit-main-finite-displays.log`
- `quadratic-prune-negative-controls.log`, `generated-manifests-quadratic-chunks.log`
- `audit-order-nine-statistics.log`, `audit-orbit36-moments.log`
- `audit-orbit36-cross-phase.log`, `audit-orbit36-adjugate.log`, `audit-orbit36-boundary.log`
- `audit-orbit36-canonical.log`, `audit-orbit7-scalar.log`, `audit-orbit7-matrix.log`
- `audit-orbit7-coordinates.log`, `audit-orbit7-six-graphs.log`
- `audit-orbit7-boundary.log`, `audit-orbit7-jacobian-affine.log`
- `audit-orbit7-xi-projectors.log`, `audit-orbit7-circle-endpoints.log`
- `audit-orbit7-structure.log`, `audit-orbit7-purity.log`
- `audit-orbit7-pauli-enumerators.log`
- `certification-current-source-scan.log` (13,943 Lean sources clean at this scan)
- `build-missing-ledger-development.log`, `audit-current-ledger-driver.log`

The authoritative manuscripts have not been edited to weaken any statement.
