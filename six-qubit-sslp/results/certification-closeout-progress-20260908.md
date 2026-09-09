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

## Still in progress

- Universal beta bounds at 8 and 9 are **not yet claimed complete**. Their complete sign-prefix
  proposals and regenerated DAG certificates exist; development builds use four and eight
  single-thread Lean processes respectively. The original serial full build remains uninterrupted.
- The ledger has 588 covered assertions, 4 partial assertions, 2 explicit conjectures and
  1003 unreviewed assertions. The main text has no remaining unreviewed display entries;
  the four partial entries and both full-prose reviews remain open. The reviewed table and
  newly connected main-text displays are recorded explicitly; the remaining prose and
  intermediate formulas must not be silently relabelled as covered.
- The physical argument proves finite components and scalar connected action directly. The
  separate prose route through a closed Lie subgroup theorem and an identity-component torus
  isomorphism has not been certified by these new modules.
- Final root imports, axiom-union closure, full source-fingerprinted build, all acceptance gates,
  final documentation and repository publication remain outstanding.

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
