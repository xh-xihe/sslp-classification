# 20260908 manuscript review

The authoritative target is now `documents/20260908/main.tex` and
`documents/20260908/supplementary.tex`. Neither file has been edited by this
certification work. This is an open review, not a full-certification claim.

## Migration and validation

- A separate `paper-claims-20260908.json` records 1588 assertion entries.
- Unchanged statement hashes were retained only within unchanged line blocks
  with a 20-line context margin. Changed or moved contexts were reopened.
- Initial migrated counts: 526 covered, 3 partial, 2 conjectures, 1057 unreviewed.
  Both whole-prose reviews remain open. Detailed provenance is in
  `paper-migration-20260908.json`; the older ledger is preserved.
- The 66-row orbit table is unchanged. The manifest now records the new source
  paths and SHA-256 hashes. The current table kernel check and its three numeric
  mutation controls passed (`tmp/orbit-table-kernel-20260908.log`).
- After the revised-main review and the cited-construction counterexample:
  581 covered, 6 partial, 2 conjectures, 999 unreviewed. After the subsequent
  orbit-8, orbit-9, orbit-21, orders 6–8, orbit-25 and order-four table review: 993 covered, 7 partial,
  2 conjectures, 586 unreviewed. The orbit-9 literal witness is partial
  because its printed bit order needs clarification; its exact integer-display
  interpretation is certified and a left-to-right fiber mismatch is proved.
  The main assertion
  inventory has no unreviewed entries, but five partial entries and the whole
  prose review remain open. These counts are not a proof of full coverage.
- The 31 certification-tool regression tests, including enabled Lean negative
  controls, passed with process exit code 0 in 82.766 seconds
  (`tmp/certification-tools-20260908-clean.log`).
- A development axiom-closure check passed for 1835 ledger declarations
  across 866 imports at the 989-covered snapshot
  (`tmp/audit-current-ledger-20260908.json`). A subsequent orbit-8 check
  passed for 121 declarations in 23 new modules
  (`tmp/audit-orbit8-current.json`). The orbit-9 check passed for 69 declarations
  in 15 modules (`tmp/audit-orbit9-current.json`). These checks admit only `propext`,
  `Classical.choice`, and `Quot.sound`; neither replaces a final build.

Subsequent development checks passed for 15 declarations in the diagonal
unitary/gauge modules (`tmp/audit-orbit9-gauge.json`), five in the actual K4
matrix and constant-kernel modules (`tmp/audit-orbit9-k4.json`), and eight in
the projector stabilizer and normalized enumerator modules
(`tmp/audit-orbit9-enumerator.json`). The phase gauge is now constructively
realized by physical local diagonal unitaries followed by a unit logical
rephasing. Its existence does not use the later two-support contradiction.

The complete A, B and shadow coefficients now have literal matrix-trace
semantics, correct Fourier factors and nonnegativity proofs. The tensor-Y
matrix identity is explicit. The new orbit-21 printed witness was checked
independently of the older witness: its full low-weight KL equations, norms,
fiber support and inverse-square-root amplitudes passed kernel checking.
The exact normalized Farkas identity and the physical diagonal-gate square
and projector equations also passed development compilation and axiom checks.
These incremental logs are named `tmp/audit-complete-shadow-trace.json`,
`tmp/audit-complete-pauli-coefficients.json`,
`tmp/audit-orbit21-literal-witness.json`, `tmp/audit-orbit21-farkas-display.json`
and `tmp/audit-orbit21-physical-gate.json`.

The representative orbit-21 face now has a proof of its two-parameter
probability form from the literal degree-two moment equations, an exact
Walsh nullspace, and a bridge from actual KL conditions to those Walsh
equations. Equal squared amplitudes give the required monomial magnitudes,
and the resulting uniform parameters are both 1/8. The moment and Walsh
audits passed (`tmp/audit-orbit21-moment-face.json`,
`tmp/audit-orbit21-walsh-face.json`, `tmp/audit-face-kl-and-summary.json`).
The rank-six proof uses a two-parameter linear equivalence with the kernel.
Its two declarations also passed `tmp/audit-orbit21-walsh-rank.json`.
The literal unphased X^u Z^v matrix-element and KL equations also passed
their four-root audit (`tmp/audit-full-kl-displays.json`).

## Orbit-8 semantic and intermediate displays

The five order-seven representatives now have literal ordered supports,
exact complete angle-record lists, complementary-fiber checks and proofs of
their probability parameterizations from all 23 moment constraints. Their
five specified moment minors have kernel-checked determinants -28, 42, -42,
-28 and -28. All 40 moment and determinant declarations passed
`audit-order-seven-moments-determinants.json`; the support and record audits
also passed. These results do not yet close every phase argument or the
surrounding affine-dimension prose.

Orbit 58 now has an independent proof following the revised text: actual
KL equations give the literal rank-three Walsh systems; paired norm squares
force s=3/28 and t=1/7; the remaining actual flip equations give the common
phase, two product identities and the final nonzero contradiction. Its
complete literal no-go and phase-algebra audit passed with six declarations
in two modules (`audit-order-seven-58-literal-nogo.json`). The five reverse
moment-family verifications also passed their audit. None of these results
closes the separate whole-prose coverage or final production build.

The four order-six representatives now have full moment parameterizations,
reverse feasibility, exact nonnegativity regions and the four literal minor
determinants 24, 36, -36 and 48. The corresponding development audits passed.
Seven physical four-edge Walsh systems and their magnitude consequences
passed a 58-declaration audit; actual KL forces the stated parameters in
orbits 53, 54 and the first parameter in orbit 56. Exact rational row
combination certificates for 29 further flip equations, together with the
orbit-55 boundary-positivity argument, passed the 179-declaration
`audit-order-six-phase-rows-and-boundary.json` audit. Complete phase closure
is still being connected to these results.

The revised order-eight A and B moment determinants are now checked against
the specified rows and column ordering, giving -48 and 32. Both probability
forms follow from the full moment system; for B, every parameter in the
printed closed interval is feasible. The literal new B triangle has its own
complete incidence checks, actual KL equations, fifth-bit dressing signs,
six nonzero amplitudes and positive/negative ratio contradiction. It does
not reuse the older triangle's intermediate amplitude labels. Development
audits passed for these modules, including `audit-order-eight-b-triangle.json`
and `audit-order-eight-b-flips.json`. The actual A edge equations and positive
sqrt(15)/16 product magnitudes also passed `audit-order-eight-a-edges.json`.

The cited continuous-parameter construction now satisfies actual full
distance-three KL for every real parameter (`audit-cited-family-full-kl.json`,
four declarations in two modules). The fixed-ancilla compression matrix
formula and inclusion isometry passed `audit-ancilla-compression.json`.
The separate local gate convention and the surrounding compression-locality
and perfect-code identification prose remain subject to their own review.

New modules identify the literal ket expansions, normalized code projector,
physical raising and lowering matrices, tensor-Y spin flip, spin-flipped
projector trace, full-index real Pauli coefficients, actual occupation sums,
complementary hafnians, and reconstruction equations. The seven- and
nine-triangle parameter solutions are now proved from those triangle
equations alone. The actual raising Gram matrix is identified with the
displayed identity/diagonal/outer-product expression.

The two-qubit excitation rotation is proved unitary and its embedding acts
on the actual six-qubit initial codewords as the certified family. Its Z,
XX, YY, and normalized A1 trigonometric formulas have been reviewed.
The remaining construction/compression and whole-prose steps remain open.

## New qualitative rationalization proof

`MainTheory/WithinSectorRationalization.lean` constructs the actual
within-sector integer system with exactly n physical coordinates. It proves
integer right-hand sides, rational solvability, within-sector constancy,
averaging against the actual sector-projector probabilities, the common phase
shift, and equality of projective action. No finite logical order is assumed.
Compilation and axiom checks passed. `WithinSectorCodeAction` extends the
identity to every vector in the actual code span with an explicit common phase.
`CurrentMainDisplays` checks the revised real-solution color equations and
the five-qubit parameter displays. Their eleven audited declarations use only
the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Singleton qualification: author decision recorded

The new main text removes the previous K >= 2 qualification immediately before
`eq:quantum-Singleton`. Under its stated KL definition, a rank-one frame detects
every operator, so the unqualified real-exponent inequality is false.

`MainTheory/SingletonRankOneCounterexample.lean` has compiled a normalized
three-qubit rank-one code satisfying `SS.HasDistance ... 3`, and proves that the
claimed inequality becomes `1 <= 2^(3-2*(3-1)) = 1/2`, which is false. This uses
integer exponents; truncated natural subtraction must not conceal the issue.

Proposed correction: restore “For codes encoding nontrivial logical information,
K >= 2” before the bound. The existing `QuantumSingleton.quantum_singleton`
proves precisely that corrected scope. The author chose to keep the manuscript
unchanged and record the counterexample and erratum separately. Consequently,
this assertion remains an explicit obstruction to certification of the text
as written; it must not be marked covered by the qualified theorem.
The standalone counterexample and correction record is `errata-20260908.md`.

## Existing cited-construction issue remains under review

The supplementary revision does not change `eq:o7knowntransversal`.
With standard Pauli matrices and ordinary matrix multiplication, the literal
Appendix B.1 construction from arXiv:2504.20847v1 has a gate-convention mismatch
at theta = 0. Exact integer certificates and their complex matrix semantics
have compiled: `FiveQubitCitedGateSemantics.cited_gate_does_not_preserve`.
The actual six-qubit ancilla bridge now compiles, and
`CitedAncillaFamily.paper_gate_fails_at_zero` passes the standard-three-axiom
audit. The proposed S-to-S-adjoint correction now has an actual complex
five-qubit gate-action proof and an all-theta six-qubit codeword-action
proof, with standard-axiom audits (`tmp/audit-five-qubit-corrected-gate-semantics.json`,
`tmp/audit-cited-corrected-family.json`). The actual normalized enumerator
parameter A1=cos(theta)^2 is now proved for every theta and audited
(`tmp/audit-cited-construction-alpha.json`); complete distance-three and
orbit-presentation checks remain in progress.
The fixed logical matrix is now explicitly proved unitary, and the recovery
formula expresses each original codeword in the span of its transformed
words for every theta (`tmp/audit-cited-corrected-logical-gate.json`).
This item is not marked covered and no source correction has been made.

## Outstanding acceptance

The beta-8 development build passed all 1466 modules. The capstone
`BinaryBetaEight.betaEightExact` and `BetaEightValue.betaOf_eight` compiled;
their axiom audits contain only the three standard axioms. The original serial
build and beta-9 certificate build remain in progress.
Development compilation is not a replacement for the final
source-fingerprinted full build. Current-root imports, a final whole-ledger axiom closure,
all remaining assertion/prose reviews and final repository delivery remain open.
