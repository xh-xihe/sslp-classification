# Six-qubit SSLP and general finite-lift certification

This repository formalizes the mathematics of `documents/20260905/main.tex`
and `documents/20260905/supplementary.tex` in Lean 4.27.0, using pinned mathlib.
**Full manuscript certification is still in progress.**

The established six-qubit classification includes 51 excluded moment orbits,
15 realized moment orbits, 11 settled nonempty weight-enumerator images,
the allowed intrinsic projective diagonal group orders, and the unique
projective-order-five code up to the stated local equivalence. The complete
enumerator images of orbits 1-4 remain explicitly open in the manuscript;
their nonemptiness is already proved.

The trust target is the Lean kernel with the standard axiom footprint
`[propext, Classical.choice, Quot.sound]`. External programs may generate
certificates. Coverage, certificate correctness, and their connection to the
actual code and Pauli predicates must be proved in Lean. Numerical sampling
and successful generator execution do not establish a theorem.

## Current coverage and outstanding work

The [initial audit](results/certification-audit-20260905.md) records the
starting snapshot. The [implementation ledger](results/certification-progress-20260905.md)
records subsequent work. The [assertion inventory](results/paper-claims-20260905.json)
is tied to the authoritative source hashes; it includes unnumbered displays
and requires a separate review of prose assertions. Unreviewed entries are
not automatically mathematical gaps: many need an existing proof mapped and
checked against their precise statement.

Newly implemented proof packages include:

- Actual operator-trace semantics for A and B, arbitrary-length homogeneous
  MacWilliams identities, and low-weight A=B from genuine Knill-Laflamme.
- Exact distance three for six-qubit rank-two codes satisfying distance at
  least three.
- The sharp eigenvalue-sector bound under only single-site Z detection.
- Actual real affine support rank at arbitrary length, the same-class sharp
  lift bound, and a sorted normal form retaining the original target distance.
- The full five-qubit irrational/rational finite-lift example, including
  physical infinite order, three- and six-order lifts of the same intrinsic
  class, and minimum primitive lift modulus three.
- General colored SSLP forward and converse statements at arbitrary logical
  rank, exact sector eigenspaces and multiplicities, and all binary moments
  below the target distance on actual sector-projector probabilities.
- Orbit 8's actual raising Gram matrix and complete spectral multiplicities;
  orbit 9's universal magnitude pattern and coefficient counts; orbit 31's
  two-way moment normal form, actual rank 23 and affine dimension 9.
- General active-face LP dimension and rational/real nonnegative feasibility,
  and generic physical full-rank flip-character obstructions.
- Genuine arbitrary local-unitary enumerator invariance and the tensor-product
  representation of the LU equivalence relation, including permutations.
- The general quantum Singleton bound from actual KL detection for logical
  rank at least two, including a proof that its exponent is nonnegative.
- Existence of the complete normalized integral Smith form with an ordered
  divisibility chain and the sharp last-factor interpretation.
- Full parity-four moment geometry, affine dimension four, and actual positive
  support and slice connectivity.
- Both directions of the Knill-Laflamme recovery theorem with actual CPTP
  Kraus maps, including one common recovery for all channels in the error span.
- All four full continuous L interval inclusions and the M interval inclusion
  in both orbits 1 and 4, including every endpoint.
- The manuscript-shaped general colored SSLP normal form and its rank-two
  corollary, each carrying the local `X` conjugation and qubit permutation that
  relate the normal form to the original code, and the computational-basis
  phase-sector lemma stated from code preservation alone, with no distance and
  no `Z`-detection hypothesis.
- The divisibility `q | d_r(C)` against an actual Smith normal form of each
  pipeline pivot, displayed as unimodular `U` and `V` with a positive
  divisibility chain, together with elementary denominator clearing against the
  same number. A witness exists for every nonsingular integer matrix and the
  last factor does not depend on which reduction is used, so no supplied
  witness and no uniqueness caveat remain.
- The manuscript's sixty-six-row orbit order proved a bijection onto the
  internal keys, so the multiplicity table is a statement about all sixty-six
  orbits rather than about the image of a relabelling.
- All six generated active moment-rank tables tied to their certified active
  faces and full-fibre LP dimensions; previously only two of the six were.
- Regeneration of the six moment-rank tables from their generator. Four of the
  six previously on disk could not be reproduced by
  `tools/generators/emit_orbit_table_ranks.py`; the generator is stable
  run to run, so the files predated the current generator or its inputs. The
  regenerated certificates give ranks 23, 23, 21, 17, 23 and 14, each equal to
  the active-column count minus the manuscript's LP dimension for that row.
- Label-facing interfaces for the supplementary no-go results and for the exact
  weight-enumerator images, the order-range corollaries and the parity-four
  geometry.

Manuscript-to-Lean correspondence is tracked by `tools/verification/label_sweep.py`,
which sweeps every named result in the two sources for a Lean source citing its
label. All 30 named results of `main.tex` are cited, and 82 of the 87 in
`supplementary.tex`. Every one of the five that are not is *declared* absent
rather than merely missing, with the reason recorded in the Lean source:

* `lem:q4o26anchorsingular`, `lem:q4o30threepoints`, `lem:q4o30exceptional`
  and `lem:q4o30mindegree` are intermediate steps of manuscript proof routes
  the package does not take. The certified orbit-26 argument is a repaired one
  that closes a mixed-axis branch the manuscript's route passes over, and the
  orbit-30 argument likewise departs from the manuscript's. The headline no-gos
  they serve, `thm:q4o26nogo` and `thm:q4o30nogo`, are proved.
* `lem:parity4-edgeisolation` is not proved. Its algebra now is, in full:
  `MainTheory.ParityFour.edge_isolation_of_character_rows` inverts the sixteen
  character sums, and `eq_zero_of_transversal` halves that hypothesis to the
  eight rows the manuscript actually writes down. That reduction is the
  manuscript's phrase "the complete character table of a three-dimensional
  Boolean group": the overlaps live on the even parity class, the all-ones
  character is identically one there, so a character sum depends only on the
  class of `z` modulo the all-ones vector and eight rows meet every class.
  What remains unproved is the manuscript's proviso -- that the four effective
  parity coordinates are represented by physical single-qubit `Z` characters
  and the flipped coordinate by a physical flip. That proviso is the bridge
  from the six physical qubits to the four effective coordinates, it is what
  turns the Knill-Laflamme rows into these characters, and it is assumed.

`lem:connected-orthogonality` was in this list and is now proved:
`MainTheory.ConnectedOrthogonality.exists_line` gives the manuscript's line,
and `frame_forms_ne` the frame consequence -- the latter without the
manuscript's equal-positive-mass hypothesis, which the inequality does not
need.

One further clause is uncovered inside a cited lemma. `lem:o7scalarmoments`
has four clauses; its three displayed equations are proved, but its closing
sentence -- every active qubit has maximally mixed one-qubit marginal -- is
not. The manuscript uses that sentence to identify `A_1` with a squared Bloch
length; the certified route reaches `A_1` through the shadow/MacWilliams
squeeze instead, so the clause is never needed here.

The sweep counts a label only when a Lean source carries it, and subtracts
labels a Lean source lists after a `NOT-FORMALIZED:` marker, so naming a label
in order to say it is absent cannot be mistaken for proving it. Naming a label
in this file does not count at all. A cited label means a kernel-checked Lean
statement carries it, not that the surrounding prose has been reviewed.

The remaining work includes the upper bounds for beta at sizes 7, 8 and 9,
all table-column semantics, those 23 supplementary steps, the remaining
independent supplementary assertions, the Eastin-Knill statement, and final
manuscript-wide review and rebuild. Orbit 31's LP affine dimension is proved
twice, by `SixQubit.Orbit31.momentPolytope_affine_dimension` on the
thirty-two-coordinate normal form and by
`Generated.OrbitTableSemantics31.lp_affine_dimension` on the full-fibre
pipeline polytope. That duplication is now closed.
`MainTheory.Orbit31Identification.same_fibre_pair` proves the hand
certificate's two sixteen-element word sets are exactly the two masks of the
pipeline pair; `matrixZ_col` checks all 736 entries of the hand-written moment
table against the pipeline's `entryZ` at the corresponding columns; and
`mem_polytope_iff` identifies the two feasible systems, so the two dimension
theorems are two readings of one polytope. The column map is not the
increasing enumeration of each mask -- the hand certificate orders its first
fibre `0, 48, 40, 24, ...` -- so the two presentations differ by a column
permutation, and the map is given in the hand certificate's order.
The detailed ledger takes precedence over older narrative status reports.

Two source corrections were necessary: the Singleton statement now specifies
logical rank at least two, and the supplementary existence paragraph now
distinguishes the four open images from the fifteen already realized orbits.
The [kernel-checked rank-one counterexample](results/certification-audit-rank-one-20260905.lean)
records why the first correction is needed.

## Verification

The complete acceptance command is:

```text
python tools/verify.py
```

It runs a serial build with source/dependency/artifact fingerprints, a
shared-traversal audit using Lean's own `Lean.CollectAxioms.collect`, a source
trust-boundary scan, generated-source checks, current manuscript/table
correspondence, assertion-coverage checks, physical semantic gates and their
mutation controls, and README declaration-name checking. It must fail while
any required assertion is unresolved or unreviewed. No current full-suite
success is claimed.

Use partial diagnostics explicitly:

```text
python tools/verify.py --only axioms sources generated paper gate gate-selftest moments moments-selftest
python tools/paper_claims.py check
python tools/paper_claims.py check --require-complete
python tools/build_lean.py --plan
python tools/build_lean.py --module SS.Basic
```

The build driver runs one Lean process at a time. An old `.olean` or an old
timestamp alone is not a certified cache entry. Failed compilations preserve
prior outputs, while incomplete build runs remain resumable through validated
per-module records. Full and partial verification results are distinguished in
`tmp/verification/report.json`.

The axiom audit reads the current imports and declarations in
`MainTheory/Audit.lean`, `SixQubit/Audit.lean`,
`SixQubit/CodeWrapAudit.lean`, and `SixQubit/Orbit7CollinearAxiomCheck.lean`,
together with explicitly covered claim roots. That last file is an audit file
whose entries were previously collected by nothing.
It rejects absent kernel declarations and any unexpected transitive axiom.
The root count is computed from those current files rather than maintained as
a manually updated number in this README. Axiom cleanliness does not by
itself show that a theorem matches the manuscript's hypotheses and conclusion.

The manuscript files are local research inputs and may not be distributed
with a checkout. Their correspondence check requires the authoritative files,
with `--source-dir` available for the table parser. Do not substitute an older
draft or silently refresh away a changed assertion's review.

## Layout

- `SS/`: bit strings, Pauli actions, Hilbert-space and KL foundations.
- `SixQubit/`: physical orbit proofs, realizations, enumerators and exact
  finite certificate modules.
- `MainTheory/`: arbitrary-length lifting, intrinsic groups, normalization,
  semantic bridges, enumeration and manuscript-facing statements.
- `tools/`: untrusted candidate generators and acceptance/checking wrappers.
- `results/`: audit and implementation records. The
  [previous README](results/readme-history-before-20260905.md) is retained as
  historical context; its milestone counts and outstanding-work lists are
  not current status.

Explicit manuscript conjectures remain conjectures. The completion target
does not permit adding unproved assumptions, weakening asserted results, or
replacing full intervals with a finite set of witnesses.
