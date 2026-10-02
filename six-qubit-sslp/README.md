# Six-qubit SSLP and general finite-lift certification

The latest manuscript target is `documents/20260924/`. Its version-bound
[acceptance entry point and first review](notes/paper-acceptance-20260924.md)
are available with `python tools/verify.py --paper-version 20260924`.
The new release is not fully certified: its first 19 priority named statements
have review records, while remaining displays and prose still need review.
See the [new named-results map](results/named-results-20260924.md) and
[current errata dispositions](results/errata-20260924.json).

The newest manuscript is `documents/20260929/`. Its supplementary materials
are byte-identical to 20260924, and its main text changes only Sections II and
III, which were rewritten against Bei Zeng's Lean formalization of Section III.
That formalization is included as the [`QECC`](QECC/README.md) library, ported
from Lean 4.28 to this repository's Lean 4.27 without changing any statement
or proof. Its main theorems, such as
`QECC.CodeProjector.general_physicalOrder_bound` and
`QECC.CodeProjector.distanceThree_physicalOrder_bound`, depend only on the
standard three axioms. The claims ledger has not yet been migrated to
20260929, so no 20260929 label is recorded as covered.

The latest proof increment connects the same physical colored lift, solved
binary pivot and actual Smith factor in
[`PaperColoredFiniteLift`](MainTheory/PaperColoredFiniteLift.lean).
It requires only single-site Z detection and uses the original operation's
actual eigenvalue count. The existing GitHub proof trees were checked against
the local committed baseline and nine supporting modules were reused.
See the [comparison, review and validation record](results/colored-lift-smith-20260924/README.md).

The preceding proof increment closes the general SSLP converse for arbitrary
input subspaces. The [paper-facing theorem](MainTheory/PaperGeneralSSLPConverse.lean)
constructs orthonormal frames, proves that their span is exactly the supplied
direct sum, and retains the target KL distance and exact logical order of the
displayed gate. No chosen basis or assumed independence is required from the
caller. See the [review and validation record](results/colored-subspaces-20260924/README.md).

An earlier proof increment closes both minimum-length corollaries: arbitrary
transversal logical order-five gates require at least six qubits, the canonical
class-36 code attains six, and the six-qubit code is unique up to LU/permutation.
The [matrix-level proof](MainTheory/MinimumLengthOrderFive.lean) includes genuine
KL-preserving ancilla padding and the exact weight-one enumerator identity.
See the [scope and verification record](results/minimum-length-20260924/README.md).

The established baseline and coverage counts below concern
`documents/20260908/main.tex` and `documents/20260908/supplementary.tex`,
formalized in Lean 4.27.0 with pinned mathlib. The historical default command
continues to select 20260908; its reviews do not automatically cover 20260924.
**Full manuscript certification is still in progress.**  Four discrepancies
between the manuscript and what is provable are recorded in
[errata-20260908.md](results/errata-20260908.md). One of them,
`eq:quantum-Singleton`, is false as the text stands and has a kernel-checked
counterexample, so main.tex cannot be certified as written until it is
qualified. The fourth points the other way: `supplementary.tex` records orbits
1--4 as unresolved at the existence level, and this development proves they are
realized.

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
starting snapshot against the previous manuscript. The
[20260908 review](results/manuscript-20260908-review.md) and
[closeout progress](results/certification-closeout-progress-20260908.md)
record the current target; the older
[implementation ledger](results/certification-progress-20260905.md) and
[assertion inventory](results/paper-claims-20260905.json) are retained
unchanged. The current [assertion inventory](results/paper-claims-20260908.json)
is tied to the authoritative source hashes; it includes unnumbered displays
and requires a separate review of prose assertions. Unreviewed entries are
not automatically mathematical gaps: many need an existing proof mapped and
checked against their precise statement.

Running text is reviewed separately, because the ledger tracks displays and
named results and a sentence in a paragraph is where an unformalized claim can
sit indefinitely. That review is now done: 1128 prose assertions, each chunk
read by one agent and re-read by an adversarial checker. 396 are carried by a
declaration, 429 restate something the ledger already holds, 121 assert nothing
certifiable, and 182 are gaps. Two are high severity. One is the minimality
claim in the abstract of `main.tex` -- that six qubits is the smallest length
admitting this distance-three realization -- which nothing here proves, since
every declaration in the order-five story is fixed at `ExactCode 6 2 3`. The
other is a fourth erratum, and it points the other way: `supplementary.tex`
records orbits 1--4 as unresolved at the existence level, and this development
proves they are realized. The
[prose review](results/prose-review-20260908.md) lists every gap; it carries no
manuscript text, and its generator refuses to run if the underlying record ever
does.

That inventory is 1.6 MB of JSON, which is the right shape to check against
and the wrong shape to read. The
[named-results map](results/named-results-20260908.md) is the readable face of
it: every theorem, lemma, proposition, corollary, definition and example of
both manuscripts, in document order and grouped by subject, each with the
kernel-checked declarations that carry it and the review that says why, then
the remarks and tables. It is generated by `tools/named_results_doc.py` from
the ledger and re-checked by `tools/verify.py --only named-results`, so it
cannot drift from what the ledger says.

The count is worth breaking down, because the bare number invites the wrong
reading. Of 1588 claims, **none is unreviewed**: 1266 are covered, 320 are
partial, and two are the manuscript's own conjectures, boxed there with a
question mark and not asserted. Every display of `main.tex` and of
`supplementary.tex` has been examined individually -- by a reader who proposed
the Lean declarations that render or prove it, and then by an adversarial
checker who read those declarations and tried to refute the pairing.

The 320 partial entries are not 320 gaps in the mathematics, and the number
rose because review happened rather than because anything broke. Sorted by the
environment each entry came from, they fall out like this.

* **No stated result is partial.** Every theorem, lemma, proposition,
  corollary, definition and worked example in either manuscript is covered:
  32 theorems, 37 lemmas, 40 propositions, 15 corollaries, two definitions,
  one example and one long table, 128 in all, with no partial and no
  unreviewed among them. The 126 of those that are theorems, lemmas,
  propositions, corollaries or definitions are exactly the named results
  `label_sweep.py` sweeps further down, counted a second and independent way.
* **Nine partial entries carry a result name**: five of the fifteen remarks
  and four of the five tables. The remarks' endpoints are all theorems here,
  but their comparative, counting or status sentences have no single
  declaration to point at. The tables record audits -- a face enumeration of
  the orbit-29 simplex, orbit-31 support orbits, angle and fibre-pair counts
  -- that this development either reaches by another means or does not
  perform.
* **The remaining 311 are displayed equations**, and three of those are the
  errata: `eq:quantum-Singleton`, false as written; `eq:o7knowntransversal`,
  where the cited construction's gate convention provably fails to preserve
  the span at theta = 0; and the orbit-9 literal witness, an unlabelled
  display whose printed bit order is ambiguous, certified under one reading
  with the other reading proved inconsistent.

Among those 311 displays, a large group is partial for one specific reason
worth stating plainly: they are steps of a manuscript argument that this
development does not take. Several orbit no-gos here are deliberately repaired
routes -- orbit 26 closes a mixed-axis branch the manuscript passes over,
orbit 30 replaces a two-point magnitude argument with a support-graph one --
so the *conclusion* of such a proof is covered by a named theorem while a
particular intermediate line of the manuscript's own route has no counterpart.
Those entries name the theorem that carries the conclusion and say explicitly
that the step itself is not proved. The rest are displays whose Lean
counterpart covers only part of what is displayed, and local notation that no
declaration introduces because the repaired route never forms it.

A partial entry is therefore an honest record with a declaration and a reason,
not a silence. The rule applied throughout is that a checked declaration has to
carry the *whole* display before the entry is called covered.

`eq:small-beta` is no longer among the partials. All five tabulated
values are exact certificates -- a universal upper bound together with an explicitly attaining
zero-one matrix -- at sizes 5, 6, 7, 8 and 9. The size-nine entry was the last
one open: its whole sign-prefix DAG of 5374 modules had compiled, but the
capstone reading that certificate as `BetaBound 9 120` had never itself been
compiled, so the value could not be claimed. It now compiles, and
`MainTheory.BetaNineValue.betaOf_nine` gives `betaOf 9 = 120`.

Requiring a separate Lean declaration for each such display would be a
category error: the standard is that the *result* is proved, and the named
results are tracked by the label sweep above. The inventory is exhaustive by
design so that nothing is invisible, not because every line of it is an
obligation.

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
label. All 33 named results of `main.tex` and all 93 of `supplementary.tex`
are cited by a kernel-checked Lean statement.

`lem:parity4-edgeisolation` was the last one absent and is now proved. Its
algebra was already there: `edge_isolation_of_character_rows` inverts the
sixteen character sums, and `eq_zero_of_transversal` halves that hypothesis to
the eight rows the manuscript writes down, which is its phrase "the complete
character table of a three-dimensional Boolean group". What was missing was
the manuscript's proviso, that the four effective parity coordinates are
represented by physical single-qubit `Z` characters and the flipped coordinate
by a physical flip. The module `MainTheory/ParityFourProviso.lean` discharges it by
construction rather than assuming it: the effective coordinates are named by
an injection `emb : Fin 4 -> Fin 6`, the physical error carrying an effective
mask is its pushforward `push emb z`, `bdot_push` proves that the physical
dressing computes the effective character, `proj_bxor_push` that the physical
single-qubit flip induces the effective one, and `row_eq_character_sum` that
the Knill-Laflamme row is the effective character sum times a sign -- the
manuscript's "up to row phases". `edgeMasks_eq` identifies the manuscript's
eight errors `X_k`, `Y_k`, `Z_jX_k`, `Z_jY_k` with the masks of weight at most
one away from `k`, and `edgeMasks_transversal` proves those eight meet every
class modulo the all-ones vector. `edge_isolation` is the lemma.

The certified no-gos for orbits 14, 15 and 24 do not route through it. They
carry out the same inversion inline -- `SixQubit/Orbit15.lean` derives its
twelve edge orthogonalities by `linear_combination` with coefficients plus or
minus `1/8` over eight Knill-Laflamme rows, which is the inverse character
matrix written out by hand for that orbit -- so the top-level lemma changes no
certified result.

`lem:q4o26anchorsingular`, `lem:q4o30threepoints`, `lem:q4o30exceptional` and
`lem:q4o30mindegree` were in this list as intermediate steps of manuscript
proof routes the package does not take. They are now proved on the
manuscript's own displayed equations, so the divergence of routes no longer
costs any of them: `MainTheory.Orbit26.anchor_singular` proves
both anchor blocks singular, deriving the reduction `eq:q4o26commonM`, the
cancellation `eq:q4o26FM`, the norm bound `eq:q4o26rnormlarge` and the
state-interchange symmetry rather than assuming them, and
`MainTheory.Orbit30.Data.q4o30_exceptional` and its neighbours carry the
three orbit-30 steps. The
certified orbit-26 and orbit-30 no-gos still run by the repaired route.

`lem:connected-orthogonality` was in this list and is now proved:
`MainTheory.ConnectedOrthogonality.exists_line` gives the manuscript's line,
and `frame_forms_ne` the frame consequence -- the latter without the
manuscript's equal-positive-mass hypothesis, which the inequality does not
need. It is proved but not load-bearing: the certified no-gos for orbits 14,
15 and 24 do not take the manuscript's connectivity route at all.
`SixQubit/ParityFour.lean` says so in its own header and uses a uniform
Lagrange/wedge inequality that never mentions the support. Nothing outside the
axiom audit uses `ConnectedOrthogonality`; it completes the manuscript's
argument rather than participating in the verified chain.

Two clauses that were uncovered inside cited lemmas are now proved.
`lem:o7scalarmoments` has four clauses; its three displayed equations were
proved, its closing sentence -- every active qubit has maximally mixed
one-qubit marginal -- was not. `SixQubit.Orbit7Universal.active_marginal_maximally_mixed` proves it by the
manuscript's own argument: `eq:o7fractionalmatching` makes both occupations of
an active qubit `1/2`, so the `Z_i` scalar vanishes, and the two words sit in
different `ZMod 3` residue shells, so flipping one active coordinate leaves
the shell and the `X_i` and `Y_i` scalars vanish termwise. `lem:o8ladder` has
three displays; the two ladder identities were proved and the third, the
operator equation `eq:o8QP` `QP = rP`, was recorded only as the scalar
identity the argument uses. `SixQubit.Orbit8Universal.QP_eq` states and
proves the operator form, from `Q_eigen` and linearity.

Neither clause enters the verified chain: the certified orbit-7 route reaches
`A_1` through the shadow/MacWilliams squeeze rather than the Bloch-length
identification, and the certified orbit-8 route runs on `Q_eigen` directly.
They complete the manuscript's lemmas rather than the no-gos.

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
`MainTheory.Generated.OrbitTableSemantics31.lp_affine_dimension` on the full-fibre
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
python tools/verify.py --only audit-names
python tools/verification/preflight_merge.py MainTheory.SomeNewModule -o _pf.lean
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
That rejection only happens once the serial build reaches those files, which
is hours in, so `tools/verification/check_audit_names.py` resolves every
`#print axioms` name against the declarations the sources actually introduce
first, in about a second. It is a source-level check and therefore weaker than
elaboration -- it does not know about `export` or macro-generated names -- so a
reported miss is a prompt to look. It found one: an audit line asking for
axioms of a "here" declaration in MainTheory.PaperSupplementaryNoGo -- a word
scraped out of that module's own docstring rather than a declaration, which
would have failed the build. It is named without backticks on purpose, since
this same checker resolves every backticked identifier in this file.
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
- `QECC/`: Section III of the 20260929 manuscript (finite diagonal logical
  groups, SSLP normal form, physical-order bounds), from Bei Zeng's LeanSecIII.
- `tools/`: untrusted candidate generators and acceptance/checking wrappers.
- `results/`: audit and implementation records. The
  [previous README](results/readme-history-before-20260905.md) is retained as
  historical context; its milestone counts and outstanding-work lists are
  not current status.

Explicit manuscript conjectures remain conjectures. The completion target
does not permit adding unproved assumptions, weakening asserted results, or
replacing full intervals with a finite set of witnesses.
