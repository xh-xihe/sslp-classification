# Six-qubit SSLP orbits: machine-checked certification

Every one of the **51 no-go moment orbits** of the six-qubit SSLP
classification carries a Lean 4 proof that no exact six-qubit
`((6,2,3))` code arises from it. All 51 are checked by the **Lean kernel alone**
— axiom footprint exactly `[propext, Classical.choice, Quot.sound]`, with no use
of `native_decide` or `sorry` in proof/tactic position.

Start with **`formalization/formalization.pdf`**. It explains what is certified,
the standard it was held to, the no-go mechanisms, orbit-36 rigidity, the ten
realized exact-image stacks, and the errors caught along the way.

## Status

| | |
|---|---|
| No-go modules with a kernel-checked headline | 51, each with a code-level wrapper |
| Of those, matching the paper's target orbit | **51** |
| Lines / theorems in the 51 no-go modules | 41,521 / 12,521 |
| Orbit-36 rigidity chain | 16 modules; original table representative through canonical classification |
| Ten exact realizations | 10 modules, 1,606 lines / 150 theorems, over a 516-line shared layer |
| Shadow bound, universal A/B transform, all ten WE-orbit A/B images and their attainment | kernel-checked |
| Axiom-audit entries | 953 over three audit files, all clean |
| Build errors / warnings | 0 / 0 |

Orbits 25–40 (no 36) and 53–66 were certified first; the twenty-two added in the
next manuscript revision are 5, 6, 12–15, 17–20, 24, 41–44, 46–52. Orbit 66 is in
`SixQubit/Order9.lean`; all others in `SixQubit/Orbit<n>.lean`.

Ten further orbits — 7, 8, 9, 10, 11, 16, 21, 22, 23 and 45 — are certified
*realized*: `SixQubit/Orbit<n>Real.lean` exhibits an explicit pair and proves
`SS.HasDistance ![w0, w1] 3`, so the orbit is nonempty. The amplitudes are
carried in the ring `Z[sqrt 2, sqrt 3, i]` of `SixQubit/Realize.lean` and every
weight-≤2 Knill–Laflamme constraint is decided by the kernel there; the shared
layer transports the decision to genuine complex matrix elements. Together with
orbit 36 that is eleven realized orbits, against 51 excluded and four — 1, 2, 3
and 4 — whose exact enumerator image is still open.

For all ten WE orbits the certification goes past existence to the **exact A/B
weight-enumerator image**.  For orbits 10, 11, 16, 22 and 23,
`SixQubit/Orbit<n>Enum.lean` proves that *every* exact `((6,2,3))` code supported
in that orbit's two fibers has one specific pair, and the realization module
exhibits a code attaining it.
The A-vectors are `(1,1,0,0,15,15,0)` for orbits 11 and 23 and
`(1,0,1,0,11,16,3)` for orbits 10, 16 and 22; the corresponding B-vectors are
`(1,1,0,30,45,33,18)` and `(1,0,1,24,35,40,27)`.  The B half is derived in
Lean from the full seven-row MacWilliams transform in `SixQubit/BEnumerator.lean`.

The argument is a squeeze. The diagonal gate acts logically as `diag(1,-1)`, so
its square is scalar on any code in the orbit; that square is the `Z`-string on
the coordinates where the angle vector is odd, and it fixes the code because its
sign is `+1` on both fibers — a finite condition, decided. A fixing Pauli of
weight `w` forces `A_w ≥ 1` from below; the shadow inequality forces
`A_1 + A_2 + A_3 ≤ 1` from above; the coefficients are nonnegative. Nothing is
left free, and the six-qubit MacWilliams normal form determines the rest.
`SixQubit/Pin.lean` carries the squeeze.

Orbit 21's forced string has weight four, so it is closed by a separate
support-level Walsh/Farkas certificate.  Orbits 7, 8, 9 and 45 require their own
support, moment, phase and constructive-family reductions; those reductions are
also now closed at source-level hypotheses.

## What is certified about each realized orbit, and at what strength

Three different things get called "the orbit is done", and they are not the
same claim. This table keeps them apart.

| Orbit | Source's status | Realized | Enumerator of the exhibited code | **Reaches the source's status** |
|---|---|---|---|---|
| 10, 11, 16, 22, 23 | WE | yes | yes | **yes** — `enumerator_pair_unique_fiber` (A and B) |
| 36 | rigid | yes | yes | **yes** — `Orbit36Certified.table_representative_rigid` |
| 7 | WE | yes | yes | **yes** — exact interval `[0,1]` and a literal rank-two `Tr(P/2)` pair marginal |
| 8 | WE | yes | yes | **yes** — exact interval `[1/2,1]` |
| 9 | WE | yes | yes | **yes** — exact endpoint and the uniform-gauge weight-two scalar |
| 21 | WE | yes | yes | **yes** — code-level full-fibre Walsh/Farkas theorem, A/B, and attainment |
| 45 | WE | yes | yes | **yes** — exact interval `[2/3,1]` from the full-fibre Gram/phase reduction |

All eleven realized orbits reach what the manuscript claims. The last column is the
only one that answers "is this orbit done"; the other two are weaker and are
kept separate because all three get called that in conversation.

A statement reaches the source's status only if its hypotheses are
*code-level*: normalization, support in the two fibers, and
`SS.HasDistance ![c, d] 3`. Orbit 36 did not have that until
`SixQubit/CodeOrbit36.lean` was written — every orbit-36 theorem took its
moment system and twenty-two Knill–Laflamme rows as hypotheses, so it spoke
of amplitude pairs satisfying those conditions rather than of codes. The
fifty-one no-go wrappers had had that bridge from the start; orbit 36 was the
one module without it.

For orbits 10, 11, 16, 22 and 23 the forced `Z`-string has uniform overlap
parity with the whole *fiber*, so the scalar squeeze applies directly.  The
other five use genuinely different complete-fibre arguments: Walsh/Farkas for
21; support and Hafnian reductions for 8; a finite active-support and equal-pair
classification for 9; the covariant `K5` tangent/projector analysis for 7; and
the reduced Gram, phase and two-chart construction for 45.  Their top-level
modules quantify over arbitrary amplitudes on the complete fibres, rather than
only the supports of the exhibited witnesses.

Orbit 21 also records this project's clearest reasoning error and its repair.
The old class-averaging route introduced `a_E = 0` whenever
`A_a(E.x) != 0`. That condition is false even for the certified witness; for
example one label marked `forced` has `normSq (trProj) = 1`. The old conditional
lemmas remain as historical infrastructure, but no final theorem uses that
branch.

The corrected proof expands each squared projector trace into computational-
basis autocorrelations. Only 512 `(X-mask, Walsh-frequency)` pairs can occur for
the two full residue fibres, and the integral residual coefficient has exact
Walsh transform zero on every one. `Orbit21Walsh.lean` checks that finite table;
`Orbit21Residual.lean` proves the Fourier expansion for arbitrary amplitudes;
`Orbit21Farkas.lean` proves
`residual = 32 * (Aco_2 - 4) - positiveRhs`, with every term of `positiveRhs`
kernel-proved nonnegative. `Orbit21Enum.lean` then proves `IsE2A ∧ IsE2B` for
every normalized full-fibre-supported distance-three code and proves attainment
with the explicit realization.

Orbit 45's short manuscript proof has now been expanded into kernel-checkable
content.  The complete ten-point fibres are enumerated explicitly; genuine KL
rows derive the block masses and phase relations; division-free Gram lemmas
cover zero-entry boundary cases; the shadow/MacWilliams layer gives the exact
A/B line and `2/3 ≤ t ≤ 1`.  The converse does not assume a phase ansatz.
For attainment, two explicit real-amplitude charts cover `[2/3,3/4]` and
`[3/4,1]`, returning normalized codewords supported on the two complete fibres
and satisfying genuine `SS.HasDistance` at the requested parameter.  This does
not assert nonzero amplitude at every fibre point (the endpoint `t=1` has
zeros).  Orbits 7 and 8 likewise include explicit continuous families covering
their full closed intervals.

`SixQubit/Shadow.lean` proves the zeroth Rains shadow inequality
`A_1 + A_2 + A_3 ≤ 1`, which is the upper-bound half of the exact-image
theorems for seven of those orbits. The usual derivation builds a spin-flip
operator and a Pauli completeness relation; doing the `Z`-sum first is shorter,
and what survives factors into a sum of squared norms, so nonnegativity needs no
operator, transpose or matrix positivity. `alt_sum_nonneg` holds for every block
length and every number of logical states; `shadow_bound` is its six-qubit
specialization.

Orbit 36 is the only realized orbit whose source status is full rigidity rather
than a weight-enumerator image. `Orbit36Certified.table_representative_rigid`
starts directly from
the representative printed in the manuscript,
`a = (1,1,1,2,2,4)` with residue fibers `(0,1)`, and assumes only support,
normalization and the genuine predicate `SS.HasDistance ![c,d] 3`.  In the
kernel it transports that code to the symmetric gauge, derives the moment and
weight-at-most-two rows, forces every magnitude and full support, composes the
two explicit `CodeEquiv.Equivalent` witnesses to the canonical code, and proves
both enumerators
`A = (1,0,21/25,0,291/25,384/25,79/25)` and
`B = (1,0,21/25,584/25,183/5,984/25,671/25)`.
`table_representative_attained` inverse-transports the canonical code back to
those original fibers, so this strengthened theorem is also non-vacuous.

## Where the source manuscript lives now

Module docstrings, notes and workflow records throughout this repository cite
`six_qubit_sslp.tex` and `six_qubit_sslp_v7.tex`. **Neither is the authority any
more.** `six_qubit_sslp_v7.tex` no longer exists at all; `six_qubit_sslp.tex`
still exists, at `documents/<date>/623/six_qubit_sslp.tex` (12,977 lines), but
was superseded when the manuscript was reorganized in August 2026 and its
contents were split across the files below. The old citations are kept deliberately: they are
provenance for when each module was written, and nothing load-bearing depends on
them, because the datum that actually identifies an orbit is its angle vector,
which `tools/verification/gate.py` checks against `tools/manifest.json` on every
run.

| Cited as | Now in | Contents |
|---|---|---|
| `six_qubit_sslp.tex`, statement of the 66 orbits | `main.tex` §§ on the `((6,2,3))` classification | the 66 SSLP moment orbits, the four classification levels, the filtration `13,877 → ⋯ → 66` |
| `six_qubit_sslp.tex`, the 51 no-go arguments | `supplementary.tex`, eight appendices grouped by projective order `m` | see the table below |
| — (new) | `supplementary.tex` § line 320, *Rigidity of the order-five orbit 36* | the orbit-36 chapter |
| — (new) | `723/transversal_diagonal_lattice_classification_superexponential_ladder.tex` | the umbrella theory paper: projector lattices, SSLP as a normal form, the `β_n` bounds |
| — (new) | `623/orbit1_so5_bd4_c4_construction.tex` | the explicit `SO(5)` family realizing orbits 1, 4 and 45 |

The no-go appendices are grouped by projective order, and the grouping matches
this repository's modules exactly — this is a useful independent check that no
orbit was dropped or double-counted on either side:

| Projective order `m` | `supplementary.tex` appendix | Orbits | Certified here |
|---|---|---|---|
| 9 | Exact nonexistence of projective order nine | 1 | 1 |
| 8 | Exact nonexistence of projective order eight | 2 | 2 |
| 7 | Exact nonexistence of projective order seven | 5 | 5 |
| 6 | Exact nonexistence of projective order six | 4 | 4 |
| 5 | No-go theorems for the other seven order-five orbits | 7 | 7 |
| 4 | Projective order four: complete ten-orbit no-go | 10 | 10 |
| 3 | Exact no-go theorems for order-three orbits 5, 6, 47–52 | 8 | 8 |
| 2 | Exact no-go theorems for fourteen projective-order-two orbits | 14 | 14 |
| | **total** | **51** | **51** |

The manuscripts are a collaborator's unpublished work and are not redistributed
from this repository; see `.gitignore`.

## Status, stated precisely

A collaborator's audit in August 2026 found that three different things were
being conflated. They are now tracked separately:

| Question | Answer |
|---|---|
| Are the Lean headline theorems really kernel-proved? | **Yes.** 953 current audit entries across `MainTheory/Audit.lean`, `SixQubit/Audit.lean` and `SixQubit/CodeWrapAudit.lean`; every footprint is contained in `[propext, Classical.choice, Quot.sound]`, with no escape hatches. Until this was fixed, `tools/verify.py` ran only the first of those three files, so the 592 entries this table used to quote were the ones it was not checking -- `lake build` compiles an audit file, but `#print axioms` reports through `info`, so a bad footprint there failed nothing. The check now walks all three and fails if any of them audits nothing. |
| Do they state what the paper needs? | **51 of 51**, since the repair. Four modules (30, 53, 55, 65) had used a residue of the wrong additive order and were rebuilt from scratch at `delta = q/m`; five more (34, 57, 59, 64, Order9) had moment rows inconsistent with their headline ordering and were regenerated. `gate.py` now reports 51 passed, 0 failed, 0 unchecked |
| Do they rule out a real code end to end? | **All 51 do.** Each has a `no_code` theorem taking only support, normalization and `SS.HasDistance ![c,d] 3` — no KL row is assumed. `SixQubit/Vacuity.lean` exhibits, for **all 51**, a point-mass pair satisfying every other hypothesis, so no statement is vacuous |

The nine defective modules have been repaired and the checks are green. The guard
that should have existed from the start is `tools/manifest.json` (derived from
the paper's own 66-orbit table) plus `tools/verification/gate.py`, which checks
`delta = q/m`, its additive order and both fibers. The separate
`tools/verification/momentgate.py` checks the complete content and ordering of
the declared moment rows:

For the 51 no-go certifications, what remains open is one level up, and it now
has a name. The reduction of an
arbitrary code to one of the sixty-six rank-compatible moment orbits is
*Completeness of the lift-aware SSLP pipeline* (`main.tex`), and the equivalence
of other angle records to the chosen representatives is part of the same
statement. Neither is formalized. So the per-orbit no-gos are complete and
code-level; the classification theorem that assembles them is not.

Three things about that theorem are worth recording, because they change how
large the remaining gap is.

**SSLP is a normal form, not an ansatz.** The umbrella paper extracts two
integer lattices from a code's projector and shows their quotient determines the
whole physical diagonal symmetry group; for one logical qubit the finite
characters are exactly modular subset-sum sectors. The two-fiber problem these
modules solve is therefore the classification's normal form, not a convenient
parameterization of it.

**The enumeration is finite for an elementary reason.** The completeness theorem
rests on a cutoff `q ≤ β_n`, where `β_n` is the largest final Smith invariant
factor of a nonsingular `n × n` binary matrix. At six qubits `β_6 = 9`. That value
needs no table: the last Smith factor divides the determinant, so `β_6` is at most
the maximal `6 × 6` binary determinant, which is 9, and 9 is attained — for
instance by the matrix with rows `100011, 010110, 001111, 101110, 111101, 011010`,
whose Smith diagonal is `(1,1,1,1,1,9)`. Formalizing the upper bound still means
proving the maximal-determinant fact, which is a finite but non-trivial search;
it would narrow the gap, not close it.

**These 51 exclusions are what pins the six-qubit answer.** Every one of the 22
orbits with projective order `m ∈ {4,6,7,8,9}` is among them, so the manuscript's
claim that the possible nontrivial projective orders at six qubits are exactly
`{2,3,5}` rests on this set. The complementary 15 orbits are the realized ones,
and that complement agrees exactly with the manuscript's own table of
realizations, orbit for orbit.

For the repaired residue orbits the correct and previously-used fibers are
disjoint, so the rebuilds are genuinely new proofs rather than relabelled ones;
that is checked by recomputing both fibers from `(q, a)` and confirming zero
overlap.

```sh
python tools/run.py verification/mkmanifest.py   # rebuild the manifest
python tools/run.py verification/gate.py         # enforce it
```

Neither `classify.py` nor `admis.py` could have caught these: the first checks
that no algebraic fact is smuggled in as a hypothesis, the second that every
Pauli row has weight at most two. Both are still worth running, but neither
checks that a module targets the orbit it claims to.

## Verifying, in three commands

```sh
lake build                       # expect 0 errors, 0 warnings
lake build SixQubit.Audit        # expect 592 clean axiom lines (of 953 total)

lake build SixQubit.Audit 2>&1 | grep "depends on axioms" \
  | sed 's/^info: [^ ]* //' | diff - results/axiom-audit.txt
```

The third command must print nothing. That is the complete **kernel dependency
and axiom-footprint** check: because `#print axioms` is transitive, one clean line
per headline theorem certifies its entire dependency cone. It is not, by itself,
the paper-to-Lean transcription check described below.

To confirm the forbidden constructs are absent:

```sh
grep -rn "sorry\|native_decide" SixQubit/ SS/
```

Every hit must be inside a docstring or comment; the exact comment count is not
an invariant. The check that matters is the axiom footprint, not the grep count: an
escape hatch actually used would show up in `#print axioms` as `sorryAx` or
`Lean.ofReduceBool`, and none does.

Toolchain: Lean `v4.27.0`, Mathlib `fc278a179e431ed10630af63fc05481680c0c7bd`,
pinned in `lean-toolchain` and `lake-manifest.json`. Nothing outside Mathlib is
used mathematically.

## Layout

| Path | Contents |
|---|---|
| `SixQubit/` | 51 no-go orbit modules, 13 shared algebra modules, 51 code-level wrappers, the orbit-36 rigidity chain, ten realization modules and their universal exact-image stacks, the audit |
| `SS/` | problem-independent bit-string and Pauli infrastructure |
| `formalization/` | the process document (`.tex` and `.pdf`) |
| `tools/core/` | fibers, Pauli enumeration, moment matrices, relation extractors |
| `tools/orbits/` | per-orbit data and block structure |
| `tools/generators/` | the scripts that emit the Lean modules |
| `tools/verification/` | numerical and symbolic checks independent of Lean |
| `results/` | axiom audit, orbit table, multi-agent workflow records |
| `tools/push-branch.sh` | publishes this tree into the `six-qubit-sslp/` subdirectory of the `sixqubit-classification` branch |

Each `tools/` and `results/` subtree has its own README mapping artifacts to the
claims they support.

## What to read for what

**A reviewer asking "is this actually proved?"** — `results/axiom-audit.txt`,
then the three commands above. Nothing else is load-bearing for soundness.

**A reviewer asking "is the right thing proved?"** — run the checks that
compilation does not perform:

```sh
python tools/run.py verification/gate.py                # paper q/a/m/delta and both fibers
python tools/run.py verification/classify.py            # no smuggled hypotheses
python tools/run.py verification/classify.py --selftest  # known anti-smuggling regressions
python tools/run.py verification/admis.py               # every row is weight <= 2
python tools/run.py verification/admis.py --selftest     # known parser regressions
python tools/run.py verification/momentgate.py          # declared moment rows transcribed correctly
python tools/run.py verification/momentgate.py --selftest   # run its non-exhaustive adversarial suite
python tools/run.py verification/rigidity.py            # the orbit-36 chain, same obligations
python tools/run.py verification/rigidity.py --selftest  # its mutation suite
python tools/run.py verification/realized.py            # the ten realizations vs the manifest
python tools/run.py verification/realized.py --selftest  # its mutation suite
```

`classify.py` confirms every headline hypothesis has exactly one of the three
allowed syntactic forms: an off-diagonal KL row, a diagonal KL row, or the
moment system. An algebraic fact taken as an assumption instead of derived would
void the proof invisibly. `admis.py` confirms every parsed KL row is a genuine
weight-≤2 Pauli and cross-checks that no headline row was skipped; a weight-3
row would silently turn a distance-three no-go into a weaker distance-four
claim. These are fail-closed regression checks for the syntax used in this
repository, not completeness proofs for arbitrary Lean syntax. Both currently
return zero violations across all 51 orbits. `rigidity.py` holds orbit 36 to
the same four obligations — it is the orbit the other gates do not cover,
because it has no `no_go_of_moments` headline — and additionally re-derives the
moment rows from the fibers instead of sharing code with `momentgate.py`, since
two checkers built on one parser fail together.

**A reviewer inspecting the algebraic certificates** — the hypotheses of each
`no_go_of_moments`. A `False` theorem is only as good as its hypotheses, and the
failure mode to look for is an algebraic fact smuggled in as an assumption
instead of derived. Section 6 of the process document reports the hand
classification for the two hardest orbits (31: 46 hypotheses = 33 off-diagonal +
12 diagonal + 1 moment system; 26: 41 = 24 + 16 + 1; zero smuggled in either).

**A collaborator continuing the work** — `formalization/formalization.pdf`
Sections 3–4, then `tools/core/kl.py` and `tools/core/relgen.py`. Section 5
documents a tooling bug that gated three orbits for a long time; Section 6 records
the broader error audit. The invariant
that catches it is that the admissible Pauli count must be
`154 = 1 + 6*3 + 15*9`.

**Someone writing the paper** — Section 4 for the four hard orbits. The
arguments obtained here are shorter than the manuscript's, and for orbits 26 and
31 they avoid machinery the manuscript needs (matrix inverses and a genericity
argument; a 16-type support classification). The final “Open items” section
states the remaining boundary.

## The general theory of `main.tex`

Everything above certifies the *Supplementary Materials*: the six-qubit
enumeration, orbit by orbit. Those results are all conditional on a code being
in SSLP normal form -- supported in two modular fibers of an angle vector. The
companion paper `main.tex` is what justifies that normal form, and it is a
different kind of mathematics: statements quantified over all `n`, `K` and `d`
rather than finite checks at `n = 6`.

`MainTheory/` is the beginning of that half. It is a separate Lean library, held
to the same standard: `lake build` clean, no `sorry`, no `native_decide`, every
result audited to lie inside `{propext, Classical.choice, Quot.sound}`.

`MainTheory/Rationalize.lean` carries the linear-algebraic core of the paper's
qualitative finite-lift theorem: a linear system whose coefficients and
right-hand side lie in a field `K`, and which is solvable over an extension `L`,
is solvable over `K` itself. The paper proves this by choosing a nonsingular
square submatrix and inverting it, which needs determinantal rank and the
invariance of rank under field extension -- neither of which Mathlib has. The
proof here instead retracts the structure map `K -> L`, which exists because `L`
is a `K`-vector space, and applies it coordinatewise. It is shorter, holds for
an arbitrary field extension, and uses no rank theory. A companion lemma records
the other half of the paper's step: a coordinate at which the kernel vanishes
takes the same value in every solution, which is what protects the colour
coordinates.

`MainTheory/Denominator.lean` carries the step the paper states without proof
just after its eq. 2.31: that minimality of the clearing integer `q` forces
`gcd(q, a_1, ..., a_n) = 1`, i.e. that the lift is primitive. The descent is one
line once `q` is identified as the lcm of the denominators.

`MainTheory/Gate.lean` supplies the object all of `main.tex` is about and which
the repository previously lacked in any form: the diagonal gate `D(a;q)`, its
subset-sum eigenvalue, and the equivalence the paper uses everywhere without
proving it -- that the angle vector is primitive exactly when the gate's physical
order is `q` rather than a proper divisor. The subset-sum residue itself was
already here as `SS.weight`, already generic in `n`. The argument stays inside
`ZMod q`, turning the eigenvalue condition into a linear condition on residues
before any natural-number divisibility appears, which sidesteps the usual
`ZMod.val` bookkeeping.

`MainTheory/PhaseSector.lean` is Lemma 2.3, and it closes a real gap in what
this repository proves. Every theorem in `SixQubit/` opens by *assuming* its
logical word is supported in a residue fiber. What licenses that is
`support_of_eigen`: given only the physical hypothesis -- that the diagonal gate
acts on the word as a scalar -- the fiber support follows. `eigen_iff_ssCondition`
records that the two conditions are in fact equivalent, and
`support_of_ssCondition` translates into the exact contrapositive shape the
six-qubit modules use, so the claim is checkable rather than rhetorical.

The paper proves Lemma 2.3 for arbitrary logical dimension, via the spectral
theorem for a unitary operator. Mathlib has only the Hermitian case, so that
route is closed. It is also not needed: Theorem 2.6, the two-fiber normal form,
uses the lemma with `K = 2` and with the logical eigenbasis already chosen, and
there the diagonalization is a hypothesis rather than something to produce. That
is the version formalized.

`MainTheory/Normalize.lean` carries the three moves Theorem 2.6 opens with.
`weight_bxor` turns the paper's sentence that a local `X` conjugation "changes
selected signs and a common scalar only" into an equation: flipping the bits of
`x0` negates exactly the angles at those coordinates and shifts every residue by
`A_a(x0)`. That identity is also the source of the Boolean-cube equivalence the
six-qubit classification quotients by. `addOrderOf_dvd` is `m | q`. And where
the paper builds a unit of `Z_q` inverting `c` modulo `m` prime by prime and
recombines by the Chinese remainder theorem, `ZMod.unitsMap_surjective` is that
statement outright, so the proof is three lines.

`weight_bxor` is re-checked by the kernel on all 4096 pairs for a concrete angle
vector. It is exactly the kind of identity where a sign error in the flip and a
matching error in the shift would cancel and still typecheck.

`MainTheory/Cyclic.lean` is the character `chi(x) = zeta^x.val` on `Z_q`, which
is the algebraic content the rest of the paper leans on without naming: the
gate's eigenvalue on a fiber is `chi` of that fiber's residue. Once it is
available and shown faithful, two of the paper's steps become one line each.
`chi_pow_eq_one_iff` identifies the projective logical order with the additive
order of the residue gap -- which is what makes `m | q` a theorem rather than a
convention -- and `isCyclic_of_faithful` is the paper's "every finite subgroup
of `U(1)` is cyclic", which Mathlib proves for any integral domain.

`MainTheory/RankTwo.lean` assembles those into Theorem 2.6, the two-fiber normal
form -- the result that licenses everything the six-qubit development does.
`normal_form_core` is the geometric content of the forward direction: the phase
sector lemma puts each logical word in a fiber, the local `X` conjugation moves
the first to residue zero, and the residue character identifies the projective
order. `order_of_two_fiber` is the converse's arithmetic core, complete.
`exists_unit_mul_eq_div` is the coprime-power step that puts the second fiber at
`q/m`.

That last one is there because an adversarial audit of an earlier draft caught
it being dropped. The draft filed it under "the quotient by equivalences" and
omitted it as bookkeeping. It is not bookkeeping: it is a proved arithmetic
lemma, and it is the only reason the paper may write `S_{q/m}` rather than
`S_{(q/m)c}`. The same audit caught a docstring claiming that
`addOrderOf delta | q` was the paper's `m | q`. In `ZMod q` that is Lagrange,
true of every element, with no reference to a gate or a code; the paper's `m | q`
runs through the entire rationalization chain. The theorem is now named
`addOrderOf_dvd_q` and its docstring says which one it is not. The module
docstring lists every omission in full, including several the first draft did
not admit to.

`MainTheory/Clearing.lean` is Lemma 3.1, and it closes one of the three
blockers -- partly, and for the part that actually matters. The paper clears the
denominators of `C^{-1} h` with the sharp multiplier `d_s(C)`, the last
invariant factor, and sharpness is what the constants `beta_N` measure. Mathlib
cannot supply that: `Module.Basis.SmithNormalForm` records no divisibility chain
and there is no uniqueness of invariant factors. But the *qualitative* statement,
which is what Theorem 2.4 actually uses and the reason the lift is finite at all,
needs no Smith theory: `det(C) * C^{-1} = adj(C)` is an integer matrix, so the
determinant clears everything. `exists_cleared_of_real` then composes this with
`Rationalize` to give the paper's step end to end -- real angles in, a finite
denominator out.

So the Smith blocker is narrower than it first looked. It obstructs only the
numerical bound `q <= beta_n`, not the finiteness of the lift.

`MainTheory/Covariance.lean` and `MainTheory/AffineSpan.lean` are Lemma 5.2, the
common affine-span lemma, split along its natural seam. The geometric half --
that for strictly positive weights the covariance form vanishes on a direction
exactly when that direction annihilates the centred support -- mentions no codes
at all and is stated for an arbitrary finite weighted point set. The quantum
half turned out to be already present: `SixQubit/CodeBridge.lean` proves the
equality of first and second occupation numbers for a distance-three code, and
both are generic in `n` despite living in the six-qubit namespace, so the common
covariance is two rewrites away.

Splitting it that way is the point. It makes visible exactly how much of the
lemma is about quantum codes, which is: the moments, and nothing else.

What is not done is the passage from equal centred spans to
`aff(T_0) = mu + V = aff(T_1)` as a statement about Mathlib's `AffineSubspace`.
That is bookkeeping over an API rather than mathematics, and it is left open
rather than claimed.

`MainTheory/D3Bound.lean` is Theorem 5.3's rationalization. The paper builds the
rational representative by a pivot construction; that construction exists to make
the bound *sharp*, and for the qualitative conclusion -- that a rational
representative exists at all, which is what makes the lift finite -- `Rationalize`
supplies it directly. What this module adds is the equivalence step: two
solutions of the same row system agree on the whole row span, and the affine-span
lemma puts both logical supports inside it. The numerical bound `q <= beta_n` is
not proved and is the one part that genuinely needs the sharp invariant factor.

`MainTheory/Levels.lean` and `MainTheory/WImages.lean` are level (iii) of
Definition 6.1, the weight-enumerator image `W_r`, and its evaluation. All ten
realized orbits now have their `W_r` evaluated as a Lean theorem, stated in the
paper's own terminology rather than in the ad-hoc form the six-qubit modules
use: orbits 9, 10, 11, 16, 21, 22 and 23 to a single point, and orbits 7, 8 and
45 to the image of an interval under the family map, `F_I` on `[0,1]` and
`[1/2,1]` and `F_II` on `[2/3,1]`.  That is Result III of `main.tex` in full. The mathematics was already finished; what is
new is that `main.tex`'s definition is a Lean object those results are about.

The other three levels of Definition 6.1 are not defined, and the module says
which and why: level (i) needs the projective diagonal group as a group object,
level (ii) needs the Boolean-cube action on labelled fiber data, level (iv) needs
local unitaries acting on projectors and there is no operator layer.

All thirteen modules exhibit their hypotheses as satisfiable rather than merely
unrefuted. `rationalized_pi_solution` rationalizes an actual irrational solution;
`lcmDen_example` computes a concrete least denominator; `lift_exists` records
that every rational phase vector really does have a lift. The gate layer carries
a control in each direction: orbit 21's angle vector `(1,1,1,2,2,3)` at `q = 4`
is proved primitive and its gate proved to have exact order four, while an
all-even vector at the same `q` is proved *not* primitive -- without that second
one, `Primitive` could be a predicate that holds everywhere and the order theorem
would say nothing. The kernel checks the
proof, not the statement, and this repository has already paid once for
forgetting that.

### What blocks the rest

Three obstacles were found by reading the paper against the pinned Mathlib
(rev `fc278a17`), and they are recorded here rather than discovered again later.

The constant `beta_6 = 9` is what specializes the general bound to six qubits:
it is the number that makes the 66-orbit list exhaustive. The paper supports it
with the words "complete binary-matrix tables give" and no proof. Bounding the
largest invariant factor over all nonsingular 6x6 binary matrices means `2^36`
matrices, or `6.8e7` after discarding repeated and zero rows, which is far
beyond `decide`, and the Hadamard bound only gives 14.

This obstacle is closed. `MainTheory/BinaryBetaSixCanonical.lean` reduces the
maximum to weakly increasing angle six-tuples in range, and a sharded coverage
tree over `Fin 8` discharges those in the kernel:
`Generated.BinaryBetaSixKernel.Certificate.upper : BetaBound 6 9`, with
`betaExact` adding attainment, both inside
`{propext, Classical.choice, Quot.sound}`. The same route gives
`BetaExact 4 3` and `BetaExact 5 5`. Of the paper's `eq:small-beta`, that
leaves `beta_7 = 18`, `beta_8 = 42` and `beta_9 = 120` unproved: the coverage
tree has to range over `Fin 19` and wider tuples, which is a larger computation
rather than a different one. At `d >= 3` the relevant constant is `beta_6`, so
nothing in the six-qubit development waits on them. The paragraph below is kept
because it records what the bound is and is not needed for.

It is important to be clear about what this does and does not block. The general
theorem `thm:d3-bound` states `q | d_r(C)` and `q <= beta_r <= beta_n` with
`beta_n` *defined* as that maximum; the inequality is then immediate and the
value of `beta_6` is not needed to formalize it. Only the six-qubit
specialization -- Result I's `M_3(6) = 5`, and the exhaustiveness of the orbit
list -- uses the number. The paper cites it as a computation rather than proving it; this development
proves it, so it is a theorem here rather than an input. Downstream statements
that only need *some* bound take one as a parameter, and the certified value is
supplied where the sharp six-qubit form is wanted.

What actually blocks `thm:d3-bound` is the next item, not this one.

Mathlib's Smith normal form carries no divisibility chain --
`Module.Basis.SmithNormalForm` has no field asserting `a i` divides `a (i+1)` --
and no uniqueness of invariant factors, which the paper's notation `d_i(C)`
silently assumes and never proves. This turned out to block nothing.
`MainTheory/Clearing.lean` gets the qualitative denominator clearing from the
adjugate, and `MainTheory/SharpClearing.lean` gets the sharp multiplier from
the rational inverse directly -- `inverseDenominator`, which needs only
nonsingularity, and which `inverseDenominator_eq_smithLastFactor` identifies
with `d_s(C)` whenever a Smith witness is available. Since `beta_N` is defined
through `inverseDenominator`, the numerical bounds never pass through Smith
normal form at all.

The paper's finite-projective-group theorem is compact-Lie-group theory, and
Cartan's closed-subgroup theorem is absent from Mathlib entirely. That blocked
the paper's proof, not the theorem: at `K = 2` and `d = 3` finiteness is now
proved at arbitrary `n` by a different route, in which a bound on the modulus
of a class representative makes the group inject into a finite type. The
substitute runs on the distance-three rationalization, so `d = 2` and `K > 2`
still need the Lie-theoretic argument. Everything else in the rank-two normal
form is proved at the paper's own `d >= 2`.

Mathlib also has no spectral theorem for unitary or normal operators, only for
Hermitian ones, which is what the phase-sector lemma needs.
`MainTheory/UnitarySpectral.lean` proves the unitary case here rather than
routing through two commuting self-adjoint parts, and
`GeneralSpectral.spectralExtractionPrinciple` is the consequence the rest of
Section II uses.

## Statement-by-statement status of `main.tex`

Every numbered statement in the paper, with what is proved and what is not.
"Done" means a kernel-checked Lean theorem inside `{propext, Classical.choice,
Quot.sound}`; anything else is spelled out.

`python tools/verify.py` checks that claim end to end -- the whole package
builds with no errors and no warnings, every audited declaration's axiom set is
inside those three, no `sorry`, `native_decide` or `axiom` declaration occurs
outside a docstring, and every Lean name this file cites exists.  It exists
because a hand-rolled grep once reported a broken build as clean: `lake` prints
failures as `error:` at the start of a line, and the exit code is what settles
it.

| # | Statement | Status |
|---|---|---|
| 2.3 | `lem:phase-sectors` | **Done at arbitrary `K`** (`PhaseSector`, `GeneralSpectral`), with `sectorSupport`, `sectorProbability` and `sectorMean` defined as the paper's `T_alpha`, `p_alpha` and first moment, so `eq:Talpha`, `eq:palpha` and `eq:common-mean` are matched literally rather than in spirit; `SectionTwoGeneral.phaseSectors_mean` supplies the value `mu_j = (1 - lambda_j)/2`. The logical eigenbasis is no longer a hypothesis: `GeneralSpectral.spectralExtractionPrinciple` produces it for all `n`, `K`, `d`, on top of the unitary spectral theorem proved in `MainTheory/UnitarySpectral.lean` -- Mathlib has only the self-adjoint case, and the proof here diverges from it by using `Module.End.exists_eigenvalue` in place of the Rayleigh quotient. |
| 2.4 | `thm:qualitative-finite-lift` | **Done at general `(n, K, d)`**, and stated whole as `QuantitativeGroup.qualitative_finite_lift`: a primitive `D(a;q)` with `q >= 2`, a projective logical order `m >= 2` with `m | q`, and a nonsingular zero--one pivot of size `s = rank R <= n+t-1` whose denominator invariant bounds `q_min`. The pieces are `SectionTwoGeneral.qualitativeFiniteLift` (and `..._of_nontrivial` under the paper's own hypothesis), `GeneralLiftOrder`, and `PivotSize`; `GeneralLiftOrder.sector_in_fibre` is `eq:sector-contained-fiber` at arbitrary rank. The rationalization is `RealGate`, `Rationalize`, `Denominator`; the paper's pivot construction is replaced by a retraction argument that needs no rank theory, and the pivot bound `s = rank R <= n+t-1` is proved separately and unconditionally as `PivotSize.exists_pivot_rank_le` with `PivotSize.card_eq_rank`. `eq:qualitative-m-divides-q` is `GeneralLiftOrder.orderOf_dvd_of_hasPrimitiveLift`, also at general `K` and in the paper's sharp form -- `m` divides the modulus of *any* primitive lift, not only of the one the rationalization produces; it had existed only as a field of the rank-two certificate. The paper's `q_min` of `eq:qmin` is `GeneralLiftOrder.qMin`, with `qMin_spec` and `qMin_le` saying it is attained and minimal; Section II's claim about it is that the set is nonempty (`exists_hasPrimitiveLift`), which is what is proved. |
| 2.5 | `thm:finite-projective-group` | **Done unconditionally at arbitrary rank and the paper's own `d >= 2`** (`ProjectiveGroupGeneral.whole`). The obstruction was one instance: every cyclicity route in the repository takes `Finite (IntrinsicGroup C)` as a hypothesis, and the only unconditional supplier was typed at `ExactCode n 2 3`, so the whole `K > 2` branch and the whole `d = 2` branch stalled on it. An earlier note here said that needed Cartan's closed-subgroup theorem; that was wrong. `GeneralFinitenessRank.finite_intrinsicGroup` supplies it at arbitrary `(n, K, d)` with `2 <= d`, from material that was already general: `QuantitativeGroup.quantitative_projective_group` is stated at arbitrary `(n, K, d)`, `BetaExists.betaBound_betaOf` gives a `BetaBound` at every size, and `FiniteGateAsPhase`'s label lemma turns a modulus bound into a `BoundedPhaseLabel` on a bare local phase. Only `BoundedRepresentation` was typed at `K = 2`, decoratively, and is now stated at arbitrary `K`. The sharp value does not generalize: the bound is `beta_{n+K-1}`, not `thm:d3-bound`'s `beta_n`. What the row used to say follows., stated whole as `FiniteProjectiveGroup.whole` -- finite, abelian, every class has a primitive finite lift, and every class's order divides every such lift's modulus. The lift clauses hold at arbitrary rank (`FiniteProjectiveGroup.lifts`); only finiteness is restricted, and `whole_of_finite` takes it as a hypothesis exactly where the paper appeals to compact Lie theory. The finiteness itself is `GeneralFiniteness.finite_and_abelian`, by a route the paper does not take: every class has a representative whose modulus is bounded, so the group injects into a finite label type. That route runs on the distance-three rationalization, so it gives nothing at `d = 2`, and nothing at `K > 2`; there the paper's own proof is the only one, and it stays out of reach -- compact-Lie-group theory, with Cartan's closed-subgroup theorem absent from Mathlib, no Lie algebra of a group, and no `PU(K)`. |
| 2.6 | `thm:rank-two-sslp` | **Done at arbitrary `n`, forward and converse, now including `eq:a-canonical`.** `RankTwoSSLPCanonical.rank_two_sslp_canonical` returns a `SortedNormalForm` whose fields are the theorem clause by clause: `sorted` and `lt_q` are `0 <= a_1 <= ... <= a_n < q`, `primitive` is `gcd(q, a) = 1`, `leftFiber` and `rightFiber` are `eq:0L-fiber` and `eq:1L-fiber`, `hasDistance` is the genuine Knill--Laflamme predicate, and `source_span` with `frame_eq` are the local `X` conjugation and the qubit permutation. It is a separate file because `SortedNormalForm.lean` imports `RankTwoSSLP`, so neither could host it. Cyclicity is now at `d >= 2` over `ProjectiveGroupGeneral`. What the row used to say follows. The two-fibre half holds at the paper's own hypothesis `d >= 2` (`RankTwoSSLP.two_fibre_normal_form`, and `..._of_nontrivial` under the paper's hypothesis on the group rather than on a chosen phase vector). Cyclicity needs finiteness, exactly as the paper's proof does: `cyclic_of_finite` at general `d`, discharged at `d = 3` by row 2.5, giving the whole statement as `RankTwoSSLP.rank_two_sslp`. `GroupOrder.rank_two_sslp_generator` runs it on a *generator*, so the modulus that comes out is `Nat.card` of the group -- the paper's `m` in `C_m`. The sorted form `0 <= a_1 <= ... <= a_n < q` with `gcd(q,a) = 1` is `SortedForm.exists_sortedNormalForm`, also at `d >= 2`. All four of the theorem's normalizations now have semantic transports: `FlipSemanticTransport` (local `X`), `PermutationSemanticTransport` (qubit permutation), `UnitPowerSemanticTransport` (coprime power) and `InterchangeTransport` (logical-state interchange, which had been absorbed into an existential rather than stated). The converse is `SSLPConverse.sslp_converse` -- `RankTwo.order_of_two_fiber` alone is only its spectral half, since its conclusion is about scalars and builds neither the code nor the group element (see row 4.2). The `d = 2` finiteness this row used to name as the remaining gap is closed by row 2.5. |
| 3.1 | `lem:denominator-clearing` | **Done, sharply** (`SharpClearing`). `solution_lcmDen_dvd_inverseDenominator` is the lemma with the sharp multiplier and needs only nonsingularity; `inverseDenominator_eq_smithLastFactor` identifies that multiplier with the paper's final Smith factor `d_s(C)` for any matrix carrying a `SmithWitness`, so the divisibility is about `d_s(C)` and not a relabelling. Mathlib supplies no Smith normal form with a divisibility chain, so witnesses are built here; nothing downstream needs one. |
| 3.2 | `thm:colored-finite-lift` | **Done at arbitrary `(n, K, d)`** (`ColoredBound.quantitative_colored_finite_lift`): a primitive rational lift inducing the same projective action, with `q <= beta_{n+t-1}`; `m | q` for *any* primitive lift is `GeneralLiftOrder.orderOf_dvd_of_hasPrimitiveLift`, and `q | d_s(C)` is `FiniteLift.sharp_pivot_divisibility_smith`, with `sharp_pivot_divisibility` the witness-free form against `inverseDenominator`. The pivot size `s = rank R <= n+t-1` is `PivotSize.exists_pivot_rank_le` with `PivotSize.card_eq_rank`. |
| 3.3 | `cor:quantitative-projective-group` | **Done at arbitrary `(n, K, d)`, both sentences.** The sharp one -- an element with `t` distinct logical eigenvalues admits `q <= beta_{n+t-1}` -- used to be `exists_sectorCount_qMin_le`, which quantified `t` existentially and tied it to nothing, so it was the coarse bound wearing the sharp one's name. The gap was a single `Classical.choice`: `SectionTwoGeneral.resolutionOf` picks some resolution and its `sectorCount` is then opaque. `SharpSectorBound.hasPrimitiveLift_le_beta_sectorCount` routes through the canonical resolution instead, whose `sectorCount` is by definition `Fintype.card (SectorIndex hpres)`, the eigenvalue count itself. Two lemmas were freed of the choice for it, both by adding a resolution argument their proofs already only used the fields of. What the row used to say follows. (`QuantitativeGroup.quantitative_projective_group`): finite order, a primitive lift, `m | q` and `m <= q <= beta_{n+K-1}`; `qMin_le_beta` says `q_min` obeys the same bound. It does not go through 2.5 -- finite order of one element follows from its having a finite lift, not from finiteness of the group. `t <= K` is `SectionTwoGeneral.sectorCount_le`. |
| 4.1 | `cor:K2-q-bound` | **Done at the paper's own `d >= 2`, both sentences** (`ProjectiveGroupGeneral.k2_bound_and_cyclic`). The bound half was already there; the cyclicity half needed finiteness at `d = 2`, which row 2.5 now supplies, so `cyclic_of_rank_two` holds at `d >= 2` rather than at `d = 3`. What the row used to say follows. (`QuantitativeGroup.k2_q_bound`): `m | q`, `m <= q <= beta_{n+1}`, and `q_min <= beta_{n+1}`. Cyclicity and the two-fibre normal form, the corollary's other clauses, need finiteness and so hold at `d = 3`: `RankTwoSSLP.rank_two_sslp`.**The table `eq:small-beta` is now covered further than before, and where it is not is now recorded.** The paper tabulates `beta_5 = 5`, `beta_6 = 9`, `beta_7 = 18`, `beta_8 = 42`, `beta_9 = 120`, and cites `beta_7 = 18` as the general distance-two six-qubit cutoff of `eq:6qubit-d2-bound`; this package had `BetaExact N` only for `N = 1, ..., 6`, so the last three values entered nothing. The attainment halves are now kernel theorems -- `BinaryBetaSevenLower.betaSevenAttained`, `BinaryBetaEightLower.betaEightAttained` and `BinaryBetaNineLower.betaNineAttained` -- found by hill climbing on the inverse denominator, each reaching the tabulated value exactly, which is independent corroboration of the table. They avoid the determinant entirely: the integer matrix `clearedInverse = beta * A^{-1}` and the single identity `A * clearedInverse = beta * I` exhibit `A^{-1}` over the rationals, give `det A != 0` through `Matrix.det_ne_zero_of_right_inverse`, and make `beta` a universal clearing multiplier; at size nine no single inverse entry has denominator 120, so two of them are combined by `Nat.lcm_dvd`. The **upper** halves `BetaBound 7 18`, `BetaBound 8 42` and `BetaBound 9 120` are not claimed, and the obstruction is not the size of the coverage tree. The pattern count barely moves -- 1716 weakly increasing six-tuples of three-bit column patterns become 3432 seven-tuples (`multichoose(8,7)`) -- but the *leaf* argument breaks. At six variables `laplace33Grouped` writes the determinant as twenty complementary pairs of `3 x 3` minors, the bottom ones bounded by two in absolute value, and the tree tightens the resulting crude bound down to nine. At seven the same split gives thirty-five pairs against `4 x 4` bottom minors bounded by three, so the crude bound is an order of magnitude above eighteen rather than a factor of two, and the tree would have to be far deeper to close it. That looks like it needs a new argument -- a genuine bound on the largest invariant factor of a binary matrix -- rather than more compute. So `q_min <= beta_7` is proved and `beta_7 = 18` is proved only from below. |
| 4.2 | `thm:d2-sslp-classification` | **Done** (`SortedForm.d2_sslp_classification`), at the paper's own `d >= d0 >= 2`: the sorted two-fibre normal form with `2 <= q <= beta_{n+1}`, `m | q`, `m >= 2`, `0 <= a_1 <= ... <= a_n < q`, `gcd(q,a) = 1`, and the Knill--Laflamme system. The record's `m` is pinned to an actual group element's order (`m_isOrder`), `q` and `m` are the *exact* physical and projective orders of the displayed gate (`physicalOrder`, `projectiveOrder`), and the fibre conditions are shown to be the operator statement (`gate_left`, `gate_right`: `D(a;q)` fixes the first logical word and scales the second by `omega_q^{q/m}`). The bound arrives because `rationalLift` is now the pivot lift of `ColoredBound` rather than an arbitrary choice, so everything built downstream of it inherits `q <= beta`; `SectionTwoGeneral.sectorCount_eq_two` supplies the `n+1`. **The converse is now proved at arbitrary `n` too** (`SSLPConverse`). The theorem's closing sentence -- "every orthonormal pair of the displayed form satisfying those complete equations defines such a code, and `D(a;q)` induces a projective logical element of order `m`" -- had only its spectral half, `RankTwo.order_of_two_fiber`, whose conclusion is about scalars and mentions neither a code nor a group element; its own docstring says orthonormality is not imposed. `SSLPConverse.codeOfPair` builds the code, `resolutionOfPair` the finite generator (projectively nontrivial exactly because `m >= 2`), and `orderOf_intrinsicClass_resolutionOfPair` computes the order of its class in the intrinsic projective diagonal group to be `m` on the nose. |
| II.F | `sec:fixed-sector` (the moment LP) | **Both directions done.** `SixQubit.occOn_eq_of_hasDistance` and `occ2On_eq_of_hasDistance` derive `eq:LP-first` and `eq:LP-second` from distance three -- the direction the no-gos need, and the only one that was stated. `MomentEquivalence` adds the converse the paper asserts ("is equivalent to"), which is what makes the linear program a reformulation rather than a relaxation, and `lp_normalization_and_positivity` supplies `eq:LP-normalization` and `eq:LP-positive`. |
| 5.2 | `lem:common-affine-span` | **Done in full** (`Covariance`, `AffineSpan`), split into a general convexity half and a quantum half that was already in `SixQubit/CodeBridge.lean`. `span_eq_of_cov_eq` closes it: equal covariances give equal centred spans, via the dual annihilator. |
| 5.3 | `thm:d3-bound` | **`six:eq:qbetar` done -- `q <= beta_r` at the affine rank of the code's own support** (`SupportAffineRank.q_le_threshold_supportAffineRank`), not merely `q <= beta_n`. Earlier in this work the sharper form was given up on and the coarse filter's soundness routed around it instead, through 422 Farkas separators. It is provable by the paper's own argument: `thm:d3-bound` opens with a local `X` conjugation putting `0^n` into `T_0` (`eq:zero-in-T0`), which makes the common affine span linear so that `r` is the affine and the linear rank at once. Without a supported zero word only one fewer difference vector than the pivot's rank lies in the affine direction, and one gets `beta_{r+1}`; with it the pivot's own vertex points do, and one gets `beta_r`. The key -- `RankTwoGlobal.TwoFiberCertificate.base_supported` -- was already in the tree, added for an unrelated purpose. **What is still open is the same theorem's other clause**, `q | d_r(C)` with `d_r` the last Smith invariant factor: the chain `q | inverseDenominator P.matrix` and `inverseDenominator C = w.lastFactor` is complete, but `w` is a `SharpClearing.SmithWitness`, which asks for unimodular `U` and `V` over the integers with `U C V` diagonal *and* the divisibility chain, and nothing in this repository or in Mathlib builds one. An earlier version of this row said Mathlib "cannot", which is too strong: `Submodule.smithNormalForm` does give a basis-level Smith form for a submodule of a finite free module over a PID. Two things separate it from a `SmithWitness`. It returns bases rather than matrices, which is a change-of-basis argument away; and it does not expose the divisibility chain `a_1 | a_2 | ... | a_n`, which is what makes the scalars *invariant factors* -- the chain is what `Submodule.basis_of_pid_aux` is proving internally, so it is recoverable, not absent. The third step, `lastFactor = inverseDenominator`, is the easy one: `C^{-1} = adj(C)/det C`, so the sharp denominator is `|det C|` divided by the gcd of the cofactors. The rationalization and the `beta_n` bound follow. (`D3Bound`, `BetaExists`, `GeneralFiniteness`), including the agreement-on-the-row-span step: every projective class of an exact `((n,2,3))` code has a representative of modulus at most `beta_n`, with `beta_n` the maximum inverse denominator over nonsingular binary matrices of size at most `n`. The named form is `D3BoundedNormalForm.d3_bound`: a primitive finite generator on the code itself with `2 <= q <= beta_n`, `m | q` and `m >= 2`. The `q | d_r(C)` clause is proved for both pivots against `inverseDenominator` (`FiniteLift.sharp_pivot_divisibility` for the coloured one, `D3FreshSparseAssembly.FreshSparsePhase.order_dvd_inverseDenominator` for the sparse one); calling that number `d_r(C)` needs a `SmithWitness`, which nothing here builds, so the identification -- not the bound -- is what is missing. `QMinBound.d3_bound_same_class` gives the theorem for the element itself rather than for a generator of its cyclic group: the bounded-representation route keeps the class fixed, and `PrimitiveReduction` makes its representative primitive without enlarging the modulus -- dividing a gate's angle and modulus by their common divisor leaves the local phase unchanged. `D3BoundedNormalForm.d3_bound` is the normal-form version, whose generator is a coprime power. `QMinBound.qMin_le_nine` is `eq:6qubit-d3-bound`, the paper's boxed `q_min <= beta_6 = 9`, with no hypothesis. |
| 5.4 | `thm:d3-sslp-classification` | **Done** (`D3BoundedNormalForm.exists_sortedNormalForm_le_betaN`): at distance three the cutoff improves from `beta_{n+1}` to `beta_n`, and at six qubits to `9` with no hypothesis (`exists_sortedNormalForm_le_nine`). This needed the third normalization the repository was missing: permutations and coprime powers had semantic transports, local `X` conjugation did not. `FlipSemanticTransport` supplies it, which lets the sparse distance-three generator -- built on the normalized code -- be flipped back onto the original one. **The corollary's own reading of `m` is now proved as well** (`SSLPGeneratorOrder`). The paper takes *a generator* of the nontrivial projective diagonal group, so its `m` is `Nat.card` of that group; `exists_sortedNormalForm_le_betaN` runs on an arbitrary projectively nontrivial phase vector, so the modulus record's `m` was only the order of some element. `exists_sortedNormalForm_le_betaN_order` gets both halves of `eq:d3-sslp-bound` onto one record, and the step that makes that possible is `BoundedGeneratorOrder.logicalOrder_boundedGenerator`: the bound comes from the sparse `boundedGenerator` and the order from the original one, so without knowing the `beta_n` route preserves the projective order the two clauses would be about different generators. `d3_sslp_classification_generator` is the unfolded statement, `..._six` its unconditional six-qubit instance. |
| 5.6 | `thm:sslp-completeness` | **The covering half done** (`SSLPCompleteness`), which is the mathematical content: with `B_{n,d0} = beta_{n+1}` for `d0 = 2` and `beta_n` for `d0 >= 3` (`outerCutoff`, `eq:Bnd0`), no code in the class escapes the enumeration -- `completeness_distance_two`, `completeness_distance_three`, and `completeness_six_qubit` at cutoff `9`, with `completeness_of_nontrivial_*` restating them under the paper's own hypothesis on the group. The cutoff itself is load-bearing (`outerCutoff`), and `hasDistance_normalForm` carries the original code's distance onto the normal form, so the enumeration's candidate satisfies the equations for every Pauli of weight below `d`. Finiteness of the outer index is `OuterIndex`. `SectionThreeNonVacuity` closes the question an adversarial reading asks of any conditional theorem: the hypotheses are satisfiable. The orbit-21 representative is a genuine exact `((6,2,3))` code whose intrinsic group has an element of order exactly two, and feeding it through gives an actual normal form of an actual modulus, so none of Section III is vacuously true. **The "neither false positives nor false negatives" sentence is now two-sided** (`SSLPPipelineExact`). The negatives half is the covering statement above; the positives half is `code_of_sortedNormalForm` -- every record the enumeration retains is realized, its displayed data defining an exact code on the record's own frame carrying a projective diagonal logical element whose order is the record's own `m` -- and `pipeline_exact_two` / `pipeline_exact_three` state the two halves together at each cutoff. The round trip is not the identity on codes and does not claim to be: the recovered code sits on the normal-form frame, which is the original one after the local `X` conjugation and qubit permutation the record carries, and that is exactly the equivalence the theorem quotients by. What is still not formalized is the remaining algorithmic clause: that the group audit and equivalence quotient return the selected data. |
| 6.1 | `def:six-classification-levels` | **Levels (i), (ii) and (iii) done; (iv) is partial**, and `Levels` says why for each -- its own header was stale on all three of the levels it declared out of reach, and is corrected. Level (i) is `ClassificationLevelsSix.level_one_intrinsic_group`: the group is finite and cyclic and a nontrivial symmetry has order `2`, `3` or `5`. Level (iv) is stated for codes supported on orbit 36's two table fibres (`level_four_lu_class`); carrying it to an arbitrary order-five code needs a state-level transport from that code's fibres to the table's, which `CodeOrbitStatus.code_orderFive_is_orbit36` supplies only at the level of directory keys. Level (ii) is now complete rather than partial: `RealizationOrbits15.hasCompletion_iff_mem_realizationKeys` decides membership for all sixty-six keys, and `RealizationOrbits15.settled` has no open column -- the four keys the previous draft left open are discharged in `OpenOrbitsRealized`. `SSLPOrbitLevels` names both halves of the new `def:six-sslp-orbits` against objects the development proves things about: `MomentOrbit` is the classified index type, `KSet` is `K_r` of `eq:Kr-definition` (which needs no new definition -- `Completion` already *is* a member of `K_r`), `RealizationOrbit` is level (ii), and `card_realizationOrbit` is its fifteen. The definition's other two components are supplied too, and they needed no new mathematics: `CubeAction` already had `MomentWitness` (the feasible degree-two moment geometry), `ActiveMask`, `activeAffineRank` and `activeAffineRank_actFibers`, and nothing outside that file used any of them. `SSLPOrbitLevels.degreeTwoFeasible_of_fiberEquivalent` and `activeAffineRank_of_fiberEquivalent` say what makes them *orbit* data rather than pair data: they are invariants of the cube action, so `r_*` travels with the orbit. All four levels now carry a six-qubit theorem rather than only a definition -- `ClassificationLevelsSix` has one per level, so the named objects are load-bearing. The older `ClassificationLevels.SSLPMomentDatum` models the *20260822* level (ii) and still has no users. |
| 7.1 | Primitive sorted-vector count | **Done, all eight values, in the kernel** (`OuterEnumeration.primitive_two` through `primitive_nine_exact`, collected as `PaperReductionChain.primitive_sorted_counts`); an earlier note here that `P_6(6)` to `P_6(9)` were only checked in Python was stale. The paper's closed form `six:eq:primitiveMobius` is verified against Mathlib's own `ArithmeticFunction.moebius` at every one of those eight arguments (`PrimitiveMobius.primitiveCount_eq_mobiusCount`). **The general Mobius inversion is now formalized too** (`SortedVectorMobius`), at every length and every modulus, so the proposition holds as stated rather than at a table of arguments. The counting identity that was missing is `sortedCount_eq_choose`: the number of sorted vectors `0 <= a_1 <= ... <= a_k < m` is `binom(m + k - 1, k)`, proved by the multichoose recursion -- split on whether the first entry is zero, which either drops the length by one or, after subtracting one from every entry, drops the alphabet by one. The bijection that was missing is `card_contentFiber`: for each divisor `c` of `q` the sorted vectors of content `c` are the `c`-fold multiples of the primitive sorted vectors modulo `q/c`, which gives `sum_primitiveCount_divisors`, and Mathlib's `sum_eq_iff_sum_smul_moebius_eq` inverts it. `primitiveCount_six_eq_mobiusCount` is the paper's own display against the `mobiusCount` of row 7.1's earlier work, and `primitiveAngles6_length_eq_primitiveCount` puts the six-qubit outer loop's own list at the same count at all eight moduli -- a cardinality agreement, not a constructed bijection. Two further displays of the reduction fall out of the same counting lemma: `sortedCount_six` is `six:eq:starsbars`, the stars-and-bars count `#{0 <= a_1 <= ... <= a_6 < q} = binom(q+5,6)` that the raw-count lemma behind `six:eq:13877` uses, and `sum_sortedCount_two_to_nine` is `six:eq:qequalsm`, its sum `6,434` over `q = 2, ..., 9`. |
| 7.2 | Maximum support rank | **Convexity core done** (`ActiveFace`, `MomentPolytope.exists_maximum_support_rank`), and its finite content is now inside Lean too. The lemma's operative clause is `r_* = affdim U_0 = affdim U_1`; `Generated.RankSymmetry.ranks_equal` proves it for all 291 certified rank rows by kernel reduction, which is what lets a code's pivot bound the left active rank and have the `min` of the rank filter follow. The active masks themselves are identified inside Lean by `FinitePipeline.active_masks_exact` from the stored dual, and `RealFaceBridge.realSupport_subset_face` extends the forced-zero direction from the rational programme to the real one. |
| I | `six:thm:global-status` | **Done at the level of codes.** `CodeOrbitStatus.code_logicalOrder_mem` says every exact `((6,2,3))` code carrying a projectively nontrivial diagonal symmetry has `m` in `{2, 3, 5}`, and `code_logicalOrder_le_five` is the boxed `M_3(6) = 5` half. Until this session the statement existed only over the sixty-six directory keys: fifteen files mentioned `keyAt` and none of them mentioned `ExactCode 6 2 3`, twenty-seven mentioned `ExactCode 6 2 3` and none of them mentioned `keyAt`. Both semantic filter gates are now entered from a code -- the coarse one by `CodeDirectoryEntry`, the rank one by `CodeRankFilter` -- and `CodeOrbitKey.code_reaches_orbit_key` walks the four generated continuity theorems from the code's own row to a key. The record of how the coarse gate was closed follows. `beta_6 = 9` is a kernel theorem (`Generated.BinaryBetaSixKernel.Certificate.betaExact`), as are the 51 no-gos, the realizations, cyclicity, and now the whole combinatorial reduction (row II). What is left is entering the two *filters* from a code, and the obstruction is a specific one rather than plumbing. The paper's `r` is the **affine** dimension of the actual supports (`six:eq:ractual`, `r := affdim T_0 = affdim T_1 = rank Sigma`) and its bound is `q <= beta_r` at that rank (`six:eq:qbetar`). What this development proves is the **linear**-rank version: `SixQubitSemanticEntrance.SupportedBitBasis` takes raw bit rows, not differences, so `D3SparseRationalization`'s minor has the size of the real linear rank of the support's Boolean points -- which is the affine rank or one more. Half the filter does not feel the difference and is now proved: the zero-residue fibre contains the all-zero word, so its affine and linear ranks coincide (`MaskRankBridge.residueZeroMask_affineRank_eq_span`), and `CoarseFilterEntry.supportRank_le_maskAffineRank_mask0` derives the `S_0` clause of `six:eq:coarserank` from the code itself. The `q/m` fibre has no such point, and there the linear-rank bound gives one less than the filter asks; that clause rests on the affine-rank bound, which the paper proves by normalizing first (`thm:d3-bound`) but which does not follow from the linear one as this development's entrance stated it. `results/coarse-filter-audit.md` measures exactly what turns on it, in exact arithmetic, with the paper's own 508 and 291 reproduced as controls: the `S_delta` clause alone discards 350 pairs, **none** of which admits a common moment point. **That gate is now closed.** The directory rejects each discarded row by one of two witnesses; all 422 rows carrying the right-hand one are certified moment infeasible by exact Farkas separators (`Generated.ExtraMoment.rejectRightPairs_infeasible`), and `Generated.CoarseRightRows.rejectRight_mem` checks per row, over all 11,422, that a right-rejected row carries one of them. So `CoarseFilterUnconditional.keepAt_of_s0_of_feasible`: a row satisfying the `S_0` clause and admitting a common moment point is kept -- and a code supplies both. The coarse filter provably never discards a code, with no appeal to the affine-rank bound, and the directory still has 508 outputs. The arithmetic half of the `S_0` clause is now proved too, from the data it genuinely needs: `SortedPivot.Pivot` records a nonsingular zero--one minor of the support's bit matrix off whose coordinates the angle vanishes, and `SortedPivot.Pivot.s0Clause` derives the whole clause from it -- nonsingularity gives the geometric half (`SortedPivot.Pivot.rank_le_maskAffineRank`), sparsity plus primitivity gives the arithmetic one (`SortedPivot.lcmDen_phase`, `SortedPivot.Pivot.q_dvd_inverseDenominator`, `SortedPivot.Pivot.rMin_le_rank`). The sparsity is not decoration: without it the clause is false, and the module's docstring gives the counterexample. The pieces that construction needs are now in place too, and the route is not the obvious one: the normal form calls `canonicalTwoFiber` a second time, so its support is the fresh pivot's support shifted, and under that shift sparsity is inherited but **nonsingularity is not** -- the shift complements columns and a rank-one correction can drop the rank. It works because the shift is by a point of the first logical word's own support -- how `RankTwoGlobal.finiteGenerator_twoFiber` has always chosen it, though the certificate did not record it until now (`RankTwoGlobal.TwoFiberCertificate.base_supported`). That puts the **zero word** in *both* normalized supports, so their affine and linear ranks agree and the +/-1 disappears entirely; `MaskRankBridge.vectorSpan_eq_span_of_zero_mem` and `MaskRankBridge.finrank_direction_image_affine` carry that across the shift, `MaskRankBridge.finrank_vectorSpan_le_finrank_span` turns it back into a linear rank, and `MaskRankBridge.exists_nonsingular_rows` extracts a *fresh* minor. The whole remaining obligation is now one statement, not a construction: `SortedPivot.nonempty_pivot_of_spanning` takes the pivot's coordinate set to be the angle's own support -- which makes sparsity free -- and builds the minor itself, so all that is missing is that the normal form's left support, restricted to the coordinates its angle touches, **spans**. That statement is false for a general sorted normal form (the module's counterexample), which is precisely why it is the content the construction has to supply -- and it now does: `SortedPivotConstruction.exists_normalForm_s0Clause` derives the `S_0` clause for every exact `((6,2,3))` code with a projectively nontrivial diagonal symmetry, with no hypothesis. Combined with `CoarseFilterUnconditional`, whose other input a code supplies as its own pair of distributions, **the coarse filter provably never discards a code**. That second input is *real* feasibility, not rational: `FinitePipeline.Feasible` is over `Q` and a code's probabilities are real, so a code does not directly give a rational feasible point -- that would need a rational point of a nonempty rational polyhedron, true but not proved here. `RealMomentSeparatorBridge.not_realFeasible_of_separatorData` makes the descent unnecessary: a rational separator excludes the real fibre LP too, and all 422 certificates are recorded in both forms (`Generated.ExtraMoment.rejectRightPairs_realInfeasible`) -- with no appeal to `q <= beta_r` at the affine rank -- the step this development could not at first enter, though the paper proves it: `thm:d3-bound` normalizes by a local `X` conjugation that puts `0^n` in `T_0`, so the common affine span is linear and `r` is both ranks at once -- and the transport across the shift that separates the normal form from the fresh pivot is now one theorem, `SortedPivot.span_rqpoint_of_shifted_nonsingular`: it takes the nonsingular minor the rationalization produces on the normalized side and returns the spanning statement on the side the normal form lives on. With the zero word in both supports the restricted point sets have equal affine ranks (`MaskRankBridge.finrank_direction_rqpoint_bxor`), so they span together or not at all; `MaskRankBridge.span_eq_top_of_nonsingular` is the nonsingular-to-spanning direction. What is left is the plumbing: restating `D3BoundedNormalForm.exists_sortedNormalForm_le_nine` -- the data is what `SixQubitSemanticEntrance.BinarySimplexPivot` already carries for the generator that construction passes through, but its conclusion discards it -- and `FiniteRankPipeline.RankRow`, which is the same shape at the active face. One prerequisite of that arithmetic half is now supplied: `CoarseFilter.ThresholdBounds` -- which `fullFiberCriterion_of_realization` and `CoarseFilter.Directory.Valid.realization_retained` both take as a hypothesis -- **had no inhabitant anywhere in the repository**, so those theorems were sound but unusable. The three hard cases `beta_4 = 3`, `beta_5 = 5`, `beta_6 = 9` were generated enumerations; the three easy ones were simply absent. `ThresholdBoundsSmall.thresholdBounds` closes it: `betaBound_of_fixedSize_detNatAbs_bound` turns each into an absolute-determinant bound on zero--one matrices of one fixed size, and at sizes one, two and three that is a short explicit polynomial in `0/1` entries. |
| II | `thm:six-66-orbits` | **Done end to end, and now entered from a code.** The eight steps are stated in the paper's own form in `PaperReductionChain`, one theorem per lemma of the 20260902 revision, with `six_66_orbits` as their conjunction. Its `216` primitive angle records -- a projection back onto the pre-hashing records -- is `ActiveRankRecordCount.compatible_record_count`, run through the provenanced record-to-pair map itself; at about ten minutes it is the most expensive single declaration in the package. Both semantic filter gates are closed (rows I and 7.2). The record of the combinatorial half follows. Every count in `13,877 -> 13,449 -> 12,768 -> 11,422 -> 508 -> 291 -> 215 -> 66` is a kernel theorem, and the last step is now assembled rather than left as parts: `Generated.FiniteOrbitCertificate.hasExactlyClasses` says there are exactly 66 labelled classes, `orbit_coverage` that every rank-compatible pair meets one, `no_ghost_key` that none is a directory artefact. Its two nontrivial fields had never been proved -- `Generated.OrbitCertificate.signature_exact` (the 66 stored distance signatures really are the keys' own histograms) and `Generated.OrbitCertificate.witness_valid` (the 215 separately checked cube actions, collected). Entering the chain *from a code* is `CodeFiberBridge`: `recordOf_mem_nonemptyFiber` puts an exact `((6,2,3))` code's normal form into the 12,768-record list, and `code_supports_in_enumerated_fibres` puts its two logical words in that record's two residue fibres. What is missing is the two filters in between -- see row I. |
| II.b | `six:thm:global-status` (the boxed `M_3(6) = 5`) and its physical companion | **Done** (`OrderRange`). `logicalOrder_mem`: a directory key with an exact normalized distance-three completion has `m` in `{2,3,5}`; `maxLogicalOrder_eq_five` is `M_3(6) = 5`, upper bound and attainment. The two layers this needed did not exist -- logical orders 4 and 7, fifteen of the sixty-six keys, more than all the previously ruled-out orders together, so nothing had prevented a code of logical order four (`OrderFourNoCompletion`, `OrderSevenNoCompletion`). The physical-order companion `main.tex` does not state is `physicalOrder_le_six` and `maxPhysicalOrder_eq_six`: `Q_3(6) = 6`. It is not a corollary of the logical one -- `m = 2` occurs at `q = 2, 4` and `6`. Attainment of every value is exhibited by an actual code (`logicalOrders_attained`, `physicalOrders_attained`). |
| II.c | `thm:six-15-sslp-realization-orbits` (new in 20260902) | **Done, both halves, with the distribution.** `RealizationOrbits15.hasCompletion_iff_mem_realizationKeys` is the boxed iff; `realizationKeys_paperIds` is the fifteen paper numbers; `realizationKeys_orderDistribution` is the `11 : 3 : 1` table over `m = 2, 3, 5`; `card_realization_orbits` is "exactly fifteen". The only-if half is the fifty-one no-gos this development already carried. The if half needed the four keys the 20260822 draft left open, and needed no new code: `Completion` asks for support *inside* a key's fibres, and the supports of `Orbit11Real`, `Orbit22Real` and `Orbit23Real` already sit inside them (`OpenOrbitsRealized`, two of the four with the logical words interchanged). Note what is **not** claimed: the weight-enumerator images `W_1` to `W_4` stay open, so row III still settles eleven images, not fifteen. |
| III | `thm:six-WE-status` | **Done, in full, and now at the directory level.** `WImages` and `WImageNoGo51` give the 51 empty images and the 11 exact nonempty ones -- single points and interval families alike -- and `WImageSettled62` packages them with the audit that 51 + 11 + 4 covers paper IDs 1 through 66 exactly once, which is the theorem's clause (v). What that left open was named in its own docstring: those are statements about *paper representatives* -- an angle vector such as `SixQubit.Orbit45Support.av` and its two residue fibres -- not about the 66 orbits. `DirectoryOrbitStatus` closes it -- `noCompletion_of_mem_noGoKeys`, `hasCompletion_of_mem_realizedKeys` and `settled_or_open` are the same census about the directory keys, each key bound to its paper orbit by an exact mask computation and its stored cube action, with `openKeys_paperIds` identifying the four remaining keys as the paper's boxed `W_1, ..., W_4`. |
| IV | `thm:unique-C5-LU` | **Done, both claims.** An earlier note here said this was blocked for want of an operator layer; that was stale. The rigidity half is `SixQubit.Orbit36Certified.table_representative_rigid`, lifted to projectors by `Orbit36LUBridge.original_projector_luEquivalent_canonical`, which builds honest orthonormal frames and applies the kernel-visible six-qubit local-monomial bridge. The other half -- every exact code with a projective order-five element is in orbit 36 -- was the one genuinely missing piece, because nothing carried a code to a directory key; `CodeOrbitStatus.code_orderFive_is_orbit36` now does, over `CodeOrbitKey.code_reaches_orbit_key` and the seven order-five no-gos. |

Two things block the rest, and only one of them is deep. Cartan's
closed-subgroup theorem is a genuine Mathlib-scale project -- now needed only
for `K > 2` and for `d = 2`, since rank two at distance three no longer goes
through it. What remains of the six-qubit pipeline is no longer the enumeration
-- that is finished, counts and orbit directory alike -- but the two filters
between them: the coarse affine-rank filter and the active-face rank filter are
sound as stated (`CoarseFilter.fullFiberCriterion_of_realization`,
`FiniteRankPipeline.RankRow.sound_of_valid`), and what is missing is
constructing their input witness from a code's own normal form. That is now a
named piece of mathematics rather than an open-ended engineering item: the
denominator bound has to hold at the *affine* rank of the support, and only the
linear-rank version is proved (row I). Mathlib supplies neither half of the
gap -- there is no lemma relating an affine span's rank to the linear span's,
and no rank transfer between `Q` and `R` for matrices -- so both were built
here (`MaskRankBridge`), in the descending direction that does exist for linear
independence. `beta_6 = 9`
used to be listed here; it is now proved. Nothing else in `main.tex` is
unformalized for want of mathematics.

## A note on the negative results

`results/workflows/` holds the multi-agent records, including the adversarial
review that found a real gap in the first orbit-26 argument and produced explicit
witnesses for it. These are kept deliberately: they record which relations are
*not* available and which branches are vacuous. That information is expensive to
rediscover and easy to assume away — three of the five reasoning errors in this
project were exactly that kind of assumption.
