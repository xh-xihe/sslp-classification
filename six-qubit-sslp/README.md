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
| Axiom-audit entries | 592, all clean |
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
| Are the Lean headline theorems really kernel-proved? | **Yes.** 592 current audit entries; every footprint is contained in `[propext, Classical.choice, Quot.sound]`, with no escape hatches |
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
lake build SixQubit.Audit        # expect 592 clean axiom lines

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
Definition 6.1, the weight-enumerator image `W_r`, and its evaluation. Seven
orbits -- 9, 10, 11, 16, 21, 22, 23 -- now have `W_r = {E_2^A}` or `{E_1^A}` as
Lean theorems, stated in the paper's own terminology rather than in the ad-hoc
form the six-qubit modules use. The mathematics was already finished; what is
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
with the words "complete binary-matrix tables give" and no proof. Verifying it
would mean bounding the largest invariant factor over all nonsingular 6x6 binary
matrices -- `2^36` of them, or `6.8e7` after discarding repeated and zero rows --
which is far beyond `decide`, and the Hadamard bound only gives 14.

It is important to be clear about what this does and does not block. The general
theorem `thm:d3-bound` states `q | d_r(C)` and `q <= beta_r <= beta_n` with
`beta_n` *defined* as that maximum; the inequality is then immediate and the
value of `beta_6` is not needed to formalize it. Only the six-qubit
specialization -- Result I's `M_3(6) = 5`, and the exhaustiveness of the orbit
list -- uses the number. Since the paper itself cites it as a computation rather
than proving it, the faithful thing is to carry it as an explicit input, which
is what is done here. Replacing it with a weaker provable bound would not be
formalizing the paper; it would beimproving on the paper at the cost of redoing the
Supplementary enumeration, and that is a separate project.

What actually blocks `thm:d3-bound` is the next item, not this one.

Mathlib's Smith normal form carries no divisibility chain --
`Module.Basis.SmithNormalForm` has no field asserting `a i` divides `a (i+1)` --
and no uniqueness of invariant factors, which the paper's notation `d_i(C)`
silently assumes and never proves. This turned out to block less than expected:
`MainTheory/Clearing.lean` gets the qualitative denominator clearing from the
adjugate instead, so what remains blocked is only the sharp multiplier, and with
it the numerical bound `q <= beta_n`.

The paper's finite-projective-group theorem is compact-Lie-group theory, and
Cartan's closed-subgroup theorem is absent from Mathlib entirely. Mathlib also
has no spectral theorem for unitary or normal operators, only for Hermitian
ones, which is what the phase-sector lemma needs; there is a route through two
commuting self-adjoint parts, but it is real work.

## A note on the negative results

`results/workflows/` holds the multi-agent records, including the adversarial
review that found a real gap in the first orbit-26 argument and produced explicit
witnesses for it. These are kept deliberately: they record which relations are
*not* available and which branches are vacuous. That information is expensive to
rediscover and easy to assume away — three of the five reasoning errors in this
project were exactly that kind of assumption.
