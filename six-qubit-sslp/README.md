# Six-qubit SSLP orbits: machine-checked certification

Every one of the **51 no-go moment orbits** of the six-qubit SSLP
classification carries a Lean 4 proof that no exact six-qubit
`((6,2,3))` code arises from it. All 51 are checked by the **Lean kernel alone**
— axiom footprint exactly `[propext, Classical.choice, Quot.sound]`, with no use
of `native_decide` or `sorry` in proof/tactic position.

Start with **`formalization/formalization.pdf`**. It explains what is certified,
the standard it was held to, the algebraic mechanisms, the four hard orbits, and
the errors that were made and caught along the way.

## Status

| | |
|---|---|
| No-go modules with a kernel-checked headline | 51, each with a code-level wrapper |
| Of those, matching the paper's target orbit | **51** |
| Lines / theorems in the 51 no-go modules | 41,521 / 12,521 |
| Orbit-36 rigidity chain | 11 modules, 28,412 lines / 1,894 theorems |
| Ten exact realizations | 10 modules, 1,606 lines / 150 theorems, over a 516-line shared layer |
| Lines in the whole development | 120,929 |
| Axiom-audit entries | 436, all clean |
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

Orbit 36 is the one realized orbit whose certification goes further than
existence. What is certified there is rigidity: from the support conditions, the moment
system and twenty-two weight-≤2 KL rows alone, the amplitude magnitudes are
forced, the code is unique up to local-monomial equivalence, and its weight
enumerator is `(1, 0, 21/25, 0, 291/25, 384/25, 79/25)`. The chain lives in
`SixQubit/Orbit36*.lean` with `CodeEquiv`, `MacWilliams` and `K4Kernel`, and its
hypotheses are exhibited as satisfiable in `SixQubit/Orbit36Vacuity.lean`, so
the rigidity statement is not vacuous.

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
| Are the 51 Lean theorems really kernel-proved? | **Yes.** 332 audit entries, all `[propext, Classical.choice, Quot.sound]`, no escape hatches |
| Do they state what the paper needs? | **51 of 51**, since the repair. Four modules (30, 53, 55, 65) had used a residue of the wrong additive order and were rebuilt from scratch at `delta = q/m`; five more (34, 57, 59, 64, Order9) had moment rows inconsistent with their headline ordering and were regenerated. `gate.py` now reports 51 passed, 0 failed, 0 unchecked |
| Do they rule out a real code end to end? | **All 51 do.** Each has a `no_code` theorem taking only support, normalization and `SS.HasDistance ![c,d] 3` — no KL row is assumed. `SixQubit/Vacuity.lean` exhibits, for **all 51**, a point-mass pair satisfying every other hypothesis, so no statement is vacuous |

The nine defective modules have been repaired and the checks are green. The guard
that should have existed from the start is `tools/manifest.json` (derived from
the paper's own 66-orbit table) plus `tools/verification/gate.py`, which checks
`delta = q/m`, its additive order and both fibers. The separate
`tools/verification/momentgate.py` checks the complete content and ordering of
the declared moment rows:

What remains open is one level up, and it now has a name. The reduction of an
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
lake build SixQubit.Audit        # expect 332 clean axiom lines

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

Every hit must be inside a docstring or comment. There are 181 occurrences on 123
lines; most are the sentence in each module stating that `native_decide` is not
used. The check that matters is the axiom footprint, not the grep count: an
escape hatch actually used would show up in `#print axioms` as `sorryAx` or
`Lean.ofReduceBool`, and none does.

Toolchain: Lean `v4.27.0`, Mathlib `fc278a179e431ed10630af63fc05481680c0c7bd`,
pinned in `lean-toolchain` and `lake-manifest.json`. Nothing outside Mathlib is
used mathematically.

## Layout

| Path | Contents |
|---|---|
| `SixQubit/` | 51 orbit modules, 13 algebra modules, 51 code-level wrappers, the 11-module orbit-36 chain, ten realization modules over a shared exact-arithmetic layer, the audit |
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
argument; a 16-type support classification). Section 9 lists what remains open.

## A note on the negative results

`results/workflows/` holds the multi-agent records, including the adversarial
review that found a real gap in the first orbit-26 argument and produced explicit
witnesses for it. These are kept deliberately: they record which relations are
*not* available and which branches are vacuous. That information is expensive to
rediscover and easy to assume away — three of the five reasoning errors in this
project were exactly that kind of assumption.
