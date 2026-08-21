# Six-qubit SSLP no-go orbits: machine-checked certification

Every one of the **51 no-go moment orbits** of `six_qubit_sslp.tex` carries a
Lean 4 proof that no exact six-qubit
`((6,2,3))` code arises from it. All 51 are checked by the **Lean kernel alone**
— axiom footprint exactly `[propext, Classical.choice, Quot.sound]`, no
`native_decide`, no `sorry`.

Start with **`formalization/formalization.pdf`**. It explains what is certified,
the standard it was held to, the algebraic mechanisms, the four hard orbits, and
the errors that were made and caught along the way.

## Status

| | |
|---|---|
| Modules with a kernel-checked headline | 51, each with a code-level wrapper |
| Of those, matching the paper's target orbit | **51** |
| Lines in orbit modules | 41,521 (the 51 orbit modules alone) |
| Theorems in orbit modules | 12,521 |
| Lines in the whole development | 90,109 |
| Axiom-audit entries | 332, all clean |
| Build errors / warnings | 0 / 0 |

Orbits 25–40 (no 36) and 53–66 come from `six_qubit_sslp_v7.tex`; orbits 13, 18,
41, 42, 43, 44, 46, 47, 48, 50, 52 are the first eleven of the twenty-two added
in `six_qubit_sslp.tex`. Orbit 66 is in
`SixQubit/Order9.lean`; all others in `SixQubit/Orbit<n>.lean`.

## Status, stated precisely

A collaborator's audit in August 2026 found that three different things were
being conflated. They are now tracked separately:

| Question | Answer |
|---|---|
| Are the 51 Lean theorems really kernel-proved? | **Yes.** 332 audit entries, all `[propext, Classical.choice, Quot.sound]`, no escape hatches |
| Do they state what the paper needs? | **51 of 51**, since the repair. Four modules (30, 53, 55, 65) had used a residue of the wrong additive order and were rebuilt from scratch at `delta = q/m`; five more (34, 57, 59, 64, Order9) had moment rows inconsistent with their headline ordering and were regenerated. `gate.py` now reports 51 passed, 0 failed, 0 unchecked |
| Do they rule out a real code end to end? | **All 51 do.** Each has a `no_code` theorem taking only support, normalization and `SS.HasDistance ![c,d] 3` — no KL row is assumed. `SixQubit/Vacuity.lean` exhibits, for **all 51**, a point-mass pair satisfying every other hypothesis, so no statement is vacuous |

The nine defective modules have been repaired and the gate is green. The guard
that should have existed from the start is `tools/manifest.json` (derived from
the paper's own 66-orbit table) plus `tools/verification/gate.py`, which enforces
`delta = q/m`, its additive order, the fibers, and the moment-row ordering:

What remains open is one level up: neither the reduction of an arbitrary code to
one of the sixty-six rank-compatible moment orbits, nor the equivalence of other
angle records to the chosen representatives, is formalized. So the per-orbit
no-gos are complete and code-level; the classification theorem that assembles
them is not.

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

The third command must print nothing. That is the whole certification: because
`#print axioms` is transitive, one clean line per headline theorem certifies its
entire dependency cone.

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
| `SixQubit/` | 51 orbit modules, 13 algebra modules, 51 code-level wrappers, the audit |
| `SS/` | problem-independent bit-string and Pauli infrastructure |
| `formalization/` | the process document (`.tex` and `.pdf`) |
| `tools/core/` | fibers, Pauli enumeration, moment matrices, relation extractors |
| `tools/orbits/` | per-orbit data and block structure |
| `tools/generators/` | the scripts that emit the Lean modules |
| `tools/verification/` | numerical and symbolic checks independent of Lean |
| `results/` | axiom audit, orbit table, multi-agent workflow records |

Each `tools/` and `results/` subtree has its own README mapping artifacts to the
claims they support.

## What to read for what

**A reviewer asking "is this actually proved?"** — `results/axiom-audit.txt`,
then the three commands above. Nothing else is load-bearing for soundness.

**A reviewer asking "is the right thing proved?"** — run the checks that
compilation does not perform:

```sh
python tools/run.py verification/classify.py            # no smuggled hypotheses
python tools/run.py verification/admis.py               # every row is weight <= 2
python tools/run.py verification/momentgate.py          # moment rows transcribed correctly
python tools/run.py verification/momentgate.py --selftest   # and that checker actually catches errors
```

`classify.py` confirms every headline hypothesis is an off-diagonal KL row, a
diagonal KL row, or the moment system — an algebraic fact taken as an assumption
instead of derived would void the proof invisibly. `admis.py` confirms every row
is a genuine weight-≤2 Pauli; a weight-3 row would silently turn a
distance-three no-go into a much weaker claim. Both currently return zero
violations across all 51 orbits.

**A reviewer asking "is the right thing proved?"** — the hypotheses of each
`no_go_of_moments`. A `False` theorem is only as good as its hypotheses, and the
failure mode to look for is an algebraic fact smuggled in as an assumption
instead of derived. Section 5 of the process document reports the hand
classification for the two hardest orbits (31: 46 hypotheses = 33 off-diagonal +
12 diagonal + 1 moment system; 26: 41 = 24 + 16 + 1; zero smuggled in either).

**A collaborator continuing the work** — `formalization/formalization.pdf`
Sections 3–5, then `tools/core/kl.py` and `tools/core/relgen.py`. Section 6
documents a tooling bug that gated three orbits for a long time; the invariant
that catches it is that the admissible Pauli count must be
`154 = 1 + 6*3 + 15*9`.

**Someone writing the paper** — Section 4 for the four hard orbits. The
arguments obtained here are shorter than the manuscript's, and for orbits 26 and
31 they avoid machinery the manuscript needs (matrix inverses and a genericity
argument; a 16-type support classification). Section 8 lists what remains open.

## A note on the negative results

`results/workflows/` holds the multi-agent records, including the adversarial
review that found a real gap in the first orbit-26 argument and produced explicit
witnesses for it. These are kept deliberately: they record which relations are
*not* available and which branches are vacuous. That information is expensive to
rediscover and easy to assume away — three of the five reasoning errors in this
project were exactly that kind of assumption.
