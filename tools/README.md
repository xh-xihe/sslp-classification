# Tools

[Home](../README.md) · [Documentation](../docs/README.md) · [Reproduction](../docs/reproduce.md)

Current commands and verification scope are in
[`docs/reproduce.md`](../docs/reproduce.md). The generator notes below retain
provenance for older construction routes.

| Current entry point | Purpose |
| --- | --- |
| `build_lean.py` | Content-validated serial build of all five active libraries |
| `verify.py --paper-version 20261003 --only sources generated audit-names axioms` | Public proof checks without private manuscripts |
| `repository_index.py --check` | Source-catalog and topic-navigation consistency |
| `check_navigation.py` | Curated links, anchors, SVGs and GIF block structure; also run by documentation CI |
| `render_banner.py` | Optional visual-asset renderer; requires Pillow, Playwright and a local browser |
| `rebuild_orbit_certificates.py` | Exact orbit-2/3 payload reconstruction |
| `generators/emit_si_sector_counts.py` | Witnesses for both SI count tables, checked against actual records, distinct fibre pairs and orbit keys by ordinary Lean reduction |
| `verification/generate_orbit26_printed_moments.py --check` | Reproduce the literal orbit-26 rational matrix, complete affine solution and rank-fourteen certificate; Lean checks the output |
| `verification/generate_order_five_printed_moments.py --check` | Reproduce physical SI moment consequences for orbits 35, 37 and 38, including reconstruction of the complete real moment system |
| `verification/check_orbit31_reproduction.py` | Forty exact source-reproduction checks for current literal moment, support, physical phase and enumerator bridges; requires separate kernel build and axiom audit |
| `verification/check_orbit30_reproduction.py` | Eight exact source-reconstruction checks for the literal physical K5, graph and determinant route; requires separate kernel build and axiom audit |
| `verification/check_split_matrix_reproduction.py` | Three exact source checks for split-family displays and physical orbit-26/28 matrices; requires separate kernel build and axiom audit |
| `verification/check_frame_anchor_reproduction.py` | Two exact source checks and ten physical anchor/frame source hashes; separate whole kernel build and audit required |
| `verification/check_matching_parity_snapshot.py` | Fifteen matching/parity source hashes; separate whole kernel build and fresh audit required |
| `verification/check_scalar_spinor_snapshot.py` | Twelve scalar/spinor source hashes; separate whole kernel build and fresh audit required |
| `verification/check_display_route_snapshot.py` | Twenty display-route source hashes; separate whole kernel build and fresh audit required |
| `verification/check_final_bridge_snapshot.py` | Nine final bridge source hashes; separate whole kernel build and audit required |
| `verification/check_si_correspondence.py` | Complete current SI assertion and paragraph/type correspondence; requires exact private sources |
| `paper_claims.py`, `named_results_doc.py`, `prose_review_doc.py` | Version-bound private-source correspondence records |

Use `--paper-version 20261003` explicitly. Historical tools retain their
historical default so that old release records can still be reproduced.

This directory retains the Python generators used for the Lean transcription and
the independent checks used to review what the Lean statements say. Execution
provenance is not part of the kernel certificate; the checked artifacts are the
committed Lean sources, build outputs and axiom audit.

Requirements: Python 3 with `sympy`, `numpy`, `scipy`.

Run anything through the path-setting wrapper, from the repository root:

```sh
python tools/run.py verification/feas2.py
python tools/run.py core/kl.py
```

The scripts import each other by bare module name, so `core/` and `orbits/` must
be on `sys.path`; `run.py` does that and nothing else.

## `core/` — shared infrastructure

| File | What it provides | Why it matters |
|---|---|---|
| `orbit.py` | residue fibers from `(q, a, delta)` | the definition everything else is built on |
| `scan.py` | the original orbit search and mechanism ladder | **contains the dressings bug**; kept as the historical record, superseded by `kl.py` |
| `kl.py` | the complete weight-≤2 Knill–Laflamme system | **the fix.** Enumerates all 64 dressings and filters on support size. The invariant: the admissible Pauli count must be `154 = 1 + 6*3 + 15*9` |
| `cert.py` | exact `linear_combination` certificates (`build`, `reduce_mod_linear`) | supplies the rational coefficients in every derived moment fact |
| `relations.py` | trustworthy two-term relation extraction | written after mis-reading a collapse three times; computes what is genuinely in a mask's row space |
| `relgen.py` | the same without assuming complementary fibers | orbit 29's fibers are **not** complementary, which breaks `relations.py` |
| `propagate.py` | fixpoint between the moment polytope and the Walsh systems; `pdim`, `DLP` | `DLP` was once used to pin `delta`; it is NOT the authority. The rule is `delta = q/m` from `tools/manifest.json` — see the warning below |
| `blocks.py` | block structure when the first angle is zero | serves orbits 26 and 33 |

> **Two traps recorded in the code.** (1) `delta` is *defined* as `q/m` and its
> additive order in `Z_q` must equal `m`. Picking it by fiber size, or by polytope
> dimension alone, is how four modules came to prove a no-go for the wrong
> projective order; the correct and incorrect fibers had equal sizes and empty
> intersection. `tools/verification/gate.py` now enforces the definition. (2) `blocks.py` indexes `TOP` by sorted top
> tails, so block matching must use the *complement* of the bottom tail.

## `orbits/` — per-orbit structure

`o26.py`, `o29.py`, `o31.py`, `o33.py` set up the four hard orbits of the first
batch exactly. `o26data.py`, `o29data.py`, `o54data.py` are mask and relation
tables the generators read. `o28.py`, `o32.py` are smaller structural probes.

## `generators/` — orbit → generator → module

This is a **historical provenance index for the major construction routes**, not
a byte-for-byte generator manifest. Some algebra layers were hand-written, the
order-nine source module has no complete raw-module generator committed, and
several repaired modules require the explicit overlay scripts listed below.
Kernel checking plus the independent verification gates, rather than this table
alone, certify the committed Lean sources.

### First batch (from `six_qubit_sslp_v7.tex`)

| Orbits | Generator(s) | Emits |
|---|---|---|
| 25 | `gen15.py`, `gen15b.py`, `gen15c.py`, `gen15d.py` | `SixQubit/Orbit25.lean` — first orbit needing the diagonal layer |
| 26 | `gen26f.py` (staged: `python gen26f.py <stage>`) | `SixQubit/Orbit26.lean`; algebra in `SixQubit/Block26.lean` |
| 29 | `gen29a.py`, `gen29c.py`, `gen29pf.py` | `SixQubit/Orbit29.lean`, parts of `SixQubit/Pair29.lean` |
| 31 | `gen31.py` | `SixQubit/Orbit31.lean`; algebra in `SixQubit/Table31.lean` |
| 33 | `gen16.py`, `genblock.py` | `SixQubit/Orbit33.lean`, `SixQubit/Block33.lean` |
| 27, 28, 32, 35, 37–40, 54, 56, 58, 60–63 | historical mechanism-ladder route in `core/scan.py` + `core/cert.py` | their `SixQubit/Orbit<n>.lean` sources; this row records provenance, not byte reproduction |
| 30 | `genk5.py`, then `gen30.py` | rebuilt `SixQubit/K5.lean` and `SixQubit/Orbit30.lean` at `delta = 1` |
| 53 | `gen53.py` | rebuilt `SixQubit/Orbit53.lean` at `delta = 1` |
| 55 | `genstar.py 55` | rebuilt `SixQubit/Orbit55.lean` at `delta = 1` |
| 65 | `gen3lp.py 65` | rebuilt `SixQubit/Orbit65.lean` at `delta = 1` |
| 34, 57, 59, 64 | historical base sources plus the `genmomrows.py` repair overlay | final `MomentSystem` rows in the four named orbit modules |
| 66 | no complete raw-module generator is committed; `gencode9.py` emits only the wrapper | historical `SixQubit/Order9.lean`; generated `SixQubit/CodeOrder9.lean` |

### Second batch (the twenty-two added in `six_qubit_sslp.tex`)

| Orbits | Generator(s) | Mechanism |
|---|---|---|
| 47, 48, 18, 41, 42, 43 | `newanalyse.py` → **`newcerts.json`** → `gennew.py <orbit>` | isolation certificate: a rational combination of admissible dressings isolates one incidence monomial whose two endpoint probabilities the polytope pins to positive constants |
| 52, 44, 46 | `gen2.py <orbit>` | isolate several incidences whose endpoints are tied by a positive ratio, so each `mul_eq_zero` branch collapses; the vanishing set breaks the moment system |
| 50 | `gen3.py <orbit>` | odd triangle of reciprocal relations (`SixQubit/Triangle.lean`) |
| 13 | `gen13.py` + `fin13.py 13` | complete 2×2 block orthogonality + equal block frames (`SixQubit/Frame.lean`) |
| 14, 15 | `genp4.py`; layer by `genpf.py` | sliced parity-four connectivity (`SixQubit/ParityFour.lean`) |
| 24 | `genp424.py`; layer by `genpf.py` | un-sliced parity-four, via the repetition isometry on qubits 1 and 6 |
| 12 | `gen12.py`; layer in `SixQubit/Spinor.lean` | cancelling pair of rank-one matrices, division-free |
| 6 | `gen6.py`; layer in `SixQubit/Spinor.lean` | Lagrange's identity makes two `1/9`s cancel exactly |
| 17 | `o17_analyse.py`, `o17_cert.py` → `gen17.py`; layer by `gen17haf.py` | hafnian ideal + support-graph enumeration (`SixQubit/Hafnian.lean`) |
| 19 | `gen19.py` | product projector on two half-angle coordinates |
| 20 | `gen20.py` | block uniformity + odd triangle |
| 49, 51 | `an4951.py` → `gen4951.py` | quadratic moment pinning + the mixed-pair triangle |
| 5 | `gen5orbit.py` → `gen5lean.py`, `gen5lean2.py`, `gen5lean3.py`; `gen5algebra.py`+`build5.py` → `Trace5.lean`; `gen5flip.py`, `gen5flip2.py`, `gen5flip3.py` → `Flip5.lean` | C⁴ trace inequality + the flip-kernel dichotomy |

`newcerts.json` is the certificate data `gennew.py` consumes. Regenerate it with
`python tools/run.py generators/newanalyse.py` (it writes to the working
directory).

The thirteen algebra layers (`Block26`, `Block33`, `Pair29`, `Table31`, `Triangle`,
`Frame`, `Spinor`, `ParityFour`, `Hafnian`, `Trace5`, `Flip5`, `Kernel5`, `K5` — the
last used by the rebuilt orbit 30) are
hand-written or emitted by the scripts named above; that is where the
mathematics lives. The generators write only the transcription layers — fibers,
incidences, Walsh signs, moment facts, expansions.

### The five generated scalar-squeeze exact images

| Generator | Emits |
|---|---|
| `genenum.py` | `SixQubit/Orbit<n>Enum.lean` for n in 10, 11, 16, 22, 23 |

These are the orbits whose forced stabilizer `D(a;4)^2` has Pauli weight one or
two. The generator computes that mask from the angle vector, checks in Python
that it really does have even overlap with every support word, and refuses to
write a module otherwise; the Lean then decides the same condition. Orbit 21's
mask has weight four and orbit 45 has `q = 6`, where the square is not a Pauli,
so neither is emitted — the generator reports them rather than skipping
silently.

The generated headline is `enumerator_pair_unique_fiber`, not merely an
A-vector statement.  `SixQubit/BEnumerator.lean` proves the complete seven-row
six-qubit MacWilliams transform from the subset identity and derives the exact
B-vector for each of the two possible A-vectors.  Each generated module also
contains `enumerator_pair_attained`, so uniqueness and non-emptiness are both
kernel statements.

### The five orbit-specific exact-image stacks

The other five WE orbits require individual reductions rather than the common
`genenum.py` mask squeeze:

| Orbit | Top-level module | Kernel-checked result |
|---|---|---|
| 7 | `Orbit7UniversalFinal.lean`, `Orbit7DirectMarginal.lean` | exact `[0,1]` A/B line and a literal rank-two `Tr(P/2)` pair marginal |
| 8 | `Orbit8UniversalFinal.lean` | exact `[1/2,1]` A/B line |
| 9 | `Orbit9UniversalFinal.lean` | unique `E2` pair and the uniform-gauge weight-two scalar |
| 21 | `Orbit21Enum.lean` | full-fibre Walsh/Farkas `E2` pair and genuine attainment |
| 45 | `Orbit45Final.lean` | exact `[2/3,1]` A/B line and two-chart attainment |

Most of these reductions are hand-written Lean. Two generated finite cores have
explicit provenance: `geno21coef.py` emits the integral orbit-21 coefficient
table in `Orbit21Coef.lean`, and `gen_o45_attain_rows.py` emits the explicit
Knill--Laflamme row proofs in `Orbit45AttainRows.lean`. The final theorems do not
trust Python: all emitted identities are rechecked by the Lean kernel.

Dedicated `Orbit7AxiomCheck.lean`, `Orbit8AxiomCheck.lean`,
`Orbit9AxiomCheck.lean` and `Orbit45AxiomCheck.lean` files expose the critical
dependency cones. `o45_gram.py` and `o45_attain_check.py` independently check
the Gram identities and the two numerical charts; they are diagnostics, not
members of the trusted proof base. Orbit 21's Walsh, residual, Farkas and final
headlines are included directly in `SixQubit/Audit.lean`.

### The ten realizations

| Generator | Emits |
|---|---|
| `genreal.py` | `SixQubit/Orbit<n>Real.lean` for n in 7, 8, 9, 10, 11, 16, 21, 22, 23, 45 |

One generator covers all ten because the shared layer `SixQubit/Realize.lean`
carries everything table-independent: the ring `Z[sqrt 2, sqrt 3, i]`, its
embedding into the complex numbers, and the theorem taking a decided certificate
to `SS.HasDistance`. A module contributes only its amplitude table, its support
lists and a rational scale. The generator re-checks the whole certificate in the
same eight-integer arithmetic before writing, so the kernel `decide` is a second
confirmation rather than the only one. Amplitudes and orbit records are parsed
from the source tables, never transcribed by hand.

### Orbit 36 (rigidity, not a no-go)

| Generator | Emits |
|---|---|
| `gen36code.py` | `SixQubit/Orbit36Code.lean` — the canonical pair, its fibers, `canonical_is_code` |
| `gen36.py` | `SixQubit/Orbit36.lean` — fibers, moment system, forced magnitudes, full support |
| `gen36alg.py` | `SixQubit/K4Kernel.lean` — the algebra layer the phase argument runs on |
| `gen36phase.py` | `SixQubit/Orbit36Phase.lean` — `A_1 = 0`, the triangle sum, the weight-two table |
| `gen36enum.py`, `gen36enum4.py` | `SixQubit/Orbit36Enum.lean`, `Orbit36Enum4.lean` — the enumerator through weight three, then four to six |
| `gen36class.py` | `SixQubit/Orbit36Class.lean` — classification up to local-monomial equivalence |
| `genmacw.py` | `SixQubit/MacWilliams.lean` — the subset MacWilliams identity at `n = 6` |
| `gen36final.py` | `SixQubit/Orbit36Final.lean` — the assembled headline |
| `gen36vac.py` | `SixQubit/Orbit36Vacuity.lean` — the non-vacuity witness |

Four hand-written closing modules now sit after this generated chain:
`BEnumerator.lean` supplies the B-transform; `CodeEquivEnum.lean` proves
composition/inversion of `Equivalent` and A/B invariance under the fixed
permutation, flips and logical swap; `Orbit36Transport.lean` proves the exact
kernel change from the manuscript's table representative
`(1,1,1,2,2,4; 0,1)` to the symmetric representative; and
`Orbit36Certified.lean` states the final code-level rigidity and A/B theorem
directly on the table fibers, together with an attained witness there.

`SixQubit/CodeEquiv.lean`, which defines the local-monomial equivalence and its
distance-preservation lemmas, is hand-written: it is problem-independent and
belongs with the `SS` infrastructure in spirit. Orbit 36 is checked by `rigidity.py`, not by
the four gates below, which key off the `no_go_of_moments` headline it does not
have.

## `verification/` — checks independent of Lean

These provide regression checks for questions compilation alone does not answer:
whether the selected orbit data, rows and auxiliary relations match their
intended specifications. They are not part of the Lean kernel's soundness chain.

| File | Claim it supports |
|---|---|
| `feas2.py`, `feasnew.py` | numerical feasibility/infeasibility probes for the full weight-≤2 system. **Both include controls** — `feas2.py` uses certified no-go orbits (orbit 25 must come out excluded, and does, residual 0.79); `feasnew.py` uses the *realizable* orbits 7, 8, 9, 36 as POSITIVE controls, and the optimizer finds exact solutions for all four (residuals ~1e-31). Without controls neither is a test |
| **`classify.py`** | **the anti-smuggling check.** Parses every headline theorem and accepts only exact `offSum = 0` / `diagBot = diagTop` / `MomentSystem` hypothesis forms. Unexpected or unparsed binders fail closed. Current result across all 51: **zero** |
| **`admis.py`** | **the weight check.** Resolves every mask and dressing definition and confirms `\|supp(e) ∪ supp(z)\| ≤ 2` for every parsed row. It independently cross-checks the headline classification so a syntactically unexpected row cannot disappear from both counts |
| **`momentgate.py`** | **the transcription check.** Verifies every declared `MomentSystem` row against the order the headline passes probabilities, using exact rational linear forms rather than variable-name sets. Its non-exhaustive `--selftest` mutates every module in memory and fails if any requested mutation is missed or not injected; this is regression evidence, not a completeness theorem for the checker |
| **`rigidity.py`** | **the orbit-36 check.** The four gates above key off the `no_go_of_moments` headline, so orbit 36 — the unique realized orbit certified to rigidity rather than only an exact WE image — is invisible to all of them. This verifies the same obligations for it: the symmetric gauge and its fibers; the manifest's exact original representative `(1,1,1,2,2,4)` at `q=5` with residue-`0,1` fibers; the residue-shift and logical-swap direction; the absence of smuggled hypotheses; all 22 KL rows and moment equations; and the final table-level theorem's exact physical hypotheses, magnitudes/full-support/direct-equivalence/A/B conclusion, and constructive original canonical witness. Its `--selftest` retains the 14 legacy injections and adds transport/closure injections (34 total); every mutation must be caught and zero may be inert |
| **`realized.py`** | **the realization check.** Each `Orbit<n>Real.lean` decides its own Knill–Laflamme certificate, so the kernel already proves the exhibited pair is a code. What the kernel cannot prove is that the pair belongs to the orbit the module is named for, since `manifest.json` is not a Lean object — exactly the defect that hit four no-go modules before `gate.py` existed. This checks orbit identity by canonical form, recomputes both fibers, and re-derives the amplitude norms in the same eight-integer ring the Lean uses. Six mutations in its `--selftest` |
| `mktable.py` | regenerates `results/orbit-table.tsv`: `q` and `a` are parsed from each Lean module and cross-checked with `tools/manifest.json`; `delta` and `m` come from the manifest; fiber sizes are recomputed from `(q,a,delta)`. Run `gate.py` separately to compare the Lean residue and support declarations with the manifest |
| `phase4.py` | which orbits admit isolable C² *inner products* (as opposed to single monomials) |
| `pin51.py` | the quadratic consequences that pin orbits 49 and 51 |
| `close31.py`, `branch31.py` | orbit 31 against the raw conditions; which phase partitions die |
| `collapse29.py`, `o29end.py`, `o29sym2.py` | orbit 29's support collapse and endgame |
| `diagrel.py`, `quad.py`, `oddcycle.py` | diagonal conditions as a linear system; quadratic closure; odd cycles |
| `stepA_*.py` | the four silent assumptions behind orbit 26's Step A, each recomputed from the raw system. `stepA_global.py` is an independent route through one 256-column system |
| `t26_*.py`, `x26_*.py` | orbit 26 facts, Farkas certificates, ablations, case tree. `t26_ablate.py` shows dropping `P_0+P_2+P_4 = 3/8` makes the fact set feasible again — that fact is load-bearing |
| `audit_spinor.py` | re-derives orbit 6 and 12's fibers and moment system from `(q,a,delta)` independently and re-checks their hypothesis lists |

The `stepA_*` and `x26_*` families exist because the first orbit-26 argument had
a real gap (per-anchor axis choices used as if global). They are the record of
finding it and of verifying the repair.

Run `gate.py`, `momentgate.py`, `classify.py`, `admis.py`, `rigidity.py` and
`realized.py`
together. They check different parts of the paper-to-Lean transcription and
deliberately fail on unrecognized input; none replaces the kernel build and
axiom audit. The first four cover the 51 no-gos; `rigidity.py` covers orbit 36,
which has no `no_go_of_moments` headline and so is outside their inventory.

With no orbit arguments, all four gates obtain the exact reviewed 51-module set
from `manifest.json` (`_no_go.lean_modules`) and fail if an expected file or its
top-level `no_go_of_moments` marker is absent, or if an unexpected module bears
that marker. Positional orbit arguments deliberately request a certified subset.
Their in-memory self-tests include whole-module and marker deletion checks.
