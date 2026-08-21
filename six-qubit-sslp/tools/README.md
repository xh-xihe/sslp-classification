# Tools

The Python that produced the Lean, and the independent checks that decided what
the Lean should say. Everything here is byte-identical to what was actually run.

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

Every certified orbit and every algebra layer, with the script that emits it.
**This table is the reproduction map**; if a row is wrong, the artifact is not
reproducible and that is a defect.

### First batch (from `six_qubit_sslp_v7.tex`)

| Orbits | Generator(s) | Emits |
|---|---|---|
| 25 | `gen15.py`, `gen15b.py`, `gen15c.py`, `gen15d.py` | `SixQubit/Orbit25.lean` — first orbit needing the diagonal layer |
| 26 | `gen26f.py` (staged: `python gen26f.py <stage>`) | `SixQubit/Orbit26.lean`; algebra in `SixQubit/Block26.lean` |
| 29 | `gen29a.py`, `gen29c.py`, `gen29pf.py` | `SixQubit/Orbit29.lean`, parts of `SixQubit/Pair29.lean` |
| 31 | `gen31.py` | `SixQubit/Orbit31.lean`; algebra in `SixQubit/Table31.lean` |
| 33 | `gen16.py`, `genblock.py` | `SixQubit/Orbit33.lean`, `SixQubit/Block33.lean` |
| 27, 28, 30, 32, 34–35, 37–40, 53–66 | closed by the mechanism ladder in `core/scan.py` + `core/cert.py` | their `SixQubit/Orbit<n>.lean` |

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

## `verification/` — checks independent of Lean

These answer questions the Lean proofs do not: is the orbit excluded at all, is a
relation genuinely available, is a branch live, is a claimed proof honest.

| File | Claim it supports |
|---|---|
| `feas2.py`, `feasnew.py` | the full weight-≤2 system is numerically unsatisfiable. **Both include controls** — `feas2.py` uses certified orbits (orbit 25 must come out excluded, and does, residual 0.79); `feasnew.py` uses the *realizable* orbits 7, 8, 9, 36 as POSITIVE controls, and the optimizer finds exact solutions for all four (residuals ~1e-31). Without controls neither is a test |
| **`classify.py`** | **the anti-smuggling check.** Parses every headline theorem and classifies each hypothesis as `offSum = 0` / `diagBot = diagTop` / `MomentSystem`. Anything else is an algebraic fact taken as an assumption, which voids the proof invisibly from the outside. Current result across all 51: **zero** |
| **`admis.py`** | **the weight check.** Resolves every mask and dressing definition and confirms `\|supp(e) ∪ supp(z)\| ≤ 2` for every row used. A weight-3 row would silently turn a distance-three no-go into a much weaker distance-four claim |
| **`momentgate.py`** | **the transcription check.** Verifies every `MomentSystem` row against the order the headline actually passes probabilities, identifying rows by CONTENT rather than name so a renamed or reordered row cannot slip past. `--selftest` injects 749 corruptions (dropped terms, reindexed terms, swapped sides, broken normalizations, renamed-and-corrupted rows) and asserts every one is rejected — a checker never shown to fail is not evidence of anything |
| `mktable.py` | regenerates `results/orbit-table.tsv`: `q` and `a` are parsed out of each Lean module and cross-checked, while `delta` and the fiber sizes come from `tools/manifest.json`, so the table cannot drift from what is actually proved |
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

`classify.py` and `admis.py` are the two that a reviewer should run first: they
check not that the proofs compile, but that they prove the right thing.
