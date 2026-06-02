# Dyadic Bell Ladder — Lean 4 Formalization

A Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4) formalization
of the **nonadditive dyadic Bell ladder** for two-sector SS–LP quantum codes: the
two-anchor Bell-flag ladder theorem and its supporting results, together with an
**unconditional, machine-checked infinite family of distance-3 codes** obtained by
feeding a concrete `((7,2,3))` BD16 code into the ladder.

The development targets the paper `dyadic_lifts.tex` and its Lean-oriented companion
note `dyadic_theorem_lean.tex`. For the full audit and scope report see
[`FORMALIZATION_REPORT.md`](FORMALIZATION_REPORT.md); for the per-result coverage map
and trust-base notes see [`DyadicLifts/COVERAGE.md`](DyadicLifts/COVERAGE.md).

---

## Prerequisites

You only need **`elan`**, the Lean toolchain manager. Everything else (the exact Lean
compiler version, Mathlib, and all dependencies) is pinned by this repository and
fetched automatically.

- **Install `elan`** (if you don't have it):
  - macOS / Linux:
    ```bash
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    ```
  - Windows (PowerShell):
    ```powershell
    curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
    powershell -ExecutionPolicy Bypass -f elan-init.ps1
    ```
  - Or via a package manager (`brew install elan-init`, etc.).
- The pinned toolchain (`leanprover/lean4:v4.27.0`, see `lean-toolchain`) is installed
  automatically by `elan` the first time you run `lake`.
- A network connection is needed for the first build (to download the Mathlib build
  cache), plus roughly **10 GB of free disk** for `.lake/` (Mathlib oleans + build
  artifacts).

No global Lean or Mathlib installation is required — the build is fully project-local
under `.lake/`.

---

## How to reproduce

From the repository root, run exactly two commands:

```bash
# 1. Download the prebuilt Mathlib oleans (fast; avoids compiling Mathlib from source).
lake exe cache get

# 2. Build the whole development (shared library + abstract ladder + concrete examples).
lake build
```

A clean exit with **`Build completed successfully`** and **no errors** reproduces the
entire formalization. On a warm Mathlib cache this takes a few minutes.

What `lake build` checks:

- it builds the three libraries `SS`, `DyadicLifts`, and `Examples`;
- it runs `DyadicLifts/AxiomCheck.lean`, which **fails the build** if any headline
  theorem ever acquires a `sorry`/`sorryAx` or an unexpected axiom.

> **If you skip step 1**, `lake build` will compile Mathlib *from source* instead,
> which is very slow (tens of minutes to hours). Always run `lake exe cache get`
> first.

### The unconditional distance-3 family (opt-in, slow)

The headline Tier-3 result lives in `Examples/D3/BD16Ladder.lean` and is **not** part
of the default build, because it runs two `native_decide` Knill–Laflamme
verifications over an exact algebraic number field — a one-time native-code
compilation that takes roughly **45–55 minutes from scratch**. Build it explicitly:

```bash
lake build Examples.D3.BD16Ladder
```

It establishes

```lean
theorem BD16Ladder.exists_distance3_family (r : ℕ) :
    KL (psr 8 a0 ψ0 false r) (psr 8 a0 ψ1 true r)
```

i.e. every rung of the dyadic Bell ladder over the concrete BD16v1 seed satisfies the
full distance-3 Knill–Laflamme conditions.

---

## Troubleshooting

- **`lake: command not found`** — `elan` is not installed or not on your `PATH`.
  Install `elan` (see Prerequisites) and reopen your shell.
- **`lake build` recompiles all of Mathlib (very slow)** — you skipped
  `lake exe cache get`, or the cache did not match. Run `lake exe cache get` first.
- **Windows: `lake exe cache get` prints `failed to execute 'tar': … non UTF-8 data`**
  — this only affects the *optional* `ProofWidgets` release blob (interactive VS Code
  widgets), **not** proof checking. `lake build` still succeeds. You can ignore it,
  or run `lake build ProofWidgets` once beforehand.
- **Moving/copying this folder** — copy the *source* folder only (it does not contain
  `.lake/`). After copying, re-run the two commands above in the new location. Do not
  copy a prebuilt `.lake/` between machines or paths; it contains machine-specific
  absolute paths and is not portable — delete it and rebuild.

---

## What is proved

| Result | Location |
|---|---|
| **Two-anchor Bell-flag ladder theorem** (every rung is distance ≥ 3) | `DyadicLifts/DistanceTheorem.lean` (`two_anchor_ladder`) |
| Iterated doubled diagonal `D_{m_r}` | `DyadicLifts/DistanceTheorem.lean` (`rung_diagonal`) |
| Binary-dihedral group `BD_{2m_r}` on the rung code | `DyadicLifts/LogicalGroup.lean` (`rung_binary_dihedral`) |
| Exact diagonal orders | `DyadicLifts/CyclicOrder.lean` (`orderOf_Rm`, …) |
| General carry-tag lift criterion (paper §2) | `DyadicLifts/CarryTag.lean` (`strong_carry_tag`) |
| Exact-field → ℂ bridge for `native_decide` KL checks | `DyadicLifts/Bridge.lean` (`KLmat_of_KLmatK`, `liftVec_bridge`) |
| **Unconditional infinite distance-3 family** | `Examples/D3/BD16Ladder.lean` (`exists_distance3_family`) |
| Concrete distance-3 BD16 codes (12 examples) | `Examples/D3/BD16v*.lean` |
| Distance-3 no-go results | `Examples/D3/NoGo/` |
| Distance-2 SS–LP examples | `Examples/D2/` |
| Shared SS toolkit (residues, Z-type KL, exact fields) | `SS/` |

### Trust base

- The abstract ladder, the bridge lemmas, and the logical-group results depend only on
  the three standard Lean/Mathlib axioms `propext`, `Classical.choice`, `Quot.sound`
  (pure kernel proofs; no `sorry`).
- The concrete finite KL verifications (`Examples/D3/BD16*`, and hence
  `exists_distance3_family`) additionally use `native_decide`, which adds
  `Lean.ofReduceBool` and `Lean.trustCompiler`. This is the standard way to discharge
  finite exact-arithmetic facts in Lean; it enlarges the trust base to include the
  Lean compiler and the exact-field arithmetic, but introduces no `sorry`.

### Checking there are no `sorry`s

```bash
grep -rnE '\b(sorry|admit)\b|^\s*axiom ' DyadicLifts SS Examples \
  --include='*.lean' | grep -v '`sorry`'
```

The only textual matches are in comments/docstrings. The build itself is the strongest
check: Lean's kernel rejects any gap.

---

## Project layout

```text
.
├── lakefile.lean        # Lake package (default targets: SS, Examples, DyadicLifts)
├── lean-toolchain       # pinned Lean version (v4.27.0)
├── lake-manifest.json   # pinned Mathlib + dependency commits
├── DyadicLifts/         # the abstract dyadic Bell ladder (main development)
│   ├── COVERAGE.md       # per-result coverage map + scope/trust notes
│   └── AxiomCheck.lean   # axiom-footprint regression guard
├── SS/                  # shared toolkit (subset sums, Z-type KL, QSqrt235i, BD16)
├── Examples/            # concrete codes: D2 (distance-2), D3 (BD16 distance-3, no-go)
└── FORMALIZATION_REPORT.md
```
