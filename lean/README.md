# Dyadic Bell Ladder — a kernel-only Lean 4 formalization

A [Lean 4](https://lean-lang.org) + [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of the nonadditive dyadic Bell ladder for two-sector SS–LP quantum codes:
the ladder theorem and its supporting lemmas, the carry–tag framework and the
binary-dihedral logical group it induces, and — instantiating all of it — an explicit
`((7,2,3))` seed whose Knill–Laflamme conditions are decided by the kernel, yielding an
infinite distance-3 family with no hypotheses left open.

Every proof here is reduced by the Lean kernel. `native_decide` appears nowhere, so
nothing rests on the Lean compiler or its runtime; the trust base is the kernel and the
three standard Mathlib axioms `propext`, `Classical.choice`, `Quot.sound`.

That claim is enforced, not asserted. `DyadicLifts/AxiomCheck.lean` (9 results) and
`DyadicLifts/Seed/Audit.lean` (16 results) pin the axiom footprint of every headline
theorem with `#guard_msgs` + `#print axioms`. Both are in the default target, so if a
`sorry` or a compiler-backed tactic ever enters a dependency the **build fails**.

## What is proved

The abstract ladder, against the labelled statements of `dyadic_lifts.tex`:

| paper | Lean |
|---|---|
| `thm:two-anchor-bell` | `DyadicLifts.two_anchor_ladder` |
| `thm:phase-lift-template` | `DyadicLifts.phase_lift_template` |
| `prop:strong-carry-tag` | `DyadicLifts.strong_carry_tag` |
| `lem:bell-pauli` | `DyadicLifts.Bell` (all sixteen two-qubit overlaps) |
| `lem:two-value-subsets` | `DyadicLifts.Combinatorics` |
| `lem:no-small-weight-Smr1` | `DyadicLifts.NoSmallWeight` |
| `lem:bell-recursion` | `DyadicLifts.AnchorRecursion` |
| `lem:buddy-unique` | `DyadicLifts.Buddy` |
| `lem:anchor-leakage` | `DyadicLifts.AnchorLeakage` |
| `def:carry-dephased-kl` | `DyadicLifts.CarryDephasedKL` |
| `def:tag-invisibility` | `DyadicLifts.TagInvisible` |

Those are every labelled statement in that note; its §5 (the generalized-concatenated-code
viewpoint) is discussion and states none.

The "Moreover" clauses of `thm:two-anchor-bell` — that the induced transversal diagonal on
rung `r` is `D_{m_r}` with `m_r = 2^r m_0`, and that a self-complementary seed gives every
rung the binary-dihedral group `BD_{2m_r}` — are `DyadicLifts.logical_diagonal_order_doubles`
and `DyadicLifts.rung_binary_dihedral`, resting on the exact orders `orderOf_Rm = 2m` and
`Dm_pow_smul_one_iff`.

### The seed, and what it removes

`DyadicLifts.two_anchor_ladder` is conditional: it assumes the Knill–Laflamme conditions
at the seed and after the first lift. `DyadicLifts/Seed/` discharges both hypotheses for a
concrete code, so the family below is unconditional.

| statement | Lean |
|---|---|
| seed KL conditions hold | `BD16Kernel.hKL0` |
| first-lift KL conditions hold | `BD16Kernel.hKL1` |
| every rung is a distance-3 code | `BD16Kernel.exists_distance3_family` |
| rung `r` has transversal diagonal `D_{2^r·8}` | `BD16Kernel.seed_rung_diagonal` |
| rung `r` has logical group `BD_{2^{r+1}·8}` | `BD16Kernel.seed_rung_binary_dihedral` |

`exists_distance3_family` is the unconditional statement: for every `r`, the two rung-`r`
codewords on `n_r = 7 + 2r` qubits (`DyadicLifts.nr`, which appends one Bell pair per lift)
are orthonormal and satisfy the Knill–Laflamme equations for every Pauli of weight at most
two — an `((7+2r, 2, 3))` nonadditive code, distance bounded below. It depends on nothing
but the three Mathlib axioms.

The modulus, not the length, is what doubles: `m_r = 2^r m_0` (`DyadicLifts.mr`), so rung
`r` carries a transversal diagonal of order `2^{3+r}` on `7 + 2r` qubits. That gap between
linear length and exponential gate order is the point of the construction.

**Scope.** The formalization proves distance **at least** 3 at every rung. The matching
upper bound — that the distance is exactly 3, witnessed by `X⊗X⊗Z⊗id⊗…` with matrix
element `−i√3/4` at every rung — is proved in the manuscript and checked numerically, but
is not formalized here.

### How the seed checks are made to fit

Deciding the seed's KL conditions by the kernel alone is not free, and three things make
it finish. They are documented at the head of each module and summarized here because they
are the reason this package exists in kernel-only form.

- **An integer mirror.** The kernel cannot reduce `Rat`: `Rat.normalize` calls `Nat.gcd`,
  which is well-founded recursion the kernel will not unfold. `SS/ZSeedKL.lean` therefore
  carries the amplitudes in `ℤ[√2,√3,√5,i]` scaled by a nonzero rational. The KL
  constraints are quadratic, so the scale cancels and vanishing and equality are preserved.
  `Int` is GMP-backed in the kernel, so this path reduces.
- **Short-circuited multiplication.** `mulL`/`mulR` inspect one argument and return early
  on `0` and `1` without touching the other. The kernel does not evaluate an argument it
  never reaches; measured against the naive product this is the difference between about
  8.5 hours and about 18 minutes.
- **A support decomposition instead of enumeration.** `SS/PauliSites.lean` proves
  `pauli_le_two_decomp`: a Pauli of weight ≤ 2 is the identity, a one-site operator, or a
  two-site operator. That replaces a `4^n` sweep by a sum over supports.
- **One declaration per position.** The kernel holds one weak-head-normal-form cache per
  declaration and frees it only at the end of that declaration — about 4.5 GB per minute
  here. `DyadicLifts/Seed/Checks.lean` is therefore split into 75 declarations, which
  bounds the live cache by the cost of a single position.

`Checks.lean` is generated. Regenerate it with `python gen_checks.py` from this directory;
the script rewrites the file in place and is byte-reproducible.

[`DyadicLifts/COVERAGE.md`](DyadicLifts/COVERAGE.md) maps every module to what it carries
and states the boundaries of the result.

## Building

You need only [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager;
the compiler version (`leanprover/lean4:v4.27.0`) and every dependency are pinned by this
repository.

```bash
lake exe cache get     # prebuilt Mathlib artifacts, a few minutes
lake build             # the whole verification
```

`lake build` is the audit — both axiom guards are part of the default target. Budget about
**three hours** for a first build. Nearly all of it is a single module:
`DyadicLifts.Seed.Checks` measured 10,487 s (2.9 h) on a 24-core Windows machine. The rest
of the development takes about 1.5 minutes once Mathlib is in place, and `Seed.Ladder`,
`Seed.Audit` and the root module together take under a minute. Rebuilds after an edit
outside `Seed.Checks` replay that module from cache and finish in seconds.

The seed's checks enumerate `Finset.univ` over `BitString 9` by structural recursion,
which overflows the default 8 MB thread stack. The package raises it itself
(`moreLeanArgs := #["-s", "2000000"]` in `lakefile.lean`), so plain `lake build` suffices —
no environment variable to remember.

On Windows, `lake exe cache get` may report a `tar` error while unpacking the optional
ProofWidgets blob. That blob is editor decoration; proof checking is unaffected. If it
blocks the fetch, unpack it once by hand and re-run:

```bash
tar -xz -f .lake/packages/proofwidgets/.lake/ProofWidgets4.tar.gz \
    -C .lake/packages/proofwidgets/.lake/build
```

## Checking the claims yourself

```bash
# no compiler-backed tactics, no holes
grep -rn "native_decide" DyadicLifts SS
grep -rnw "sorry\|admit\|axiom\|unsafe" DyadicLifts SS
```

Both should return only documentation comments. For the axiom footprint of any theorem,
ask Lean directly:

```lean
import DyadicLifts
#print axioms BD16Kernel.exists_distance3_family
-- 'BD16Kernel.exists_distance3_family' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

## Layout

```
DyadicLifts/          27 modules — the abstract ladder, and AxiomCheck
DyadicLifts/Seed/      4 modules — the ((7,2,3)) seed: Defs, Checks, Ladder, Audit
SS/                   11 modules — bitstrings, Pauli strings, the exact fields
                                   ℚ(√2,√3,√5,i) and ℤ[√2,√3,√5,i], the integer
                                   mirror (ZSeedKL) and the support decomposition
                                   (PauliSites)
gen_checks.py                     — regenerates DyadicLifts/Seed/Checks.lean
```

The `SS` modules are shared with the SS–LP search development, which keeps its own
repository; nothing specific to that project is carried here.
