# A dyadic Bell ladder for transversal diagonal gates

Code, data, and machine-checked proofs for the dyadic Bell ladder.

> **Status.** `paper/dyadic_lifts.tex` is the development note, included so the
> repository is self-contained. A publication version will replace it. The note
> states and proves the ladder theorem *in the abstract* and exhibits no
> concrete code; the explicit seed, the unconditional family it generates, and
> the proof that the distance is exactly three live in `code/` and `lean/`, and
> are described below. The code and the Lean development therefore go beyond
> what the note claims — they discharge its hypotheses.

A transversal gate — one applied to each physical qubit separately — is the
cheapest kind of fault-tolerant gate. In every explicit family we know of,
making such a gate finer is expensive: at distance 3, a diagonal gate of
projective order `2^ν` costs `2^{ν+1}-1` qubits along punctured Reed–Muller
codes, `O(3^ν)` along divisible-code towers, and `2^ν+3` along
permutation-invariant spin codes. All three grow exponentially in `ν`.

This work shows the cost can be **linear**. A lift appends to a subset-sum code
a two-qubit Bell pair carrying the dyadic carry of the subset-sum residue, so
each lift adds two qubits and doubles the order of the induced transversal
diagonal gate.

Refining the phase is the easy half. The distance is not preserved
automatically, and the main theorem settles it by a finite computation:

> if a seed and its first lift satisfy the Knill–Laflamme conditions for every
> Pauli error of weight at most two, so does every rung above them.

**Two finite checks therefore certify an infinite family.** Applied to an
explicit `((7,2,3))` code with transversal `T`, this gives `((7+2r,2,3))` codes,
of exactly distance 3, whose transversal diagonal gate has projective order
`2^{3+r}`.

The theorem, the lemmas it rests on, and the seed's two finite checks are
verified in Lean 4 **by the kernel alone** — `native_decide` appears nowhere, so
neither the Lean compiler nor its runtime is trusted.

---

## Layout

```
paper/      the development note, and the scripts that re-derive its numbers
lean/       the Lean 4 formalization (source only; `lake build` fetches the rest)
code/       the numerics: the lift, the seed data, and the two verification runs
data/       the sweep results
results/    the theorem-hypothesis sweep report, and its consistency checker
six-qubit-orbit2/  independent kernel-checked orbit-2 enumerator certification
```

Nothing here is stale. Superseded drafts, intermediate outputs, and the
distance-2 parameter search (on which nothing here depends) are not included.

---

## What is verified, and how strongly

Three independent layers, in decreasing order of strength.

### 1. Lean 4, kernel only

`lean/` formalizes the ladder theorem, every lemma it rests on, and the seed's
two finite checks. Every proof is reduced by the Lean kernel; the trust base is
the kernel plus the three standard Mathlib axioms `propext`,
`Classical.choice`, `Quot.sound`.

That claim is enforced rather than asserted: `DyadicLifts/AxiomCheck.lean` (9
results) and `DyadicLifts/Seed/Audit.lean` (16 results) pin the axiom footprint
of every headline theorem with `#guard_msgs` + `#print axioms`, and both are in
the default target. If a `sorry` or a compiler-backed tactic ever enters a
dependency, **the build fails**.

| statement | Lean |
|---|---|
| the ladder theorem | `DyadicLifts.two_anchor_ladder` |
| seed KL conditions hold | `BD16Kernel.hKL0` |
| first-lift KL conditions hold | `BD16Kernel.hKL1` |
| every rung is a distance-3 code | `BD16Kernel.exists_distance3_family` |
| rung `r` has transversal diagonal `D_{2^r·8}` | `BD16Kernel.seed_rung_diagonal` |
| rung `r` has logical group `BD_{2^{r+1}·8}` | `BD16Kernel.seed_rung_binary_dihedral` |

**Scope.** The formalization proves distance **at least** 3 at every rung. The
matching upper bound — that the distance is exactly 3, witnessed by
`X⊗X⊗Z⊗id⊗…` with matrix element `−i√3/4` at every rung — is *not* formalized,
and the note does not state it either. In this repository it is only checked
numerically, by `paper/tools/check_exact_distance.py` at rungs 0–4 and
`check_witness_detail.py` at rung 0. Its proof will appear in the publication
version.

### 2. Independent numerics

`code/verify_paper_seeds.py` lifts all 14 published seeds four times and checks
distance 3 at every rung, in floating point, with no reference to Lean. Exit 0
on success.

### 3. A sweep over published codes

`code/verify_thm44_paper.py` tests the theorem's hypotheses against 43
instances: 33 codes whose codeword is printed in
[arXiv:2504.20847](https://arxiv.org/abs/2504.20847), 9 built here from angle
vectors listed in its Sec. 6.3.1, and the Steane code as a stabilizer control.

The 39 subset-sum instances are each lifted five times; the remaining four are
not subset-sum codes, so the lift is undefined and only their applicability is
classified. The outcome is

| verdict | count |
|---|---|
| hypotheses hold and every rung keeps `d ≥ 3` | **30** |
| counterexample | **0** |
| a hypothesis fails | 9 |
| not a subset-sum code, lift undefined | 4 |

Of the nine codes failing a hypothesis, eight also fail the conclusion — and
they fail where the mechanism predicts: four at rung 1, three at rung 2, one at
rung 3. `results/sweep_report.pdf` records all of it per code.

### 4. Two checks against self-confirmation

`code/verify_thm44_paper_2510.py` runs the same theorem over the ten Appendix-F
codes of [arXiv:2510.20728](https://arxiv.org/abs/2510.20728). They carry the
**same weight vectors** as `bd16_01..10` above but **different amplitude
representatives**, from that appendix's closed-form families. All ten confirm —
so the verdicts track the arithmetic hypotheses, not one choice of amplitudes.

`code/_adv_bd12_typeII.py` re-verifies a *failing* code from scratch **without
importing the distance checker used everywhere else**: independent transcription
of the codewords from the source LaTeX, every weight-≤2 Pauli built as an
explicit Kronecker product, the hypothesis arithmetic recomputed. It reproduces
the sweep's verdict for `bd12_type_II` (rung 0 passes, rung 1 onward fails), so
that verdict does not rest on a single implementation.

---

## Reproducing

Full commands, pinned versions and expected outputs are in
[`REPRODUCE.md`](REPRODUCE.md). The short version:

```bash
cd paper   && python tools/run_all_checks.py      # the numeric claims, ~1 min
cd results && python check_sweep_report.py        # the report against its data, <1 s
cd code    && python verify_paper_seeds.py        # 14 seeds x 4 lifts, ~2 min
cd lean    && lake exe cache get && lake build    # the whole formalization, ~3 h
```

Each exits nonzero if anything it checks no longer holds. `lake build` is
itself the audit: the axiom guards run inside it.

---

## The seed

The explicit code the family is built from is the `((7,2,3))` code with
transversal `T` of [arXiv:2504.20847](https://arxiv.org/abs/2504.20847),
Sec. 6.3.1, at the phase point `θ₁ = θ₂ = 0`. Angle vector `a = (1,2,2,2,2,3,3)`,
modulus `m₀ = 8`, and

```
4·|0_L⟩ = |0000000⟩ + √3|0111100⟩ + √3|1001110⟩ + √2|1010101⟩
        + √2|1011001⟩ + |1110010⟩ + 2i|0100011⟩
|1_L⟩   = X^{⊗7}|0_L⟩
```

Its angle vector satisfies the theorem's two conditions — `Σaⱼ = 15 = 2m₀−1`
and `max aⱼ = 3 ≤ 6 = m₀−2` — and both anchor-uniqueness hypotheses hold
sharply.

---

## What this is not

The rungs are `((n₀+2r, 2, 3))` codes: the distance is fixed while `n` grows,
so the rate falls to zero and no rung is a candidate for encoding at scale.
What the construction settles is a question about reach and cost, not about
performance. Exponential block-length growth is not intrinsic to refining a
transversal diagonal gate; it is a property of the constructions in which such
gates have so far been found.

Block lengths quoted for other families are lengths those families *achieve*.
For stabilizer codes a matching lower bound is known under the hypotheses of
[arXiv:2210.14066](https://arxiv.org/abs/2210.14066); for nonadditive codes we
know of no lower bound.

---

## Six-qubit orbit-2 enumerator certification

[`six-qubit-orbit2/`](six-qubit-orbit2/README.md) contains a separate,
self-contained Lean 4 certification of the exact orbit-2 enumerator image:

```text
(1, alpha, 1-alpha, 0, 11+4*alpha, 16-alpha, 3-3*alpha), 0 <= alpha <= 1.
```

The theorem assumes an isometric six-qubit encoder, full weight-two Pauli
Knill--Laflamme detection, and logical `IIZZZZ`. It proves the converse and
attainment of every parameter with exact distance three. The entire argument,
including the physical reductions and exact Gram certificate, is kernel
checked. The final theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`, with no admitted proof or native computation oracle.

This package has its own pinned toolchain and Mathlib dependency. It does not
change the dyadic-ladder formalization. See its README for the assumptions,
main theorem, verification logs, and build commands.

---

## Requirements

Python 3.12, `numpy`, `scipy`, `sympy` (see `requirements.txt`); TeX Live to
build the note (it uses `article` and an inline bibliography, so no BibTeX pass
is needed); `elan` for Lean, which pins the compiler and every dependency
itself.
