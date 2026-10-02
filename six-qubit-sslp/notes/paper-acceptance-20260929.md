# 20260929 manuscript acceptance

`documents/20260929/supplementary.tex` is byte-identical to 20260924. `main.tex`
rewrites Section III against Bei Zeng's Lean formalization of that section,
which this repository carries as the [`QECC`](../QECC/README.md) library. The
abstract, the introduction, parts of Section II and the opening of Section IV
also changed. No review status was transferred from 20260924; every entry
listed below was reviewed again against the 20260929 text.

```text
python tools/paper_claims.py check --paper-version 20260929
python tools/named_results_doc.py --paper-version 20260929 --check
python tools/prose_review_doc.py --paper-version 20260929 --check
python tools/verify.py --paper-version 20260929 --only release audit-names named-results axioms
python tools/verify.py --paper-version 20260929 --only claims prose-review errata
```

The fourth command passes. Its axiom gate takes 1859 roots: the audit files,
including the seventeen QECC main declarations, plus every declaration a
covered ledger entry or a covered prose assertion cites. All of them exist in
the kernel environment, and their union of axioms is `propext`,
`Classical.choice` and `Quot.sound`. The fifth command fails, because the
review is incomplete and eight errata stand. Logs are in
`tmp/verification/20260929/`.

## What was reviewed

[`paper-migration-20260924-to-20260929`](../results/paper-migration-20260924-to-20260929.md)
lists the candidates: 1703 ledger entries, of which 1605 have a byte-identical
20260924 statement, 14 changed, 78 are new and 6 are ambiguous duplicates. The
review covered:

- all 145 ledger entries of Section III (main.tex lines 606-2074) and all of
  its running prose, including assertions inside proofs;
- the running prose outside Section III that changed since 20260924;
- the 16 entries outside Section III that had a 20260924 review;
- the supplement's references into main.tex, which the rewrite can break even
  though the supplement did not change;
- the four recorded errata and the 20260924 prose assertions.

Each of ten chunks was read by one agent, attacked by a second that re-read
the sources and the cited declarations, and settled by a third where the two
disagreed. A consistency reviewer then compared all chunks. It found six
contradictions in four groups, and each group was re-judged under one stated
rule by a resolver and an adversarial verifier. No agent ran Lean. Names were
then checked mechanically, and the kernel gate above checked them again. The
method is recorded in full in the
[prose review record](../results/prose-review-20260929.json).

## Results

| Range | covered | partial |
| --- | ---: | ---: |
| III.A finite diagonal logical groups (606-1054) | 23 | 25 |
| III.B SSLP as a classification normal form (1055-1430) | 31 | 2 |
| III.C bounds on the physical order (1431-2074) | 41 | 23 |
| main.tex outside Section III (re-reviewed entries) | 2 | 5 |
| supplementary.tex (re-reviewed entries) | 6 | 3 |

The ledger is **103 covered, 58 partial, 1542 unreviewed**. These are review
statuses, not a measure of how much mathematics is proved.

Seven of the eleven named results of Section III are covered:
`lem:uniform-rational-section`, `thm:finite-projective-group`,
`thm:general-sslp-normal-form`, `cor:rank-two-sslp`, `lem:phase-sectors`,
`lem:denominator-clearing` and `thm:colored-finite-lift`. Four are partial:

- `ex:seven-qubit-rationalization`: the worked seven-qubit example is not
  formalized; its general mechanism is.
- `lem:common-mean-rational-replacement`: Lean states the replacement for the
  phase sectors of a code under Z detection, with the explicit scalar. It does
  not state it for an abstract direct sum of subspaces on arbitrary supports
  sharing a mean.
- `lem:positive-affine-moments`: proved for supports inside {0,1}^n, which is
  the case the paper uses. The lemma is stated for arbitrary finite point sets.
- `cor:d3-physical-order-bound`: see the two structural findings below.

### Two structural findings

**The two libraries encoded d_s(C) differently; this is now bridged.**
MainTheory works with an actual Smith witness. It proves that every witness
of a matrix has the same last factor, and builds `betaOf` on it. QECC defines
`finalSmithInvariant` as the exponent of the integer cokernel, and
`smithBeta` as its maximum. The manuscript asserts that the two coincide (the
sentence near main.tex line 1580). When the review began, no declaration
proved that. [`MainTheory.QECCSmithBridge`](../MainTheory/QECCSmithBridge.lean)
now does:
- `finalSmithInvariant_eq_lastFactor`: the cokernel exponent is the last
  factor of every Smith witness;
- `smithBeta_betaExact` and `smithBeta_eq_betaOf`: for nu >= 1, `smithBeta nu`
  is the exact beta_nu and equals `betaOf nu`.

All three use only the standard axioms. The affected entries and prose items
were re-judged with the bridge. The sentence at line 1580 is now covered.
`cor:d3-physical-order-bound`, `eq:d3-full-bound`, `eq:d3-qmin` and the
displays at lines 1703 and 2022 remain partial. Their Smith and beta clauses
are now the manuscript's, but QECC states them for the supports of an
internally chosen representative (next finding).

**Several QECC quantities belong to a representative chosen inside a
proof.** QECC's sector count ell, its supports T_k and its affine dimension r
are attached to a reduced representative chosen inside the proof, not to the
gate D(theta) the paper starts from, and no invariance lemma relates the two.
Where MainTheory states the result for the given gate (for example
`PaperColoredFiniteLift.colored_finite_lift_of_zDetects`, which uses the given
gate's eigenvalue count), the clause is covered through it. Otherwise it is
partial. For the distance-three entries above, this and the missing rank-one
identity between projector-diagonal supports and eigenvector supports are now
the only reasons left.

### Entries that were covered for 20260924 and are partial now

The 20260929 review applied one rule throughout: the Lean objects must be the
manuscript's objects. Four entries that the 20260924 review covered do not
meet that rule:

- `thm:six-15-sslp-realization-orbits` and supplementary `thm:main-result-II`
  count paper classes. The Lean count is over the 66 directory keys. No
  declaration identifies those keys with the candidate classes as
  `def:six-sslp-orbits` now words them, including its support-dimension
  clause. The realizability of each key is carried.
- `thm:six-WE-status` and supplementary `thm:main-result-III` concern the
  class-level W_r of `def:six-classification-levels`. The Lean equalities are
  for `Levels.WImage` at the table representative. No declaration shows that
  the image does not depend on the representative.

Neither is a doubt about the mathematics. Each needs one bridging declaration.

## Prose

The [prose review](../results/prose-review-20260929.md) records 291
assertions: 107 covered, 121 tracked, 34 gaps and 29 nonmath. Three gaps are
high:

- The reduction to a finite enumeration that the abstract (line 76) and the
  introduction (line 177) claim for general K. It needs the normal form at a
  representative that also obeys the uniform order bound. Only K=2 is
  carried.
- The unqualified Singleton display (line 274), the standing erratum.

The supplementary prose beyond its references into main.tex, and the
unchanged main.tex prose outside Section III, were not reviewed for this
version.

## Errata

[`errata-20260929.json`](../results/errata-20260929.json) carries the four
20260924 dispositions, unchanged in substance, and five new ones. All five are
in text that is new or renumbered in 20260929:

- the supplement's hard-coded "Corollary III.4" (proof of Result I, line 5772)
  now names a different result than in 20260924;
- the last step of the proof of `thm:colored-finite-lift` describes q_min as a
  minimum over all physical representatives, which contradicts `eq:qmin`;
- the introduction's roadmap (lines 172-176) states finiteness without the
  single-site Z detection hypothesis;
- the bridge sentence after `eq:logical-basis-KL` (lines 269-272) holds only
  for diagonal errors;
- the lead-in to `lem:uniform-rational-section` (lines 684-686) says the
  wrong component stays fixed.

Two further candidates were judged not to be errata and are recorded with the
reason. The author instruction to leave the manuscripts unchanged still
applies; no TeX was edited.

## Next work

- Invariance of QECC's ell, T_k and r under change of reduced representative,
  or given-gate versions of the distance-three statements, together with the
  rank-one support identity. With the Smith bridge in place, this is what
  `cor:d3-physical-order-bound` and its displays still need.
- The two six-qubit bridges: the 66 directory keys against
  `def:six-sslp-orbits` as worded, and representative independence of
  `Levels.WImage`.
- Review of the remaining 1542 entries and of the unchanged prose. The
  20260908 reviews are background for this, not evidence.
