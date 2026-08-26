---
name: sslp-orbit26-hexagon
description: "HISTORICAL orbit-26 work log, including the rejected per-edge argument and the completed cross-anchor repair."
metadata:
  type: project
---

> **HISTORICAL WORK LOG; CURRENT PROOF COMPLETE.** The body preserves several
> chronological checkpoints, so statements such as “NOT yet certified,” old
> line counts, and “what remains” are intentionally historical rather than
> current status. Orbit 26 is now kernel-certified in
> `SixQubit/Orbit26.lean`, with its algebra in `SixQubit/Block26.lean` and its
> code-level wrapper in `SixQubit/CodeOrbit26.lean`. The current per-orbit counts
> are generated in `results/orbit-table.tsv`.

Orbit 26 (`a = (0,1,1,2,2,3)`, `q = 4`, `delta = 1`, fibers 16+16).  NOT yet
certified; everything below is verified numerically/symbolically.

## Structure

Qubit one has angle zero, so each fiber splits into eight blocks of two.  Tails
are `t(x,y,z) = (x, y, z, z xor xy, x xor y)`.  In sorted order my block indices
are `0..7 = A,B,E,F,C,D,G,H` (paper labels), i.e. tails

    0:00000  1:00110  2:01001  3:01111  4:10001  5:10111  6:11010  7:11100

Tail distances decide the conditions: distance 4 gives a MATRIX relation,
distance 3 a SCALAR one, distance 2 nothing.  The result is remarkably clean:

* blocks `0..5` form a **6-cycle** of matrix relations, `0-3-4-1-2-5-0`;
* blocks `6,7` (the anchor group) have NO matrix relation to anything and a
  scalar relation to every one of `0..5`.

Group the blocks in pairs by the virtual bit `z`, indexed by `(x,y)`:
`{0,1}, {2,3}, {4,5}, {6,7}` (the last is the anchor).  Then the diagonal
conditions for `F` on qubit one together with `F Z_j` on the tail bits carrying
`x, y, x xor y` (six-qubit positions 1, 2, 5) give the **matrix moment
identity**

    C_g C_g^dagger + D_g D_g^dagger = rho / 2,     rho = sum_g C_g C_g^dagger,

verified in the span for every group and every matrix entry.

## Moment facts (all exact against the moment system)

`P_i = Q_i` for all eight blocks; `P_6 = P_7 = 1/8`; `sum_{i<6} P_i = 3/4`; and
the three antipodal sums on the cycle are each `1/4`:
`P_0+P_1 = P_3+P_2 = P_4+P_5 = 1/4`.

LP enumeration of which blocks can vanish: at most TWO of `0..5`, and every
feasible pair is **adjacent on the 6-cycle** (exactly the six edges).  So the
live set is always a connected path of at least four vertices.

## RESOLVED -- the algebra layer is rebuilt and installed

`SixQubit/Block26.lean` (415 lines, 19 theorems, all axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings) REPLACES the flawed
version.  Theorems: `mul_conj_self`, `axis_lemma`, `axis_isotropic`, `contract`,
`cross_anchor`, `per_anchor`, `mixed_core`, `branch4a`, `branch3_step`,
`unit_pair_orthogonal`, `branch2_step6`, `lagrange`, `cauchy_schwarz_unit`,
`branch4b_core`, `branch4b`, `branch1`, `branch4_aligned`, `branch3_aligned`,
`branch1_full`.

THE REPAIR.  Contract the outer identity on the `a` index with `D_7` and on the
`b` index with `conj(C_6)` -- DIFFERENT anchors in the two slots.  After
substituting the anchor scalar relation `Y = -X` this is exactly

    R_g^(7) J R_h^(6)^T + R_h^(7) J R_g^(6)^T = 0,   g < h.

In the mixed configuration (anchor 6 on one axis, anchor 7 on the other) it reads
`a_g b_h + a_h b_g = 0` for the three pairs, whose only solution has one of the
six entries zero.  That kills the mixed branch, which was the specific fatal gap.

TWO CAVEATS, both verified rather than assumed:

* the cross-anchor relation is VACUOUS in the aligned branch (residuals all zero
  -- both coordinate axes are J-isotropic).  Aligned is closed separately by a
  moment / Cauchy-Schwarz argument (`branch4b`), NOT by the cross relation.
* so "the cross-anchor contraction repairs the gap" means "repairs the MIXED
  branch"; branches 1, 2 and 4b need the moment and positivity facts.

ONE FACT MUST BE ADDED to the working list:

    (T2)  P_0 + P_2 + P_4 = P_1 + P_3 + P_5 = 3/8

It is a proven consequence of the moment system (remainder 0 under
`cert.reduce_mod_linear`), INDEPENDENT of `(T)`, and an ablation shows it is
exactly what is load-bearing: dropping it makes the whole fact set feasible
again, precisely at the aligned point `P = (0,1/4,0,1/4,0,1/4,1/8,1/8)`.

Also confirmed: orbit 26 really is excluded by the full weight-<=2 system.  Best
residual on the normalised sphere is `1/sqrt(3)` over 550 starts (random plus
diagonal- and off-diagonal-seeded), with the minimum equalling the 1st percentile
in every batch.  Controls behave: diagonal-only relaxes to `3e-16`, off-diagonal
only solves exactly 40/40.

STILL TO BUILD for orbit 26: the transcription layer (fibers 16+16, the moment
normal form including `(T)` and `(T2)`, the outer identity's twelve entries, the
twelve anchor scalars, and the grouped diagonal conditions), then the assembly.

## The earlier correction (kept for the record)

An earlier version of this note claimed a short route built on PER-EDGE matrix
relations `D_i C_j^dagger + D_j C_i^dagger = 0` on the 6-cycle.  **Those do not
exist.**  Checked by rref on each mask's row space:

* the weight-one masks (`010000`, `001000`, `000001`) have EIGHT incidences and
  rank only FOUR -- they cover TWO cycle edges at once;
* the weight-two partners (`110000`, `101000`, `100001`) have rank TWO;
* **no two-term relation is available on any of them.**

What IS available off-diagonally:

* per GROUP PAIR `0 <= g < h <= 2`, the paper's outer identity
  `conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0` (four entries).  Its `(1,0)` entry
  is literally `star(b0)s3 + star(b1)s2 + star(b2)s1 + star(b3)s0 = 0`, the SUM
  over the two edges;
* per (cycle block `i`, anchor block `j`), the scalar relation
  `C_j^dagger D_i + C_i^dagger D_j = 0` -- these twelve ARE individually
  available, one mask giving two of them.

So `SixQubit/Block26.lean` compiles and its lemmas are true as conditional
statements, but `overlaps_vanish` and `finish26` take hypotheses the
Knill-Laflamme conditions do not supply.  They CANNOT certify orbit 26 as they
stand.  This is the same trap as the earlier collapse mistakes: never assume a
relation's shape without checking it lies in the mask's row space.

## PRE-CHECK: all four silent failure modes HOLD (machine-verified)

An adversarial pass had flagged four assumptions behind the Step A contraction,
each of which would make it produce `0 = 0` with no symptom.  All four were then
verified against the actual Walsh row spaces by two independent routes (per-mask
row spaces, and one global 72x256 system of rank 30), which agree on every
verdict:

* (a) R1's relative coefficient is `omega = +1` in all twelve instances, so the
  prefactor `(1+omega) = 2` is NOT zero.  The `omega = -1` variant and the
  SYMPLECTIC variant (`J` replaced by `[[0,1],[-1,0]]`) are NOT implied for any
  instance.  The form really is the SYMMETRIC `J = [[0,1],[1,0]]` -- essential,
  since "three nonzero pairwise J-orthogonal rows lie on one axis" is FALSE for
  the symplectic form.
* (b) R2's per-block ratio is `mu_i = -1` for all twelve, no variation.  The
  worry that the residues `2` and `3` in `a` could produce per-block Pauli phases
  is structurally impossible in this parametrisation: `X^e Z^z |y> =
  (-1)^{z.y} |y^e>` makes every coefficient a real sign, and a `Y` factor
  contributes one global `i` to the whole condition.  The residues affect only
  WHICH strings lie in `S0`/`S1`.
* (c) One global virtual-bit labelling gives J-form for all three group pairs,
  and the I-form is not merely unused but UNAVAILABLE -- its monomials sit on
  masks of weight 3 or 4, above the distance-3 budget.
* (d) R2's scalar is the UNflipped `sum_b conj((C_j)_b)(D_i)_b`.  The flipped
  variant does not exist: its monomials sit on weight-3 masks, and in the global
  system that column is identically zero.

End to end, `sum_{a,b} (D_j)_a conj((C_j)_b) E_ab` was expanded symbolically and
verified EQUAL to `sum_c Y_{2g+c}X_{2h+1-c} + sum_c Y_{2h+c}X_{2g+1-c}` for both
anchors and all three pairs, giving `-2(X_{2g}X_{2h+1} + X_{2g+1}X_{2h})` after
`Y = -X`.  Negative controls all behave.  Scripts in `tools/verification/stepA_a.py`,
`stepA_bd.py`, `stepA_global.py`, `stepA_end2.py`.

## THE LIKELY REPAIR: anchor-free scalar relations (not yet exploited)

The pre-check turned up relations the fact list did not credit, and they look
like exactly the resource the two-anchor gap lacks.  Each weight-one mask has an
8-monomial, rank-FOUR relation space whose content is THREE pure scalar
relations plus one "difference" relation -- strictly stronger than R1's two
entries `E_00`, `E_11`, whose sum is only one of the three.  Writing
`s(b,t) := C_b^dagger D_t` and
`e(b,t) := conj((C_b)_0)(D_t)_0 - conj((C_b)_1)(D_t)_1`:

    mask 010000:  s(0,3) = s(3,0) = -s(1,2) = -s(2,1),  and
                  e(0,3) + e(1,2) + e(2,1) + e(3,0) = 0
    mask 001000:  s(0,5) = s(5,0) = -s(1,4) = -s(4,1),  plus its e-relation
    mask 000001:  s(2,5) = s(5,2) = -s(3,4) = -s(4,3),  plus its e-relation

These are per-BLOCK-PAIR inner-product identities with NO anchor in them, so they
link individual blocks ACROSS groups -- which is precisely what the per-anchor
axis argument cannot do by itself.  They do not contradict the recorded fact that
no two-term MATRIX (outer-product) relation exists: that fact is about the eight
monomials, these are about traced scalars.  Each has a two-term Walsh
certificate, e.g.

    C_0^dagger D_3 - C_3^dagger D_0 = (1/2)[e=010000, z=001000] + (1/2)[e=010000, z=000100]
    C_1^dagger D_2 + C_3^dagger D_0 = (1/2)[e=010000, z=000000] - (1/2)[e=010000, z=000100]

-- Lean-friendly.  START THE REPAIR HERE.

## One salvageable improvement over the paper

Contract the outer identity on the `b` index with `conj(C_j)` (`j` an anchor
block), then on the `a` index with `D_j`.  Writing `X_i = C_j^dagger D_i` and
`Y_i = C_i^dagger D_j`, the four terms give `Y_0 X_3 + Y_1 X_2 + Y_2 X_1 +
Y_3 X_0 = 0`, and the scalar relation `Y = -X` turns this into

    X_0 X_3 + X_1 X_2 = 0,   X_0 X_5 + X_1 X_4 = 0,   X_2 X_5 + X_3 X_4 = 0.

With `R_g := (X_{2g}, X_{2g+1})` these are exactly `R_g J R_h^T = 0` -- the
paper's J-orthogonality, but reached WITHOUT assuming `C_3` invertible and
without the inverse `M = (C_3^dagger)^{-1} D_3^T`.

MACHINE-CHECKED: all TWELVE entries of the outer identity (three group pairs
times four matrix entries) lie in the row spaces, with the `(a,a)` entries
coming from the weight-one mask and the `(a,b)` entries from its weight-two
partner:

    pair (0,1): 010000 / 110000     pair (0,2): 001000 / 101000
    pair (1,2): 000001 / 100001

The contraction itself is pure bilinearity, so the three J-orthogonality
relations are sound.  ### Closing the axis case (derived by hand, not yet machine-checked)

J-orthogonality puts the three rows on one coordinate axis, say
`X_1 = X_3 = X_5 = 0` -- one block per group.  That is not yet a contradiction,
but it closes as follows, and it needs NO inverse and no genericity:

1. `X_i = C_j^dagger D_i = 0` for `i in {1,3,5}` and BOTH anchors `j = 6,7`
   means `C_6` and `C_7` are each orthogonal to `D_1, D_3, D_5`.  Were `C_6`
   and `C_7` independent, all three `D_i` would vanish -- against
   `P_1+P_3+P_5 = 3/8`.  So `C_6 ∥ C_7`, i.e. `det A = 0`.  The mirror argument
   (using `Y_i = -X_i`, so `D_j ⊥ C_1, C_3, C_5`) gives `D_6 ∥ D_7`.
2. Hence `C_1, C_3, C_5 ∥ u`, `D_1, D_3, D_5 ∥ v`, `C_6, C_7 ⊥ v` and
   `D_6, D_7 ⊥ u`, so `A = (1/4) P_{v-perp}` and `A' = (1/4) P_{u-perp}`.
3. The anchor matrix moment identity is `A + A' = rho/2`, i.e. `rho = 2(A+A')`.
   With `kappa = |<u-hat, v-hat>|`,

       <u|rho|u> = (1-kappa^2)/2,   <u|A|u> = (1-kappa^2)/4,

   while the blocks `1,3,5` contribute exactly `3/8` to `<u|rho|u>`.  Therefore

       <u| sum_{i in {0,2,4}} C_i C_i^dagger |u>  =  (1-kappa^2)/4 - 3/8,

   which is at most `-1/8`.  But the left side is `sum |<u, C_i>|^2 >= 0`.
   Contradiction.

Note `P_0+P_2+P_4 = P_1+P_3+P_5 = 3/8` is what makes step 3 work, and it is the
same split the paper uses.

Still to do: the branches where some `R_g = 0` (rather than all three nonzero
and collinear), the mirror axis, and then the whole transcription.

## The old route (WRONG -- kept only to record what failed)

The paper argues through `rank C_3`, matrix inverses `M = (C_3^dagger)^{-1}
D_3^T`, and "choose `w` outside finitely many kernels".  None of that is needed:

1. From the matrix relation `D_i C_j^dagger + D_j C_i^dagger = 0` on a cycle
   edge, eliminating one column gives `Q_j * det[C_i, C_j] = 0` and
   `Q_i * det[C_i, C_j] = 0`.  If either probability is positive the
   determinant dies; if both vanish both vectors are zero.  So
   `det[C_i, C_j] = 0` on every cycle edge UNCONDITIONALLY.
2. Transitivity along the live path gives a common direction `u` for all
   `C_0..C_5`, and likewise `v` for `D_0..D_5`.
3. The scalar relations to the anchor give `C_6, C_7 ⊥ v` and `D_6, D_7 ⊥ u`
   (same elimination as orbit 33 step 4).
4. `rho` computed on the bottom is `(3/4) P_u + (1/4) P_{v-perp}`, on the top
   `(3/4) P_v + (1/4) P_{u-perp}`.  Equating gives `P_u = P_v`, so `u ∥ v` and
   all four anchor vectors are orthogonal to `u`.
5. The matrix moment identity at the ANCHOR group then reads
   `(1/4) P_{u-perp} + (1/4) P_{u-perp} = rho/2`, i.e.
   `(1/2) P_{u-perp} = (3/8) P_u + (1/8) P_{u-perp}`, so `P_{u-perp} = P_u`.
   With `P_u + P_{u-perp} = I` that forces `P_u = I/2`, impossible for a
   rank-one projection -- exactly the `normSq p * normSq q = 9/400` versus
   `p * star q = 0` ending of [[sslp-orbit33-block-recipe]].

The uniform identity below IS correct and checked exactly against the moment
system for every vertex of the cycle -- it is the input relations that were
wrong:

    P_{nb1(i)} + P_{nb2(i)} = P_i + 1/8.

Writing `X_i` for the anchor overlap `C_j^dagger D_i` (`j` an anchor block), the
row form of the matrix relation on a cycle edge gives BOTH

    X_i X_{i'} = 0     and     |X_i|^2 P_{i'} = |X_{i'}|^2 P_i.

Multiplying the second over the two neighbours and using the first,

    |X_i|^4 (P_{nb1} + P_{nb2}) = 0,  i.e.  |X_i|^4 (P_i + 1/8) = 0,

and `P_i >= 0` makes the factor strictly positive.  So `X_i = 0` outright -- the
whole "which blocks are dead" audit evaporates.  The `C^2`
toolkit in `SixQubit/Pair29.lean` (`perp_det`, `det_trans`, `perp_par`,
`par_of_perp`) and `SixQubit/Block33.lean` (`det_zero`, `scale`, `prop_outer`,
`ortho2`) covers every step.

## What is built

`SixQubit/Block26.lean` is installed and compiles clean (zero warnings):
`sq`, `edge_zero`, `edge_norm`, `kill`, `overlaps_vanish`, `matrix_finish`,
`anchor_det`, `anchor_det'`, `finish26` -- 524 lines, axioms
`[propext, Classical.choice, Quot.sound]`.  The algebra layer is COMPLETE: it
runs from the raw block relations all the way to `False`.

`overlaps_vanish` is the headline of the algebra layer: it takes one anchor
block, the six cycle blocks with their probabilities, the twenty-four matrix
relations on the six cycle edges, and the six scalar relations, and returns all
six overlaps `C_j^dagger D_i = 0` at once -- no case analysis.  Apply it twice,
once per anchor block.

`finish26` takes the eight block norms (with `P_i = Q_i`), `P_6 = P_7 = 1/8`,
`sum_{i<6} P_i = 3/4`, the twelve vanishing overlaps in both directions, and the
eight moment identities `L' = 2A + A'`, `L = A + 2A'`, and returns `False`.
`det A = 0` comes from `anchor_det`, which needs NO nonzero `D_i` picked: each
cycle block gives `P_i * det = 0` and the six sum to `(3/4) det = 0`.

ALL that remains for orbit 26 is the transcription: fibers (16+16), incidences
and Walsh expansions, and the moment-system derivations of `P_i = Q_i`,
`P_6 = P_7 = 1/8`, `sum_{i<6} P_i = 3/4`, the six neighbour identities, the
matrix and scalar block relations, and the grouped diagonal conditions giving
`C_g C_g^dagger + D_g D_g^dagger = rho/2`.  Same shape and size as
`SixQubit/Orbit29.lean`; `tools/orbits/o26.py` already computes the group data and
the certificate coefficients.

`matrix_finish` is the endgame in five lines of algebra: `tr A = tr B = 1/4`,
`det A = det B = 0`, `A(2A+B) = 0`, `B(A+2B) = 0` are contradictory, because
Cayley-Hamilton gives `A^2 = A/4`, hence `AB = -A/2` and `BA = -B/2`, and then
`A(BA) = A/4` while `(AB)A = -A/8`.

Generators: `tools/orbits/o26.py` builds the groups and checks the matrix moment
identity; `tools/core/blocks.py` has the general block structure (but note its
`TOP` uses SORTED top tails -- for block matching you must index the top block
by the COMPLEMENT of the bottom tail, as `o26.py` does).

See [[kl-dressings-undercount]], [[sslp-orbit33-block-recipe]],
[[sslp-orbit29-pair-coords]].
