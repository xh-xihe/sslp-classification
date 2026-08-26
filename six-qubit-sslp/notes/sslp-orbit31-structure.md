---
name: sslp-orbit31-structure
description: "HISTORICAL chronological work log for the now-complete orbit-31 proof."
metadata:
  type: project
---

> **HISTORICAL WORK LOG; CURRENT PROOF COMPLETE.** This file deliberately keeps
> successive progress snapshots, including obsolete “NOT started,” “still to
> write,” line-count, and “what is left” statements. They are not current status.
> The completed kernel proof is in `SixQubit/Orbit31.lean`, the table algebra in
> `SixQubit/Table31.lean`, and the code-level wrapper in
> `SixQubit/CodeOrbit31.lean`; current counts are generated in
> `results/orbit-table.tsv`.

Orbit 31 (`a = (1,1,1,2,2,2)`, `q = 4`, `delta = 1`, fibers 16+16).  NOT started.

## Structure (computed, not from the paper)

Both fibers are stabilised by the Klein four-group
`V = {000000, 000110, 000101, 000011}` -- the even-weight patterns on the last
three qubits, since `a_3 = a_4 = a_5 = 2` and `2+2 = 0 mod 4`.  So each fiber
splits into FOUR cosets of size FOUR, not the size-two blocks of orbits 26, 29
and 33.  The `C^2` toolkit therefore does NOT transfer; blocks live in `C^4`.

`S1` IS the bitwise complement of `S0`, so `relations.analyse` works here
(unlike orbit 29).

Writing a point as `(u, w)` with `u` the first three bits and `w` the last
three: membership in `S0` is `|u|` even and `|w| = -|u|/2 mod 2`.  The four
blocks have `u in {000, 011, 101, 110}`.  The paper's table is
`A_e = (000, e)` and `B_{i,e} = (u_i, e-bar)` for `e in {000,011,101,110}`,
`u_1,u_2,u_3 = 011,101,110`.

LP on the moment polytope forces NOTHING: no coordinate is pinned to zero and
none is pinned positive.  That is why the paper needs a support audit.

## Normal form -- INDEPENDENTLY VERIFIED against the moment system

Index the table by the paper's scheme: `A_e = (000, e)` and
`B_{i,e} = (u_i, e-bar)` with `e in E = {000,011,101,110}` and
`u_1,u_2,u_3 = 011,101,110`.  CAREFUL: the complement in `B_{i,e}` REVERSES the
column order relative to the naive sorted indexing.  In my sorted `S0` the map is

    A_e        -> 0, 1, 2, 3
    B_{1,e}    -> 7, 6, 5, 4
    B_{2,e}    -> 11, 10, 9, 8
    B_{3,e}    -> 15, 14, 13, 12

Get this wrong and the column relation below appears to fail -- it did for me
once.  With the right indexing all of the following reduce EXACTLY to zero:

  * `p_1(v-bar) = p_0(v)` at all sixteen positions;
  * `sum_e beta_{i,e} = 1/4` for each of the three `B` rows;
  * `alpha_e = sum_i beta_{i,e} - 1/8` for each of the four columns.

Consequences: `sum beta = 3/4`, `sum alpha = 1/4`, polytope dimension nine.

## The phase structure

Because `p_1(v-bar) = p_0(v)`, every ACTIVE position admits
`d_{v-bar} = rho_v * conj(c_v)` with `|rho_v| = 1`.  Substituting this turns
every cross-KL equation into a BILINEAR form in the bottom amplitudes with
unit-modulus coefficients.

There are exactly TWELVE two-term relations, and they are SYMMETRY conditions,
not vanishing conditions:

    star(c_x) d_{y-hat} = star(c_y) d_{x-hat}   for  (x,y) = (A_e, B_{i,e}).

Substituting the parametrisation gives `(rho_y - rho_x) star(c_x) star(c_y) = 0`,
so whenever both positions are active, `rho_x = rho_y`.  Hence

    **rho is constant along each COLUMN of the 4x4 table**,

leaving at most FOUR unknown phases `sigma_0..sigma_3` on the unit circle.

Two dead ends already ruled out by computation:

  * the LP pins NOTHING -- no coordinate forced zero, none forced positive;
  * the modulus consequences of all twelve relations are ALREADY implied by the
    moment system (zero linearize, zero survive as new quadratics), so the
    quadratic closure adds nothing;
  * on the full support there is NO forced-zero product, so a support-collapse
    branch search cannot even start.  The audit must be driven by enumerating
    polytope faces, not by forced zeros.

## The bilinear equations (computed, `tools/orbits/o31.py`)

Substituting `d_{v-bar} = rho_v conj(c_v)` and conjugating, all forty-two
cross-KL equations collapse to twenty-one distinct ones in exactly TWO families.
Write `a_e` for the amplitude at `A_e`, `b_{i,e}` at `B_{i,e}`, and
`sigma_e = conj(rho)` for the column phase.

FAMILY 1 -- one per `B` row, from the weight-one masks:

    sum_e sigma_e a_e b_{i,e} = 0,      i = 1,2,3.

FAMILY 2 -- from the weight-two masks, after taking the sum and difference of
the two dressings.  For every column pair `{e,f}` and every row pair `{i,j}`:

    (sigma_e + sigma_f) * (b_{i,e} b_{j,f} + b_{i,f} b_{j,e}) = 0.

The second factor is a 2x2 PERMANENT, not a determinant -- the "mirror
permanent" rung of [[sslp-nogo-mechanism-ladder]].  Since every `|sigma_e| = 1`,
`sigma_e + sigma_f = 0` iff `sigma_f = -sigma_e`; otherwise that column pair
imposes the permanent condition on ALL THREE row pairs.

Counting: the minimum number of column pairs that must impose permanents is TWO
(a perfect matching), attained by `sigma = (s, s, -s, -s)` up to relabelling.
Values `s,s,s,-s` give three; all equal gives all six.

## The all-equal branch is CLOSED (complete argument, derived by hand)

Suppose all four `sigma_e` agree, so all six column pairs impose permanents.
Fix a column pair `{e,f}` and set `v_i = (b_{i,e}, b_{i,f}) in C^2`.  The
permanent condition is `v_i J v_j^T = 0` with `J` antidiagonal -- the SAME
symmetric bilinear form as in [[sslp-orbit26-hexagon]].  Three nonzero pairwise
J-orthogonal vectors in `C^2` lie on one coordinate axis, which would make a
whole COLUMN of `B` vanish.  But `alpha_e = sum_i beta_{i,e} - 1/8 >= 0` forces
every column total to be at least `1/8`, so no column vanishes.  Hence for each
of the six column pairs some row has BOTH entries zero.

A row cannot be entirely zero (`sum_e beta_{i,e} = 1/4`), so each row's zero set
has size at most three and covers at most `C(3,2) = 3` pairs.  Covering all six
pairs with three rows therefore forces every row to have zero set of size
exactly three -- one nonzero entry per row, carrying the whole `1/4` -- and the
three nonzero columns must be distinct (otherwise the pair containing them all
is uncovered).  Then the fourth column has total zero and
`alpha = 0 - 1/8 = -1/8 < 0`.  Contradiction.

## FAMILY 3 -- the diagonal conditions (I nearly missed these)

The Klein group `V = {000110, 000101, 000011}` preserves BOTH fibers, so those
weight-two masks carry FULL diagonal incidence.  The same-column masks
(`110000`, `101000`, `011000`) also have diagonal incidence but their conditions
are VACUOUS, because every term carries the factor `1 - rho_e conj(rho_e) = 0`.

CORRECTED FORM (an earlier version of this note had it too strong -- see the
warning below).  The bottom sign is `(-1)^{z.x}`, and row `A` sits at last-three-bits
`e` while the `B` rows sit at `e-bar`.  So for an ODD-weight dressing the `A` row
enters with the OPPOSITE sign from the three `B` rows.  Two column overlaps are
therefore needed:

    G_{ef} = sum over ALL FOUR rows of c_{r,e} conj(c_{r,f})
    H_{ef} = (sum over the three B rows) - (the A term)

Each Klein mask gives four conditions: the two EVEN-weight dressings are `G`
conditions, the two ODD-weight ones are `H` conditions.  Taking sums and
differences, each unordered column pair `{e,f}` yields exactly

    G_{ef} t_{ef} + G_{fe} t_{fe} = 0,     H_{ef} t_{ef} - H_{fe} t_{fe} = 0,
    where t_{ef} = rho_f conj(rho_e) - 1.

Since `G_{fe} = conj(G_{ef})`, `H_{fe} = conj(H_{ef})` and `t_{fe} = conj(t_{ef})`,
these are

    **Re( G_{ef} t_{ef} ) = 0     and     Im( H_{ef} t_{ef} ) = 0.**

WARNING -- what I got wrong: I first claimed each of the four terms vanishes
separately, giving `G_{ef} t_{ef} = 0` (columns orthogonal unless phases agree).
That is STRICTLY STRONGER than the truth and it is false.  The error was
collapsing all four rows into one `G` while the `A` row carries the opposite sign
for odd dressings.  It was caught by taking a solution of the reduced system and
replaying it against the RAW Knill-Laflamme conditions: exactly two failed,
`[000110|000010]` and `[000101|000001]` -- both weight-one dressings.  ALWAYS run
that replay before trusting a reduced system.

Column norms: `||col_e||^2 = alpha_e + sum_i beta_{i,e} = 2 alpha_e + 1/8 >= 1/8`,
so no column is the zero vector.  (The same bound is what kills the all-equal
branch above.)

Combining with FAMILY 2 for a pair `{e,f}`:

  * `rho_e = rho_f`   -> `t_{ef} = 0`, so FAMILY 3 is vacuous, but the
    permanents vanish;
  * `rho_f = -rho_e`  -> FAMILY 2 is vacuous, but `t_{ef} = -2` so
    `Re(G_{ef}) = 0` and `Im(H_{ef}) = 0`;
  * neither           -> both act.

Consequence: if NO pair has `rho_f = -rho_e`, ALL SIX pairs impose permanents and
the all-equal argument closes it.  So only branches with a nonempty "cancel
graph" survive; the cancel graph is a disjoint union of complete bipartite graphs
between opposite-phase classes -- at most `K_{2,2}`, four edges.

## THE COLUMN RELATION (STRONGEST FORM -- start here)

Family one literally says the four bottom columns `X_e in C^3` (the `B` rows)
are linearly dependent:

    sum_e v_e X_e = 0,      v_e := conj(rho_e) a_e.

Pairing against each `X_f` gives FOUR scalar equations, not just the one
weighted sum used further below:

    **sum_e v_e M_{ef} = 0,   f = 0,1,2,3.**

Substituting FAMILY 3 (`M_{ef} = conj(v_e) v_f` whenever the phases differ) and
writing `s_c` for the total `alpha` of `f`'s phase class, equation `f` becomes

    v_f ( alpha_f + 1/8 + 1/4 - s_{c(f)} ) + sum_{e in c(f), e != f} v_e M_{ef} = 0.

CONSEQUENCE: any column ALONE in its phase class has `s_c = alpha_f`, so the
bracket is `3/8` and `v_f = 0` outright.  That collapses the branch analysis:

  (1,1,1,1)  every `v_f = 0`, so `sum alpha = 0` against `1/4`.
  (2,1,1)    `v_2 = v_3 = 0`, hence `s_1 = 1/4`; the surviving `2 x 2` system is
             singular, so `(alpha_0+1/8)(alpha_1+1/8) = |M_{01}|^2` -- Cauchy-
             Schwarz TIGHT -- so `X_0 ∥ X_1`, the permanent forces a single
             nonzero row, and that row must carry `alpha_0+1/8` plus
             `alpha_1+1/8 >= 1/4`, its whole budget.  So `alpha_0 = alpha_1 = 0`
             and `s_1 = 0`, not `1/4`.
  (2,2)      the same `2 x 2` determinant, and
             `(3/8-alpha_0)(3/8-alpha_1) - (alpha_0+1/8)(alpha_1+1/8) = 1/8 - s_1/2 >= 0`.
             Strict inequality contradicts singularity; equality forces
             `s_1 = 1/4`, which is the tight case just killed.
  (3,1)      `v_3 = 0` so `alpha_3 = 0`.  Covering B puts two rows entirely in
             column 3, whose total then exceeds `alpha_3 + 1/8 = 1/8`.  Covering
             A makes columns `0,1,2` disjointly supported, so every `M_{ef} = 0`
             and each equation reads `v_f(alpha_f + 1/8) = 0`, giving
             `v_f = 0` and `sum alpha = 0`.
  (4)        no FAMILY 3 constraint at all; use the full permanent condition
             (see the repaired argument below -- the covering count I first
             used is NOT valid).

This supersedes the single-identity treatment below, which is the `f`-weighted
sum of these four and therefore weaker.

## THE GRAM PICTURE (equivalent, weaker frame)

Let `v_e := conj(rho_e) a_e`, so FAMILY 1 says `v` is in the kernel of the `3 x 4`
bottom matrix `B`.  Let `M_{ef} := sum_i b_{i,e} conj(b_{i,f})` be the Gram matrix
of the four `B`-columns, which are vectors in `C^3`.

FAMILY 3 for a pair with `rho_e != rho_f` is `M t = -conj(N t)` with
`N_{ef} = a_e conj(a_f)`, `t = rho_f conj(rho_e) - 1`.  Being LINEAR in `M_{ef}`
this determines it uniquely, and (verified symbolically) the solution is

    **M_{ef} = conj(v_e) v_f.**

Also `M_{ee} = sum_i beta_{i,e} = alpha_e + 1/8 = |v_e|^2 + 1/8`.  Hence

    **M = v-bar v^T + (1/8) I + E**,

where `E` is supported ONLY on the off-diagonal entries of SAME-phase pairs
(there FAMILY 3 is vacuous because `t = 0`, and FAMILY 2 acts instead).

Now `M` is the Gram matrix of FOUR vectors in `C^3`, so `rank M <= 3` and

    **det M = 0.**

All four phases DISTINCT: `E = 0`, and the matrix determinant lemma gives
`det M = (1/8)^3 (1/8 + ||v||^2) > 0`.  Contradiction -- this supersedes the
`3/32` computation below, which is the same fact in coordinates.

For the other partitions, write `D = (1/8) I + E` and use
`det M = det(D) (1 + v^T D^{-1} v-bar) = 0`.  With one same-phase pair `{0,1}`
and `E_{01} = eps`:

    det D = (1/64 - |eps|^2)(1/8)^2,
    1 + 8(alpha_2 + alpha_3)
      + [ (1/8)(alpha_0+alpha_1) - 2 Re(eps v_0 conj(v_1)) ] / (1/64 - |eps|^2) = 0.

### The (2,1,1) partition is CLOSED

Same-phase pair `{0,1}`, so `E_{01} = eps` is the only off-diagonal correction.
Put `delta = 1/64 - |eps|^2`, `K = (1/8)(alpha_0+alpha_1) - 2 Re(eps v_0 conj(v_1))`.

CASE `|eps| < 1/8`.  Then `delta > 0` and
`K >= (alpha_0+alpha_1)(1/8 - |eps|) >= 0`, so `K/delta >= 0`; but the
determinant condition needs `K/delta = -(1 + 8(alpha_2+alpha_3)) <= -1`.  Dead.

CASE `|eps| > 1/8`.  The same inequality forces Cauchy-Schwarz to be TIGHT,
i.e. `B`-columns `0` and `1` proportional.  The permanent condition then reads
`2 lambda b_{i,0} b_{j,0} = 0`, so at most one row has `b_{i,0} != 0` (else
`lambda = 0` and column 1 vanishes).  That row must carry `alpha_0 + 1/8` AND
`alpha_1 + 1/8`, whose sum already exhausts its total `1/4`, forcing
`alpha_0 = alpha_1 = 0` and hence `|eps| <= 1/8`.  Dead.

CASE `|eps| = 1/8`.  Now `D` is singular with kernel `k = (-8 eps, 1, 0, 0)`,
its nonzero eigenvalues are `1/4, 1/8, 1/8`, and `||k||^2 = 2`, so
`adj(D) = k k^dagger / 512` and

    det M = v^T adj(D) v-bar = |v^T k|^2 / 512.

Hence `det M = 0` forces `v_1 = 8 eps v_0`, so `alpha_0 = alpha_1` and
`|M_{01}| = alpha_0 + 1/8` -- tight again, so by the previous paragraph
`alpha_0 = alpha_1 = 0` and the `B`-columns `0,1` live only on one row (say row
2), which therefore has `beta_{2,2} = beta_{2,3} = 0`.  Rows 1 and 3 then live in
columns 2,3, and FAMILY 1 says `(b_{i,2}, b_{i,3})` is annihilated by the linear
form `(v_2, v_3)`, hence proportional to `(v_3, -v_2)`:

    (b_{1,2}, b_{1,3}) = lambda_1 (v_3, -v_2),   (b_{3,2}, b_{3,3}) = lambda_3 (v_3, -v_2).

Then `M_{23} = -(|lambda_1|^2 + |lambda_3|^2) v_3 conj(v_2)`, while FAMILY 3
demands `M_{23} = conj(v_2) v_3`.  Comparing gives
`|lambda_1|^2 + |lambda_3|^2 = -1`.  Dead.  (Degenerate sub-case `alpha_2 = 0`:
FAMILY 1 then kills column 3 entirely, against its total `alpha_3 + 1/8 = 3/8`.)

### The (3,1) partition is CLOSED

Classes `{0,1,2}` (one phase) and `{3}`.  FAMILY 2 acts on the three pairs inside
`{0,1,2}`; each needs a row vanishing on both columns.  Two coverings:

COVERING A -- three different rows, `Z_1 ⊇ {0,1}`, `Z_2 ⊇ {0,2}`, `Z_3 ⊇ {1,2}`.
Then `B`-columns `0,1,2` have DISJOINT supports, so `M_{ef} = 0` for
`e,f in {0,1,2}` and `M` is an ARROWHEAD matrix.  With `d_e = alpha_e + 1/8`,

    det M = (prod_{e<3} d_e) * [ alpha_3 + 1/8 - alpha_3 * sum_{e<3} alpha_e/d_e ].

Setting it to zero and using `alpha_e/d_e <= 8 alpha_e` with
`sum_{e<3} alpha_e = 1/4 - alpha_3` gives
`alpha_3 + 1/8 <= alpha_3 (2 - 8 alpha_3)`, i.e. `8 alpha_3^2 - alpha_3 + 1/8 <= 0`.
Its discriminant is `1 - 4 = -3 < 0`, so the quadratic is strictly positive.  Dead.

COVERING B -- one row (say row 1) vanishes on all of `0,1,2`, hence carries its
whole `1/4` in column 3.  FAMILY 2 still applies to the row pair `(2,3)`, so the
three vectors `u_e = (b_{2,e}, b_{3,e})`, `e = 0,1,2`, are pairwise
J-orthogonal.  Some `u_e = 0` would empty a `B`-column, so all three lie on one
coordinate axis, i.e. row 2 OR row 3 also vanishes on `0,1,2` and concentrates in
column 3.  Two rows then put `1/4` each into column 3, forcing
`alpha_3 >= 3/8` against `sum alpha = 1/4`.  Dead.

## CORRECTION: the (4) branch covering count is WRONG

I claimed: each column pair needs a row vanishing on both, a row's zero set has
size at most three so covers at most three pairs, hence covering all six forces
every row to have exactly one nonzero entry with the three nonzero columns
distinct, leaving a column of total zero.

COUNTEREXAMPLE to the combinatorial step: `Z_1 = {0,1,2}`, `Z_2 = {0,1,3}`,
`Z_3 = {2,3}` have sizes `3,3,2` and cover all six pairs, yet their intersection
is empty.  So no column is forced to vanish.  Concretely this gives
`beta_{1,3} = beta_{2,2} = 1/4`, `beta_{3,0} = beta_{3,1} = 1/8`,
`alpha = (0,0,1/8,1/8)`, all probabilities consistent.

That configuration IS still excluded, but by the PERMANENT itself, not by
counting: for the column pair `{0,2}` the rows `2,3` must be J-orthogonal, giving
`b_{2,2} b_{3,0} = 0` while both factors are nonzero.

### The repaired (4) argument

Use the FULL condition `b_{i,e} b_{j,f} + b_{i,f} b_{j,e} = 0` for all `e != f`
and all `i != j`.  Its key consequence, division-free, for one row pair and three
distinct columns:

    be * p_{fg} - bf * p_{eg} - bg * p_{ef} = -2 * bf * bg * se,
    so   **b_{i,f} b_{i,g} b_{j,e} = 0.**

Two branches:

  * some row `i` has THREE or more nonzero entries.  Then for each `e` in its
    support pick `f, g` also in it; `b_{i,f} b_{i,g} != 0` forces `b_{j,e} = 0`
    for every other row, so those columns are carried by row `i` alone.  The
    other two rows then live on the at most one remaining column.  Column sums
    give `sum_{e in supp} alpha_e + 3/8 = 1/4`, i.e. `sum alpha_e = -1/8 < 0`.
  * every row has at most two nonzero entries.  For a row pair both nonzero,
    if `b_{i,e} != 0` while `b_{j,e} = 0` then `p_{ef}` forces `b_{j,f} = 0` for
    every `f`, so row `j` vanishes -- impossible since its total is `1/4`.  Hence
    all three rows share ONE support `T` with `|T| <= 2`, and any column outside
    `T` is empty, against `sum_i beta_{i,e} = alpha_e + 1/8 >= 1/8`.

Both branches close, so `(4)` is sound again.  The counterexample above has
supports `{3}`, `{2}`, `{0,1}` -- not equal -- consistent with this.

The error: I used only the weak consequence "some row vanishes on both columns"
and dropped the rest of the three-vector J-orthogonality, namely that the OTHER
TWO rows must still be J-orthogonal to each other.  The full condition for the
`(4)` branch is

    b_{i,e} b_{j,f} + b_{i,f} b_{j,e} = 0   for ALL e != f and ALL i != j,

which for a fixed row pair `(i,j)` and three distinct columns forces
`b_{i,f} b_{i,g} b_{j,e} = 0`.  Re-derive the branch from that.  Everything else
in this note stands; the `(4)` branch is the only one whose certificate is not
yet sound, and it is still numerically EXCLUDED.

## Independent end-to-end check

`tools/verification/close31.py` drops the reduced system entirely: it takes the sixteen
bottom amplitudes AND the four column phases as free unknowns (with `|rho|^2 = 1`
as explicit residuals) and hits the RAW Knill-Laflamme conditions directly.  Over
sixty random starts the best residual is `2.93e-01` -- EXCLUDED.  So the phase
parametrisation is sound and the system genuinely has no solution; nothing below
rests on a reduction that was never checked against the originals.

The optimiser's best attempt lands on phases `(s, -s, -s, s)`, the `K_{2,2}`
pattern -- consistent with that being the branch that survives longest.

## ALL FIVE PARTITIONS ARE CLOSED -- the orbit 31 argument is COMPLETE

  (4)        permanents + covering count -> a column total of 0, so alpha = -1/8
  (3,1)      arrowhead determinant, or two rows trapped in column 3
  (2,2)      b_{3,e} = eps e^{i phi} conj(a_e) -> sum alpha = 0
  (2,1,1)    the three eps cases above
  (1,1,1,1)  det M = (1/8)^3 (1/8 + ||v||^2) > 0

### Expressing the branches in RAW amplitudes (the assembly design)

Two facts remove every phase variable from the Lean side:

  * `v_e = conj(d_{A-hat_e})` -- the kernel vector is literally the conjugate of
    the TOP amplitude at the complement of `A_e`.  No division, no `rho`.
    (Because `d_{v-bar} = rho_v conj(c_v)`, so `d_{A-hat_e} = rho_e conj(a_e)`
    and `conj` of that is `conj(rho_e) a_e = v_e`.)
  * Two columns share a phase iff

        **v_e a_f = v_f a_e**,

    equivalently `conj(v_f) v_e = conj(a_f) a_e` -- which is exactly the factor
    `t_{ef} = 0` appearing in family three, so the second form needs no
    conversion at assembly time.

So the five-branch case split is `by_cases` on six division-free complex
equations, and every branch conclusion (`v_f = 0`, the `2 x 2` singularity, the
permanent structure) is already stated in these terms by the lemmas in
`SixQubit/Table31.lean`.

### Lean progress

`SixQubit/Table31.lean` is installed, compiles clean, axioms
`[propext, Classical.choice, Quot.sound]`:

  kernel_identity  the weighted Gram identity (the weaker frame)
  all_distinct     the `(1,1,1,1)` branch via that identity
  partition31      the `(3,1)` covering-A branch as a nonnegative sum
  gram_eq          THE COLUMN RELATION -- one equation per column
  lone_column      a column alone in its class has `v_f = 0`
  pair_class       a two-column class forces its `2 x 2` system singular
  pair_gap         `(3/8-a0)(3/8-a1) - (a0+1/8)(a1+1/8) = 1/8 - s/2`

Also installed: `tight_pair` and `det_perm_zero` (the step shared by `(2,1,1)`
and `(2,2)`), plus `perm_triple` and `perm_support` (the repaired `(4)` branch).
Twelve lemmas, 260 lines, zero warnings.

`SixQubit/Orbit31.lean` (1777 lines, 896 theorems, zero warnings, kernel-checked)
holds the COMPLETE transcription: fibers `16+16` with `decide`, the sixteen
complement pairings, the full moment normal form (23 facts), and all three
families -- family one from the weight-one masks (two dressings each), the
eighteen family-two column-pair sums from the nine weight-two masks (all
verified to lie in the row spaces), and the family-three `diagBot`/`diagTop`
expansions on the three Klein masks.

Still to write: ONLY the branch assembly, wiring `Table31`'s twelve lemmas to
those 896 transcription theorems using the raw-amplitude phase test above.

## THE UNIFORM IDENTITY (equivalent, in coordinates)

FAMILY 1 says exactly that `v := (conj(rho_e) a_e)_e` lies in the KERNEL of the
`3 x 4` bottom matrix `B` (entries `b_{i,e}`), because `sum_e v_e b_{i,e} = 0`
for each row `i`.  Therefore

    0 = sum_i |(B v)_i|^2 = sum_{e,f} v_e conj(v_f) M_{ef},
    M_{ef} := sum_i b_{i,e} conj(b_{i,f}).

FAMILY 3, for ANY pair with `rho_e != rho_f`, is equivalent to

    M_{ef} = - conj(N_{ef}) * conj(t_{ef}) / t_{ef},    N_{ef} = a_e conj(a_f),
    t_{ef} = rho_f conj(rho_e) - 1.

(Both `Re(G t) = 0` and `Im(H t) = 0` are needed; with `G = N + M`, `H = M - N`
they say `M t = - conj(N t)`.)  Writing `u = rho_f conj(rho_e)` one gets
`conj(t)/t = -1/u`, and the ordered term collapses to

    v_e conj(v_f) M_{ef} = + alpha_e alpha_f,

INDEPENDENT of the phases.  So

    0 = sum_e alpha_e (alpha_e + 1/8)
      + sum over DIFFERENT-phase pairs of 2 alpha_e alpha_f
      + sum over SAME-phase pairs of 2 Re( a_e conj(a_f) M_{ef} ).

If all four phases are DISTINCT the last sum is empty and, using
`sum alpha = 1/4`,

    0 = sum alpha_e^2 + (1/8)(1/4) + [ (1/4)^2 - sum alpha_e^2 ] = 1/32 + 1/16 = 3/32,

a contradiction.  Note `M_{ee} = sum_i beta_{i,e} = alpha_e + 1/8` and
`|v_e|^2 = alpha_e`.

## The K_{2,2} branch is CLOSED (by hand)

Phases `(s,s,-s,-s)`, classes `{0,1}` and `{2,3}`.  FAMILY 2 acts only within
classes and forces (no `B`-column being zero) some row with `b_{i,0}=b_{i,1}=0`
and another with `b_{j,2}=b_{j,3}=0`; they must differ, so say rows 1 and 2.
The four cross pairs then give `M_{ef} = -conj(a_e) a_f`, whose modulus forces
`beta_{3,e} = alpha_e` and whose phase forces

    b_{3,e} = eps * e^{i phi} * conj(a_e),   eps = +1 on columns 0,1 and -1 on 2,3.

Substituting into FAMILY 1 for row 3 (`a_0b_{3,0}+a_1b_{3,1} = a_2b_{3,2}+a_3b_{3,3}`)
gives `alpha_0+alpha_1 = -(alpha_2+alpha_3)`, i.e. `sum alpha = 0`, against `1/4`.

## Numerical status of the branches

With the CORRECTED families 1, 2, 3 plus the moment normal form, EVERY phase
configuration tested comes out EXCLUDED, best residual `1.5e-2` or worse over
120 random starts each.  Eleven configurations covering all five partitions of
the four columns by phase:

    (4)        (s,s,s,s)
    (3,1)      (s,s,s,-s)   (s,s,s,e^{2.4i})
    (2,2)      (s,s,-s,-s)  (s,s,i,i)
    (2,1,1)    (s,s,i,e^{2.1i})  (s,s,-s,e^{1.3i})  (s,s,i,-i)
    (1,1,1,1)  (s,-s,t,-t)  (s,-s,t,u)  generic

So the REDUCED SYSTEM IS SUFFICIENT.  What remains is turning each partition into
a displayed certificate and then the Lean build -- no further search needed.

## What is left

By hand: the phase partitions `(4)` [all-equal], `(2,2)` [K_{2,2}] and
`(1,1,1,1)` [all distinct] are CLOSED.  Still to write out: `(3,1)` and
`(2,1,1)`, both numerically excluded.  For `(3,1)` the three same-phase columns
give three permanent pairs, which the covering count of the all-equal branch
should handle; for `(2,1,1)` one same-phase pair survives in the uniform
identity, so bound its `2 Re(a_e conj(a_f) M_{ef})` term using the permanent
condition on that pair.

Superseded notes below (kept for the record).  Hardest was `K_{2,2}`,
`rho = (s,s,-s,-s)`: only `{0,1}` and `{2,3}` impose permanents, so no column
being zero forces some row `i` with `b_{i,0}=b_{i,1}=0` and some row `j != i`
with `b_{j,2}=b_{j,3}=0`.  Take `i=1`, `j=2`.  Then column `0` is
`(a_0, 0, b_{2,0}, b_{3,0})` and column `2` is `(a_2, b_{1,2}, 0, b_{3,2})`, and
the four cross-class orthogonalities read

    a_0 conj(a_2) + b_{3,0} conj(b_{3,2}) = 0,   a_0 conj(a_3) + b_{3,0} conj(b_{3,3}) = 0,
    a_1 conj(a_2) + b_{3,1} conj(b_{3,2}) = 0,   a_1 conj(a_3) + b_{3,1} conj(b_{3,3}) = 0.

Together with FAMILY 1 (`a_2b_{1,2}+a_3b_{1,3} = 0`, `a_0b_{2,0}+a_1b_{2,1} = 0`,
`a_0b_{3,0}+a_1b_{3,1} = a_2b_{3,2}+a_3b_{3,3}`) and the two surviving
permanents, this is a concrete finite system -- solve it next.  The smaller
cancel graphs (one, two or three edges) leave three to five pairs imposing
permanents and should fall to the same covering count as the all-equal branch.

## Why it is the heaviest

The paper's own words: "a complete exact audit of all support faces ... The
finite classification is computer-assisted, using only rational arithmetic and
symbolic row reduction; every one of the sixteen final support types is then
excluded by a displayed analytic certificate."  So it is a sixteen-case
classification, each case with its own certificate -- structurally unlike the
other twenty-eight, which each have a single uniform mechanism.

Expect this to be the largest single formalisation of the set.  Before starting,
recompute the sixteen support types independently rather than transcribing the
paper's table, and check each certificate against the moment system the way
`cert.reduce_mod_linear` does elsewhere.

See [[sslp-nogo-mechanism-ladder]], [[kl-dressings-undercount]].
