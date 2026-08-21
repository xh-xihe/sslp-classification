---
name: sslp-orbit29-pair-coords
description: "The certified route for six-qubit moment orbit 29 — pair coordinates in C^2, a K_4 of orthogonalities, and a two-branch endgame."
metadata:
  type: project
---

Orbit 29 (`a = (1,1,1,1,2,2)`, `q = 4`, `delta = 1`, fibers 16+16) has fibers that
are NOT complementary (`sum a = 8 = 0 mod 4`), so `relations.analyse` returns
`None`; use `scratchpad/relgen.py` instead.

Both fibers are closed under `X_5 X_6` (mask `000011`), splitting each into eight
pairs.  Every two-term relation found has the uncrossed form

    star(c_{2m}) d_{2n} + star(c_{2m+1}) d_{2n+1} = 0,

so its modulus consequence is `q_{2m} r_{2n} = q_{2m+1} r_{2n+1}`.

Change coordinates to `P_m = q_{2m}+q_{2m+1}`, `D_m = q_{2m}-q_{2m+1}` and
likewise `Q_n, E_n` on top.  Two things happen:

1. The modulus consequence loses its quadratic part exactly:
   `P_m E_n + D_m Q_n = 0`.  Bilinear, and linear in `(D,E)` for fixed `(P,Q)`.
2. The moment system DECOUPLES.  The sums `P, Q` depend only on three
   parameters (the paper's 3-simplex); the differences `D, E` only on the other
   six.  In particular `P_0 = 0` and `P_7 = 1/4` outright.

`P_0 = 0` plus nonnegativity forces the parameter `tau5 = 0`, hence
`D_0 = D_7 = 0` and `E_0 = E_1 = E_2 = E_4 = 0` -- from the moment system and
positivity ALONE, with no quadratic input.  That already pins the pair
`(111100, 111111)` (the paper's `B_0`) to `1/8, 1/8`.

The 16 edges hit only `m = 0..6` and `n = 3,5,6,7`.  Wherever `P_m != 0` the
edges give `D_m = kappa P_m` and `E_n = -kappa Q_n` for one common `kappa` --
this is the paper's "all active pair ratios fixed by one common unit phase".
Substituting the moment-system relations (e.g. `D_1 = D_6 - E_6 - E_7`) forces
`P_1 = P_6 + Q_6 + Q_7`, i.e. `tau3 + tau4 = 1/4`.  So `kappa != 0` only on
special faces -- which is precisely why the paper audits all fifteen faces of
the simplex.  Numerically, 400/400 sampled solutions have `D = E = 0`.

## The geometry and the endgame

Read each pair as a vector in `C^2`: `C_m = (c_{2m}, c_{2m+1})`,
`D_n = (d_{2n}, d_{2n+1})`.  Then the two-term relation IS `C_m^dagger D_n = 0`.
After the collapse (bottom pair 0 dead) twelve edges survive, joining bottom
pairs `1..6` to top pairs `3,5,6,7`, and they realise **exactly the six edges of
`K_4`** on the top vertex set: `C_1 ⊥ D_{3,5}`, `C_2 ⊥ D_{3,6}`,
`C_3 ⊥ D_{3,7}`, `C_4 ⊥ D_{5,6}`, `C_5 ⊥ D_{5,7}`, `C_6 ⊥ D_{6,7}`.
So in `C^2`: a nonzero `C_m` makes its two `D`s parallel, a nonzero `D_n` makes
its three `C`s parallel -- this is the paper's "one common unit phase", and it
is the same `det_zero` / `prop_outer` / `ortho2` toolkit as
[[sslp-orbit33-block-recipe]].

The endgame needs no phase variable at all.  For each top pair
`n in {3,5,6,7}` there are two masks (uncrossed / crossed) with two dressings
each; taking sums and differences kills the ratios and leaves four clean
four-term equations.  For `n = 3` (masks `100001`, `100010`):

    P1: cb8 d0 + cb10 d2 + cb12 d4 + cb15 d7 = 0
    P2: cb9 d1 + cb11 d3 + cb13 d5 + cb14 d6 = 0
    P3: cb9 d0 + cb11 d2 + cb13 d4 + cb15 d6 = 0
    P4: cb8 d1 + cb10 d3 + cb12 d5 + cb14 d7 = 0

The three other bottom pairs in each family are precisely the `K_4` edges NOT
containing that top vertex.  Writing `C_m = alpha_m u` and `D_n = xi v`, the
four collapse to `xi (ubar_0 v_0 - ubar_1 v_1) = 0`; with `u ⊥ v` that is
`2 xi ubar_0 v_0 = 0`.  If it forces `xi = 0` for all four `n`, then
`Q_3+Q_5+Q_6+Q_7 = 0`, against the moment value `3/4`.  The escape
`ubar_0 v_0 = ubar_1 v_1 = 0` is the axis-aligned case `kappa = +-1`, which
needs `tau3 + tau4 = 1/4`, i.e. `P_6 = 0` -- a face where `C_6` dies and the
propagation must be rerun.  That is what the paper's fifteen-face table is
doing, and it is the only part not yet reduced to a single uniform argument.

## CERTIFIED

`SixQubit/Pair29.lean` (algebra) + `SixQubit/Orbit29.lean` (transcription),
axioms `[propext, Classical.choice, Quot.sound]`.

Two facts made it much shorter than the paper's fifteen-face audit:

* the uniform identity `P_{edge{n,n'}} = Q_n + Q_{n'} - 1/4`, which collapses the
  face table into `par_edge` (one hop);
* never picking a nonzero bottom pair.  Instead DEFINE the common bottom
  direction as `u := (-star v_1, star v_0)` from the anchor `v`.  It is
  automatically nonzero, automatically orthogonal to `v`, and `u ⊥ D_n` is
  literally `det[D_n, v] = 0`.  Only two case splits survive: which top pair
  anchors (`Q_3 = 0` or not) and whether `v_1 = 0`.

The support collapse turned out to be unnecessary: the eight endgame masks never
touch bottom pair 0, so the certificate needs only the moment system, the twelve
orthogonalities, and the sixteen Walsh combinations.

The final chain, all verified on paper and reduced to those lemmas:

1. `sum Q_n = 3/4` with each `Q_n <= 1/4`, so at most ONE top pair is empty.
2. `par_edge` six times -> all four top pairs pairwise parallel; pick a nonzero
   one as `v`.
3. every bottom pair is orthogonal to `v` (`perp_par` through an endpoint with
   `Q_n > 0`; every edge has one since at most one `Q_n` vanishes).
4. `par_of_perp` -> all bottom pairs pairwise parallel; pick a nonzero one as
   `u` (exists since `sum P_m = 3/4`).
5. `endgame` at each top pair -> `star(u_0) S_n = 0` and `star(u_1) T_n = 0`.
6. `u != 0`, so either all `S_n = 0` or all `T_n = 0`, UNIFORMLY.  Hence
   `sum E_n = -+3/4`, against the moment identity `sum E_n = 0`.

Useful sub-facts, all checked exactly against the moment system: `q0 + q1 = 0`
(then positivity kills both), `q14 + q15 = 1/4`, `q14 - q15 = (q0-q1)/3`,
`sum_n Q_n = 3/4`, `sum_n E_n = 0`, and the uniform
`P_{edge{n,n'}} = Q_n + Q_{n'} - 1/4`.

What remains is the transcription: fibers (16+16), incidences and Walsh
expansions for the twelve masks (`100000 010000 001000 000100` for the edges,
`100001 100010 010001 010010 001001 001010 000101 000110` for the endgame),
the `MomentSystem` derivations, and the assembly.  The endgame equations are
sums/differences of pairs of Walsh rows -- see the P1..P4 display above.

The remaining Lean engineering is the "pick a nonzero one" case splits in steps
2-4; the mathematics is done.

Not yet certified.  See [[kl-dressings-undercount]] and
[[sslp-orbit33-block-recipe]].
