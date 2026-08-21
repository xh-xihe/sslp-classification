---
name: sslp-orbit-delta-identification
description: SUPERSEDED - delta is q/m with additive order m; d_LP was an earlier and insufficient proxy.
metadata: 
  node_type: memory
  type: project
  originSessionId: e2435927-3651-49b0-acfb-31f3430ee257
  modified: 2026-08-18T21:00:14.764Z
---

# Historical note: identifying the second residue fiber

**SUPERSEDED.** The authoritative rule is `delta = q/m`, and the additive
order of `delta` in `Z_q` must be exactly the projective order `m`. The checked
orbit data live in `tools/manifest.json`; `tools/verification/gate.py` compares
the Lean modules with that data. Neither fiber cardinality nor `d_LP` defines
`delta`.

The earlier workflow searched residues having the expected fiber size and then
accepted the first easy certificate. Equal fiber sizes do not imply equal
residues or equivalent orbit representatives. That mistake caused orbits 30,
53, 55 and 65 to be certified at residues of additive order two instead of at
their required orders 4, 6, 6 and 8. Their corrected fibers are disjoint from
the old fibers, so the repairs are new proofs of the intended objects, not
relabelings.

`delta` is also not `sum(a) mod q`. For example, orbit 28 uses residues 0 and 1,
whereas `sum(a) = 7 = 3 mod 4`; its two supports are not complement-related.

`d_LP` remains useful only as a diagnostic cross-check. It is the dimension of
the feasible polytope `{x >= 0 : Mx = b}`, not the dimension of the unrestricted
affine solution set. Orbit 28 illustrates the distinction: its affine solution
set is 9-dimensional while its feasible polytope is a single point. It may be
computed as `|support| - rank(M restricted to the support)`, where the support is
the set of coordinates not forced to zero by the LP.

The sibling dyadic formalization is outside this repository, at
`../A_dyadic_ladder/` in the present workspace layout.
