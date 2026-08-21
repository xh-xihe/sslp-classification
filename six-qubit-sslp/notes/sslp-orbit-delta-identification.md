---
name: sslp-orbit-delta-identification
description: SUPERSEDED - delta is q/m with additive order m; d_LP was an earlier and insufficient proxy.
metadata: 
  node_type: memory
  type: project
  originSessionId: e2435927-3651-49b0-acfb-31f3430ee257
  modified: 2026-08-18T21:00:14.764Z
---

**SUPERSEDED.** The authoritative rule is , whose additive order in  must equal ; see  and . Pinning by  (or by fiber size) is what let four modules prove a no-go for the wrong projective order.

An orbit in `six_qubit_sslp_v7.tex` is the triple `(a, q, delta)`, and `delta`
is **not** `sum(a) mod q` — orbit 28 has supports in residues 0 and 1 while
`sum(a) = 7 = 3 mod 4`, so its two supports are not complement-related at all.

Identify `delta` by matching **both** the `(|S_0|,|S_delta|)` column and the
`d_LP` column of `tab:66orbits`. Fiber sizes alone are ambiguous, and a wrong
`delta` can hand back a moment polytope that is simply *infeasible* — which
looks like a proof but certifies the wrong object. This actually happened: a
propagation run reported orbits 26, 33, 37, 58 as closed, and all four were
artifacts of a size-matched but `d_LP`-mismatched `delta`.

`d_LP` is the dimension of `{x >= 0 : Mx = b}` — the polytope **with**
nonnegativity — not the dimension of the affine solution set. Orbit 28's affine
set is 9-dimensional and its polytope is a single point. Compute it as
`|support| - rank(M restricted to the support)`, where the support is the set of
coordinates the LP does not force to zero.

See [[dyadic-lean-formalization]] for the sibling formalization.
