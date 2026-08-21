---
name: sslp-orbit33-block-recipe
description: "The certified route for six-qubit moment orbit 33 — a 2x2 block reflection on the zero-angle qubit."
metadata:
  type: project
---

Orbit 33 (`a = (0,1,1,3,3,3)`, `q = 5`, `delta = 1`, fibers 12+12) is certified in
`SixQubit/Block33.lean` + `SixQubit/Orbit33.lean`, axioms
`[propext, Classical.choice, Quot.sound]`.

The first qubit has angle zero, so both fibers are closed under flipping it and
split into six blocks of two.  With `c_i, d_i` in `C^2`:

1. The moment system alone pins every block norm to `R = (3,2,2,1,1,1)/10`.
2. The diagonal conditions for `F` on qubit one and `F Z_j` on a second give
   `C f = J C g` with `C` the 6x6 tail-sign matrix (`det C = 160`) and
   `J = diag(1,-1,...,-1)`.  Then `C^{-1} J C = 2 R 1^T - I`, which is
   equivalent to the six matrix identities
   `c_i c_i^dagger + d_i d_i^dagger = 2 R_i rho`.
3. Cross conditions make blocks 1, 2 collinear with block 0 on BOTH fibers
   (`det_zero`, then `scale`), with multipliers satisfying `mu = -star lam` and
   `lam * star lam = 3/50`.
4. Those force `c_j^dagger d_0 = 0` and `c_0^dagger d_j = 0` for `j = 3,4,5`.
5. Orthogonality in `C^2` plus the reflection identity at block 3 gives
   `rho = I/2`; the same relations give `rho = (10/3) c_0 c_0^dagger`.
6. So `c_0 c_0^dagger = (3/20) I`, whose off-diagonal entry is `0` while
   `normSq p_0 * normSq q_0 = 9/400`.  Contradiction.

Everything is division-free.  The only case analysis is `mul_eq_zero` against
explicit nonzero rationals, so no positivity reasoning leaks into the complex
part.  `Block33.lean` is bit-string-free: it takes 24 complex numbers and the
listed hypotheses and returns `False`, which made it testable on its own before
any of the transcription plumbing existed -- worth repeating for orbits 26,
which has the same zero-angle block structure with eight blocks.

Generators: `tools/generators/genblock.py` (the algebra) and
`tools/generators/gen16.py`
(the transcription, incidences, expansions, and moment derivations).

See [[kl-dressings-undercount]] for the bug that had blocked this orbit.
