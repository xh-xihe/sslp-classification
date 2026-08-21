---
name: sslp-nogo-mechanism-ladder
description: "The seven mechanisms that mechanize six-qubit SSLP no-gos, in increasing strength, and what the remaining seven orbits still need."
metadata: 
  node_type: memory
  type: project
  originSessionId: e2435927-3651-49b0-acfb-31f3430ee257
  modified: 2026-08-19T00:04:54.445Z
---

Certifying the 29 no-go orbits of `six_qubit_sslp_v7.tex` in Lean. Each rung has
a Python generator emitting a kernel-only Lean file; Python computes the
certificate, Lean rechecks it.

1. **k-edge Walsh.** One flip mask; one equation per admissible dressing
   (`supp(e) u supp(z)` of size <= 2). If the sign matrix forces a product to
   zero and the polytope forces both endpoint probabilities positive, done.
   `gen3`/`gen5`.
2. **Support collapse.** Nonnegativity kills the spurious incidences when the
   support is a proper subset of the fiber. `gen4` (orbit 28).
3. **Propagation.** Anchor + Walsh zero -> vanishing amplitude -> re-solve until
   the polytope goes infeasible. `gen7` (27, 35).
4. **Quadratic closure.** A one-dimensional Walsh kernel makes `|P_t|^2/v_t^2`
   constant, giving quadratic identities `q_i r_j = q_k r_l`. Modulo the linear
   moment ideal these reduce to LINEAR relations, often collapsing the polytope
   to a point with every probability an explicit positive rational. `gen8` (54).
5. **Positive row sum + shared local lemma.** No coordinate is forced positive
   but a SUM is, so some term is; the cases all discharge one reusable lemma, so
   the enumeration costs no extra code. `gen9` (32).
6. **Phase-ratio transitivity.** `rho_i = d_{i-hat}/conj(c_i)`; transitivity is
   invisible among products and needs a second union-find on the INDICES.
   Division-free via `(P_a - P_b) * P_c = 0` with `P_c` nonzero. `gen11` (58).
7. **Star hub + mirror permanent.** A single hub point `S` reciprocally paired
   with every grid point bridges the two fibers (`c_x = 0` iff `d_x-hat = 0`)
   and collapses each permanent BOTH ways: `A+C=0` and `B+D=0`. A vanishing grid
   amplitude then forces a whole row to vanish against its row sum. `gen12`
   (38) -- shorter than the paper, which case-splits on row supports and divides
   by amplitudes not yet shown nonzero.

**Done (25):** 25 27 28 30 32 34 35 37 38 39 40 53 54 55 56 57 58 59 60 61 62
63 64 65 66.

Rung 10, built for orbit 25, is the DIAGONAL Knill-Laflamme condition
`<0_L|X^e Z^z|0_L> = <1_L|X^e Z^z|1_L>` (`diagBot`/`diagTop` in `gen15.py`). It
is the only rung that looks inside a single logical state. Orbit 25 needs it
because its phase ratios are globally consistent yet all cross relations carry
sign +1, so no odd cycle exists; the diagonal condition on the coherences closes
it instead. See [[sslp-orbit25-recipe]].

**Remaining (4): 26, 29, 31, 33.** All four DO have diagonal structure, so the
new rung is available to them:
    26: masks 100000 (8/8 coherence pairs), 011000, 000110 (8/8), 010001, 001001
    29: 110000, 101000, 011000, 100100, 010100, 001100 (4/4 each), 000011 (8/8)
    31: 110000, 101000, 011000 (4/4), 000110, 000101, 000011 (8/8)
    33: 100000 (6/6), 011000, 000110, 000101, 000011 (2/2)
Orbit 33 has the SAME fiber shape as 25 (`S0[k+6] = S0[k] xor 100000`, `hat`
the reversal), but its rho splits as [0,1,2,6,7,8] plus six singletons and only
four squared-modulus consequences linearize, leaving a 3-dimensional family, so
the orbit-25 recipe does not transfer unchanged. 26 has no rho links at all;
29's top fiber is not the complement image; 31 has four disjoint rho components.

Tools worth reusing: `relations.py` (every two-term relation genuinely in a
mask's row space, links separated from cross relations), `close.py` (cross
relations rewritten among bottom amplitudes), `branchclose.py` (odd cycle plus a
tree of vanishing cases closed by LP infeasibility).

Adversarial verification before generating pays: a three-skeptic workflow on the
orbit-38 argument found a gap I had missed (the collapsed relation contains only
`u_{B_1.}` and `v_{B_2.-hat}`, so "symmetrically" for row 2 was unearned) --
fixed by the mirror permanent. Design, verify, then generate.

See [[sslp-orbit-delta-identification]] for the delta pitfall to check first.
