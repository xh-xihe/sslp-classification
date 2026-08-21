---
name: sslp-51-orbits-complete
description: All 51 no-go moment orbits of six_qubit_sslp.tex are kernel-certified; the mechanism map and the two checks that actually matter.
metadata:
  type: project
---

As of 2026-08-20 every one of the fifty-one no-go moment orbits of
`six_qubit_sslp.tex` carries a Lean 4 proof checked by the kernel alone:
51 headline `no_go_of_moments` theorems, 332 audit entries all reading
`[propext, Classical.choice, Quot.sound]`, 0 errors, 0 warnings, 90 109 lines.

This extends [[sslp-29-orbits-complete]], which covered the twenty-nine orbits of
the v7 manuscript. The twenty-two added here are orbits 5, 6, 47–52 at projective
order three and 12–15, 17–20, 24, 41–44, 46 at order two.

**The mechanism map for the second batch.** Six fell to a plain *isolation
certificate* (47, 48, 18, 41, 42, 43): a rational combination of admissible
dressings isolates one incidence monomial whose endpoints the polytope pins to
positive constants. Three more (52, 44, 46) needed the endpoints only *tied by a
positive ratio*, so each `mul_eq_zero` branch collapses. The rest needed new
algebra layers — `Triangle` (odd triangle, division-free), `Frame` (C² block
frames), `Spinor`, `ParityFour`, `Hafnian`, `Trace5`, `Flip5`, `Kernel5`.

**Two facts that cost time and are not recoverable from the sources.**

*The per-block frame equality is unavailable for orbits 14, 15 and 24.* The
achievable coefficient patterns on the eight bottom tails have rank only 5, so a
two-element block indicator is not in their span. Orbit 13 has rank 6, which is
why the cheap `Frame.block_zero` route works there and nowhere else. I briefly
believed the block structure alone made 14/15 shortcuttable; it does not, and the
paper's connectivity argument is genuinely required. Block structure existing is
not the same as the block-level moment condition being available.

*The order-two arguments depend on `Y_i` and `Y_i Z_j`.* The half-angle system's
four rows are `X_i, Y_i, X_i Z_j, Y_i Z_j`. That is exactly the class the old
`scan.dressings` dropped — see [[kl-dressings-undercount]]. Anyone re-deriving
these fourteen orbits with unfixed tooling will find the arguments invisible.

**The two checks that matter more than compilation.** `tools/verification/classify.py`
parses every headline and classifies each hypothesis as `offSum = 0`,
`diagBot = diagTop`, or `MomentSystem`; anything else is an algebraic fact
smuggled in as an assumption, which voids the proof and is invisible from the
outside. `tools/verification/admis.py` confirms every row satisfies
`|supp(e) ∪ supp(z)| ≤ 2`; a weight-3 row would silently downgrade a
distance-three no-go to a much weaker claim. Both currently return zero
violations across all 51. Run these before believing any future extension.

**Delegation lesson.** Multi-agent builds were audited by independent adversarial
agents. One auditor hit a session limit, and the orchestrator's own check then
found that the orbit-5 headline did not exist at all — the builder had said so
honestly in its docstring, but the batch would otherwise have been reported
complete. Separately, three agents editing the same files collided and one
finished proof was overwritten; parallel attempts on shared files need worktree
isolation. Both proofs survived because the displaced agent parked its version
instead of overwriting back; the spare is in `alternatives/`.

The remaining fifteen of the sixty-six rank-compatible orbits are not no-gos:
they target the realized orders {2,3,5}. Four (7, 8, 9, 36) are known realizable.
Orbit 9's explicit witness — 22 amplitudes of the form `zeta_6^k / sqrt(d)` — was
verified symbolically against all 154 conditions and would be the cheapest
existence result to formalize; see [[sslp-orbit9-witness]].
