---
name: kl-dressings-undercount
description: "The scratchpad `scan.dressings` under-generates admissible Pauli dressings; the corrected set is what unlocked orbit 33."
metadata:
  type: project
---

`tools/core/scan.py`'s `dressings(e)` returns the WRONG admissible set for the
six-qubit Knill-Laflamme scan:

* `|e| = 1`: it returns 7 strings (`{0} u {e_j}`), but the correct set is 12 --
  `{0, e_i} x {0, e_j}` where `i` is the flipped site.  It drops every
  `e_i + e_j` with `j != i`, i.e. every `Y_i Z_j`.
* `e = 0`: it returns nothing at all, dropping all 22 pure-`Z` conditions --
  the moment equations and, crucially, `Z_i` and `Z_i Z_j`.
* `|e| = 2`: 4, which is correct.

Correct total over all `|e| <= 2`: **154 = 1 + 6*3 + 15*9**, the number of
weight-<=2 Paulis on six qubits.  `tools/core/kl.py` (`dressings_full`,
`conditions`) has the fixed version; it enumerates all 64 `z` and filters on
`|supp(e) u supp(z)| <= 2` rather than being clever.

Consequences:

* Every orbit certified with the old set is still valid -- those proofs used a
  SUBSET of the true conditions, so they only got harder, never wrong.
* Orbit 33 was blocked by exactly this.  Its argument needs `F ⊗ Z_j` for `F`
  ranging over `I, X, Y, Z` on the zero-angle qubit, and three of those four
  families were missing.
* `relations.py` now imports `dressings_full`; with it, orbit 33's rho
  component grows from `{0,2,6,8}` to `{0,1,2,6,7,8}`.

`relations.analyse` additionally returns `None` when `S1` is not the bitwise
complement of `S0` (angle vectors summing to `0 mod q`, e.g. orbit 29).
`tools/core/relgen.py` is the complement-free replacement.

See [[sslp-nogo-mechanism-ladder]] and [[sslp-orbit33-block-recipe]].
