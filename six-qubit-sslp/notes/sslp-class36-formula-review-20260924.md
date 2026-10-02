# Class 36 displayed-formula review (20260924)

Scope: the two displayed codewords, their support fibers, and the phase
conventions used by the first interactive workbench. This is a semantic review
record and symbolic transcription check, not manuscript-wide kernel acceptance.

The main manuscript SHA-256 is
`0015798c22359efffe64afd26bda2d057b71fd4b6b408062a6672193b487e542`.
The reviewed locators are `eq:six-C5-shells`, `eq:six-C5-edges`,
`eq:six-C5-code0`, `eq:six-C5-code1`, `eq:six-C5-gate-data`, and
`eq:six-C5-logical-action`. The preceding definitions of the four-qubit shells,
omega, and coefficientwise conjugation were read together with the formulas.

`tools/tests/test_explorer_manuscript.py` independently expands the paper's
shell and edge formulas using symbolic radicals, checks all 24 nonzero
amplitudes against the exported coordinates, and checks both support residues
for D and D^4. Qubit 1 is the leftmost displayed character and integer-mask bit
zero. The gate vector is `(1,1,1,1,2,3)`, distinct from the table representative
`(1,1,1,2,2,4)`. Both words have 12 nonzero entries; six squared amplitudes are
1/10 and six are 1/15. The words have disjoint supports.

Existing formal bridge references inspected:

- `MainTheory.Orbit36CanonicalAmplitudes.anchor_exact`, `edge_exact`, and
  `all_amplitudes` identify the anchor/edge scales and omega phases.
- `MainTheory.Orbit36Antiunitary.canonical_top` identifies the second word as
  coefficient conjugation, complement, and the last-two-qubit parity sign.
- The exported `SSLPExplorerCase` certificate checks the actual supplied words
  against `SixQubit.Orbit36Code`, then normalization, orthogonality, distance at
  least three, and the physical product-phase action on any logical state.

The first two bridge modules were inspected as source; this UI milestone did
not rebuild their additional dependency closures. The downloadable case
certificate has its own previously executed kernel record. Its gate theorem
assumes zeta^5=1. The D^4 UI is an exact residue consequence checked by the
symbolic test and browser simulation, but has no separate exported theorem
root in this certificate. Do not extend that certificate's badge to D^4 order
minimality, the encoder decomposition, local-unitary equivalence to the cited
external construction, enumerators, global classification, or the full text.

No acceptance-ledger entry is automatically promoted by this review. The
1652-entry 20260924 ledger still requires explicit migration and review. The
prior instruction to record the Singleton issue without editing the manuscript
remains in force.
