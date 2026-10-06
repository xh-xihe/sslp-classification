"""Archived one-shot status migration; permanently disabled."""
import io
import sys

print('ARCHIVED: no files changed. This stale one-shot migration is disabled.')
sys.exit(0)

P = 'D:/UTD/Project_purdue/Lean_certification/README.md'
s = io.open(P, encoding='utf-8').read()

OLD = """| Do they state what the paper needs? | **42 of 51.** Four modules (30, 53, 55, 65) used a residue of the wrong additive order, so they prove a no-go for the wrong projective order; five more (34, 57, 59, 64, Order9) carry moment rows that do not match the order their headline passes probabilities in |"""
NEW = """| Do they state what the paper needs? | **51 of 51**, since the repair. Four modules (30, 53, 55, 65) had used a residue of the wrong additive order and were rebuilt from scratch at `delta = q/m`; five more (34, 57, 59, 64, Order9) had moment rows inconsistent with their headline ordering and were regenerated. `gate.py` now reports 51 passed, 0 failed, 0 unchecked |"""
if OLD in s:
    s = s.replace(OLD, NEW)

OLD2 = """The nine defective modules are being repaired. The guard that should have caught
them is now `tools/manifest.json` (derived from the paper's own 66-orbit table)
plus `tools/verification/gate.py`, which enforces `delta = q/m`, its additive
order, the fibers, and the moment-row ordering:"""
NEW2 = """The nine defective modules have been repaired and the gate is green. The guard
that should have existed from the start is `tools/manifest.json` (derived from
the paper's own 66-orbit table) plus `tools/verification/gate.py`, which enforces
`delta = q/m`, its additive order, the fibers, and the moment-row ordering:"""
if OLD2 in s:
    s = s.replace(OLD2, NEW2)

EXTRA = """
The third row is the one still open, and it is the largest remaining piece of
work: no module derives its Knill--Laflamme rows from a code. Until a wrapper
exists, read each theorem as *this finite system of equations is unsatisfiable*,
not *no code of this shape exists*.

For the repaired residue orbits the correct and previously-used fibers are
disjoint, so the rebuilds are genuinely new proofs rather than relabelled ones;
that is checked by recomputing both fibers from `(q, a)` and confirming zero
overlap.
"""
if 'the largest remaining piece of' not in s:
    i = s.index('```sh\npython tools/run.py verification/mkmanifest.py')
    s = s[:i] + EXTRA.lstrip() + '\n' + s[i:]

io.open(P, 'w', encoding='utf-8').write(s)
print('README status updated:', 'since the repair' in s)
