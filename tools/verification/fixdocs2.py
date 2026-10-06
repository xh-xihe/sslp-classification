"""Archived one-shot documentation migration; not a current fixer."""
import io
import sys

print('ARCHIVED: no files changed. This stale one-shot migration is disabled.')
sys.exit(0)

R = 'D:/UTD/Project_purdue/Lean_certification/'
changed = []

# ---- results/README.md : the delta claim, and the table description
P = R + 'results/README.md'
s = io.open(P, encoding='utf-8').read()
OLD = ("`delta` here is the value pinned by the polytope dimension `d_LP`, not merely by\n"
       "fiber sizes. That distinction matters: an earlier scan chose `delta` by size\n"
       "alone and reported four orbits closed when their polytopes were simply infeasible\n"
       "under a wrong `delta`.")
NEW = ("`delta` is taken from `tools/manifest.json`, where it is *defined* as `q/m` from the\n"
       "paper's own 66-orbit table, and every module is checked against it by\n"
       "`tools/verification/gate.py`.\n\n"
       "This replaces an earlier and weaker rule. The original scan chose `delta` by fiber\n"
       "size; a later pass added a polytope-dimension check but applied it only to the orbits\n"
       "outstanding at that moment. Orbits 30, 53, 55 and 65 had already been certified and\n"
       "were never re-checked, and all four turned out to use a residue of additive order two\n"
       "rather than the order their projective order demands. A collaborator's audit found\n"
       "this; all four have since been rebuilt at `delta = q/m`, and the correct fibers are\n"
       "disjoint from the ones the old proofs used, so they are new proofs rather than\n"
       "relabelled ones.\n\n"
       "Fiber cardinalities in the table are COMPUTED from `(q, a, delta)`, not counted from\n"
       "`def y`/`def z` declarations: several modules index the top fiber as\n"
       "`SS.complement y_i` and declare no `def z` at all, which the earlier counting version\n"
       "reported as a top fiber of size zero.")
if OLD in s:
    s = s.replace(OLD, NEW)
    changed.append('results/README.md delta claim')
io.open(P, 'w', encoding='utf-8').write(s)

# ---- the 162 -> 230 drift
for P, subs in (
    (R + 'README.md', [('# expect 162 clean axiom lines', '# expect 230 clean axiom lines')]),
    (R + 'formalization/formalization.tex', [
        ('captured in \\path{results/axiom-audit.txt}, is 162 lines,',
         'captured in \\path{results/axiom-audit.txt}, is 230 lines,'),
        ('prints the 162 axiom lines; every one must read',
         'prints the 230 axiom lines; every one must read')]),
):
    s = io.open(P, encoding='utf-8').read()
    for a, b in subs:
        if a in s:
            s = s.replace(a, b)
            changed.append('%s: %s' % (P.split('/')[-1], a[:40]))
    io.open(P, 'w', encoding='utf-8').write(s)

print('corrections applied:')
for c in changed:
    print('  ' + c)
if not changed:
    print('  (none matched -- check the anchors)')
