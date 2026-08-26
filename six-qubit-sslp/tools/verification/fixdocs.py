"""Archived one-shot documentation migration; not a current fixer."""
import io
import sys

print('ARCHIVED: no files changed. This stale one-shot migration is disabled.')
sys.exit(0)

REPO = 'D:/UTD/Project_purdue/Lean_certification/'

# ---------------------------------------------------------------- the tex
P = REPO + 'formalization/formalization.tex'
s = io.open(P, encoding='utf-8').read()

OLD_ABS = ('Every one of the fifty-one no-go moment orbits of\n'
           '\\texttt{six\\_qubit\\_sslp.tex} now carries a Lean~4 proof that no exact\n'
           'six-qubit $((6,2,3))$ code arises from it. All fifty-one proofs are checked by')
NEW_ABS = ('Fifty-one modules of this development each carry a Lean~4 proof, checked by')
if OLD_ABS in s:
    s = s.replace(OLD_ABS, NEW_ABS)

# insert an honest scope paragraph right after the abstract's opening sentence
MARK = 'transferable part of the exercise.\n\\end{abstract}'
SCOPE = ('''transferable part of the exercise.

\\medskip
\\noindent\\textbf{Scope, stated precisely.} What each module proves is that a
specific finite system of Knill--Laflamme equations has no solution. Getting
from ``a code exists'' to ``that system holds'' is a separate reduction which is
\\emph{not} formalized here: every headline takes its Knill--Laflamme rows as
hypotheses rather than deriving them from a code, and no module invokes
\\lean{SS.HasDistance}. So the development does not yet establish, inside the
kernel, that no exact $((6,2,3))$ code arises from these orbits; it establishes
the algebraic core of each argument. Section~\\ref{sec:openitems} lists what a
full code-level statement would additionally require.
\\end{abstract}''')
if MARK in s and 'Scope, stated precisely' not in s:
    s = s.replace(MARK, SCOPE)

# the false repair claim about delta
OLD_D = ('Fixed by matching the polytope dimension\n'
         '  $d_{\\mathrm{LP}}$ as well, and re-verifying every orbit already certified.')
NEW_D = ('''Fixed by matching the polytope dimension
  $d_{\\mathrm{LP}}$ as well --- but \\emph{only for the orbits then outstanding}.
  Orbits $30$, $53$, $55$ and $65$ had already been certified and were never
  re-checked, and all four turned out to use a residue of additive order two
  instead of the order their projective order demands. A collaborator's audit
  found this; the four modules are being rebuilt at the correct residue. The
  guard that should have existed from the start is now
  \\path{tools/manifest.json} plus \\path{tools/verification/gate.py}, which
  derives $\\delta = q/m$ from the paper's own table and refuses any module whose
  residue, angle vector, fiber or moment rows disagree with it.''')
if OLD_D in s:
    s = s.replace(OLD_D, NEW_D)

io.open(P, 'w', encoding='utf-8').write(s)
print('formalization.tex: scope paragraph %s; delta claim %s'
      % ('added' if 'Scope, stated precisely' in s else 'MISSING',
         'corrected' if 'never\n  re-checked' in s else 'NOT FOUND'))

# ---------------------------------------------------------------- the README
P = REPO + 'README.md'
s = io.open(P, encoding='utf-8').read()
s = s.replace('| Orbits certified | **51 of 51** no-go orbits — complete |',
              '| Modules with a kernel-checked headline | 51 |')
s = s.replace('| Headline `no_go_of_moments` theorems | 51 |',
              '| Of those, matching the paper\'s target orbit | **42** (see below) |')
OLD_C = ('`classify.py` confirms every headline hypothesis is an off-diagonal KL row, a\n'
         'diagonal KL row, or the moment system')
NEW_C = ('`classify.py` confirms every headline hypothesis is an off-diagonal KL row, a\n'
         'diagonal KL row, or the moment system')
BANNER = '''
## Status, stated precisely

A collaborator's audit in August 2026 found that three different things were
being conflated. They are now tracked separately:

| Question | Answer |
|---|---|
| Are the 51 Lean theorems really kernel-proved? | **Yes.** 230 audit entries, all `[propext, Classical.choice, Quot.sound]`, no escape hatches |
| Do they state what the paper needs? | **42 of 51.** Four modules (30, 53, 55, 65) used a residue of the wrong additive order, so they prove a no-go for the wrong projective order; five more (34, 57, 59, 64, Order9) carry moment rows that do not match the order their headline passes probabilities in |
| Do they rule out a real code end to end? | **No module does.** Every headline takes its KL rows as hypotheses; nothing derives them from `SS.HasDistance` |

The nine defective modules are being repaired. The guard that should have caught
them is now `tools/manifest.json` (derived from the paper's own 66-orbit table)
plus `tools/verification/gate.py`, which enforces `delta = q/m`, its additive
order, the fibers, and the moment-row ordering:

```sh
python tools/run.py verification/mkmanifest.py   # rebuild the manifest
python tools/run.py verification/gate.py         # enforce it
```

Neither `classify.py` nor `admis.py` could have caught these: the first checks
that no algebraic fact is smuggled in as a hypothesis, the second that every
Pauli row has weight at most two. Both are still worth running, but neither
checks that a module targets the orbit it claims to.
'''
if 'Status, stated precisely' not in s:
    i = s.index('## Verifying, in three commands')
    s = s[:i] + BANNER.lstrip() + '\n' + s[i:]
io.open(P, 'w', encoding='utf-8').write(s)
print('README.md: status banner %s'
      % ('added' if 'Status, stated precisely' in s else 'MISSING'))
