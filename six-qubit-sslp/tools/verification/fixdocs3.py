"""Sync the documentation with the post-repair state the second audit verified."""
import io
import re

R = 'D:/UTD/Project_purdue/Lean_certification/'
log = []


def edit(path, pairs, regexes=()):
    p = R + path
    s = io.open(p, encoding='utf-8').read()
    for a, b in pairs:
        if a in s:
            s = s.replace(a, b)
            log.append('%s: %s' % (path, a[:52].replace(chr(10), ' ')))
    for pat, rep in regexes:
        s2 = re.sub(pat, rep, s)
        if s2 != s:
            log.append('%s: /%s/' % (path, pat[:40]))
            s = s2
    io.open(p, 'w', encoding='utf-8').write(s)


edit('README.md', [
    ('Every one of the **29 no-go moment orbits** from Section 11 onward of\n'
     '`six_qubit_sslp_v7.tex` carries a Lean 4 proof',
     'Every one of the **51 no-go moment orbits** of `six_qubit_sslp.tex` carries a\n'
     'Lean 4 proof'),
    ("| Of those, matching the paper's target orbit | **42** (see below) |",
     "| Of those, matching the paper's target orbit | **51** |"),
    ('| Modules with a kernel-checked headline | 51 |',
     '| Modules with a kernel-checked headline | 51, each with a code-level wrapper |'),
    ('`SixQubit/Vacuity.lean` exhibits a witness satisfying every other hypothesis, so the statements are not vacuous',
     '`SixQubit/Vacuity.lean` exhibits, for **all 51**, a point-mass pair satisfying every other hypothesis, so no statement is vacuous'),
], [(r'\b230 clean axiom lines', '332 clean axiom lines'),
    (r'\| Axiom-audit entries \| 230, all clean \|',
     '| Axiom-audit entries | 332, all clean |')])

edit('results/README.md', [], [
    (r'The output of `lake build SixQubit\.Audit`, 230 lines',
     'The output of `lake build SixQubit.Audit`, 332 lines'),
    (r'\b230 lines, every one reading', '332 lines, every one reading'),
])

# the tex: replace the stale "open items" entries 1 and 2
P = R + 'formalization/formalization.tex'
s = io.open(P, encoding='utf-8').read()
i = s.find(r'\item \textbf{No code-level wrapper exists.}')
j = s.find(r'\item \textbf{The classification is not formalized.}')
if i > 0 and j > i:
    NEW = (r'''\item \textbf{Every orbit now has a code-level statement.} Each of the
  fifty-one modules carries a \lean{no\_code} theorem whose only hypotheses are
  that the two logical states are supported on the residue-$0$ and
  residue-$\delta$ fibers, are normalized, and satisfy
  \lean{SS.HasDistance ![c, d] 3}. No Knill--Laflamme row is assumed; all of them
  are derived through \lean{SixQubit/CodeBridge.lean}, and every instantiated
  Pauli is checked to have weight at most two by \lean{decide}.
  \lean{SixQubit/Vacuity.lean} exhibits, for all fifty-one, an explicit pair
  satisfying every hypothesis except the distance condition, so none of the
  statements is vacuously true.
''')
    s = s[:i] + NEW + s[j:]
    log.append('formalization.tex: open items 1-2 replaced')
    io.open(P, 'w', encoding='utf-8').write(s)

print('corrections:')
for c in log:
    print('  ' + c)
if not log:
    print('  (nothing matched)')
