"""Archived one-shot documentation migration; not a current fixer."""
import io
import os
import re
import subprocess
import sys

print('ARCHIVED: no files changed. This stale one-shot migration is disabled.')
sys.exit(0)

R = 'D:/UTD/Project_purdue/Lean_certification/'
log = []

# --- real numbers, recomputed rather than restated -------------------------
orb_lines = orb_thms = 0
dev_lines = 0
for d in ('SixQubit', 'SS'):
    for f in os.listdir(R + d):
        if not f.endswith('.lean'):
            continue
        s = io.open(R + d + '/' + f, encoding='utf-8').read()
        dev_lines += s.count(chr(10))
        if d == 'SixQubit' and 'theorem no_go_of_moments' in s and not f.startswith('Code'):
            orb_lines += s.count(chr(10))
            orb_thms += len(re.findall(r'^theorem ', s, re.M))
hits = lines = 0
for d in ('SixQubit', 'SS'):
    for f in os.listdir(R + d):
        if not f.endswith('.lean'):
            continue
        for ln in io.open(R + d + '/' + f, encoding='utf-8'):
            k = ln.count('sorry') + ln.count('native_decide')
            if k:
                hits += k
                lines += 1
print('orbit modules %d lines / %d theorems; whole development %d lines'
      % (orb_lines, orb_thms, dev_lines))
print('sorry|native_decide: %d occurrences on %d lines' % (hits, lines))


def edit(path, pairs):
    p = R + path
    s = io.open(p, encoding='utf-8').read()
    for a, b in pairs:
        if a in s:
            s = s.replace(a, b)
            log.append('%s: %s' % (path, a[:50].replace(chr(10), ' ')))
    io.open(p, 'w', encoding='utf-8').write(s)


edit('README.md', [
    ('All 29 are checked by the **Lean kernel alone**',
     'All 51 are checked by the **Lean kernel alone**'),
    ('| `SixQubit/` | 29 orbit modules, 4 algebra modules, the audit |',
     '| `SixQubit/` | 51 orbit modules, 12 algebra modules, 51 code-level wrappers, the audit |'),
    ('| Lines in orbit modules | 26,600 |',
     '| Lines in orbit modules | %s |' % format(orb_lines, ',')),
    ('| Theorems in orbit modules | 6,650 |',
     '| Theorems in orbit modules | %s |' % format(orb_thms, ',')),
    ('| Lines in the whole development | 25,703 |',
     '| Lines in the whole development | %s |' % format(dev_lines, ',')),
    ('Every hit must be inside a docstring — there are 33, of which 28 are the sentence\n'
     'stating that `native_decide` is not used.',
     'Every hit must be inside a docstring or comment. There are %d occurrences on %d\n'
     'lines; most are the sentence in each module stating that `native_decide` is not\n'
     'used. The check that matters is the axiom footprint, not the grep count: an\n'
     'escape hatch actually used would show up in `#print axioms` as `sorryAx` or\n'
     '`Lean.ofReduceBool`, and none does.' % (hits, lines)),
    ('python tools/run.py verification/admis.py 5 6 12 13 14 15 17 19 20 24 49 51',
     'python tools/run.py verification/admis.py            # all 51 by default'),
])

edit('results/README.md', [
    ("Totals: 51 orbits, 40,038 lines,\n12,222 theorems.",
     'Totals: 51 orbits, %s lines, %s theorems.' % (format(orb_lines, ','),
                                                    format(orb_thms, ','))),
    ("(`Order9` predates the current naming convention and stores its angle data\n"
     "differently, so its `q`/`a`/`delta` cells read `?`. Its certification is unaffected;\n"
     "this is a table-filling gap, not a proof gap.)",
     '(`Order9` predated the current conventions; it now carries an `av` definition like\n'
     'every other module, so its `q`/`a`/`delta` cells are filled in and the acceptance\n'
     'gate checks it like the rest.)'),
])

edit('notes/sslp-51-orbits-complete.md', [
    ('230 audit entries all reading', '332 audit entries all reading'),
])

# --- the tex: the Scope paragraph, and the stale repair note ---------------
P = R + 'formalization/formalization.tex'
s = io.open(P, encoding='utf-8').read()
i = s.find(r'\medskip' + chr(10) + r'\noindent\textbf{Scope, stated precisely.}')
j = s.find(r'\end{abstract}')
if i > 0 and j > i:
    NEW = (r'''\medskip
\noindent\textbf{Scope, stated precisely.} Each orbit carries two theorems. The
first, \lean{no\_go\_of\_moments}, takes its Knill--Laflamme rows as hypotheses
and derives a contradiction. The second, \lean{no\_code}, assumes only that the
two logical states are supported on the residue-$0$ and residue-$\delta$ fibers,
are normalized, and satisfy \lean{SS.HasDistance ![c, d] 3}; every
Knill--Laflamme row is then \emph{derived} through
\lean{SixQubit/CodeBridge.lean}. So the development does establish, inside the
kernel, that no exact $((6,2,3))$ code is supported on any of these fifty-one
orbits. What it does \emph{not} yet establish is that every code must be
supported on one of them: the reduction of an arbitrary code to one of the
sixty-six rank-compatible moment orbits, and the transport of other angle
records to the chosen representatives, are not formalized. Section
\ref{sec:openitems} states this boundary.
''')
    s = s[:i] + NEW + s[j:]
    log.append('formalization.tex: Scope paragraph rewritten')
s = s.replace('found this; the four modules are being rebuilt at the correct residue.',
              'found this; all four were rebuilt at the correct residue, and the correct\n  fibers are disjoint from the ones the old proofs used.')
s = s.replace('Three items concern the formalization itself.',
              'Two items concern the formalization itself.')
io.open(P, 'w', encoding='utf-8').write(s)

print()
print('corrections:')
for c in log:
    print('  ' + c)
