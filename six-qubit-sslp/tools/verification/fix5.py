"""Final corrections: admis declared-count independence, and the documents.

Written to a FILE rather than passed inline: the previous attempt put backticks
inside a double-quoted shell argument and bash executed them as command
substitution.
"""
import io
import re

BS = chr(92)
BT = chr(96)
R = 'D:/UTD/Project_purdue/Lean_certification/'
log = []

# --- admis.py: count declared rows by the bare keyword ---------------------
p = R + 'tools/verification/admis.py'
s = io.open(p, encoding='utf-8').read()
old = None
for line in s.split(chr(10)):
    if 'declared = len(re.findall' in line:
        old = line
        break
if old is not None:
    idx = s.index(old)
    end = s.index(chr(10), s.index('diagBot', idx)) + 1
    new = (
        "    # Count declared rows by the BARE keyword. Reusing the parser's own\n"
        "    # `offSum c d` prefix made both counters blind to the same unexpected\n"
        "    # spelling -- `offSum (c) d e1 t2 = 0` -- so they agreed while both\n"
        "    # missed the row, and the script still printed OK.\n"
        "    declared = (len(re.findall(r'" + BS + "boffSum" + BS + "b', body))\n"
        "                + len(re.findall(r'" + BS + "bdiagBot" + BS + "b', body)))\n")
    s = s[:idx] + new + s[end:]
    io.open(p, 'w', encoding='utf-8').write(s)
    log.append('admis.py: declared count now independent of the parser prefix')

# --- the delta note itself -------------------------------------------------
p = R + 'notes/sslp-orbit-delta-identification.md'
s = io.open(p, encoding='utf-8').read()
s = re.sub(r'^description: .*$',
           'description: SUPERSEDED - delta is q/m with additive order m; '
           'd_LP was an earlier and insufficient proxy.',
           s, count=1, flags=re.M)
if 'SUPERSEDED' not in s.split('---')[-1]:
    body = s.split('---')
    body[-1] = ('\n\n**SUPERSEDED.** The authoritative rule is delta = q/m, whose additive\n'
                'order in Z_q must equal m; see tools/manifest.json and\n'
                'tools/verification/gate.py. Pinning delta by d_LP, or by fiber size, is\n'
                'what let four modules prove a no-go for the wrong projective order --\n'
                'their fibers had equal sizes and empty intersection.\n'
                + body[-1].lstrip())
    s = '---'.join(body)
io.open(p, 'w', encoding='utf-8').write(s)
log.append('delta note: marked superseded in the body, not only the index')

# --- the tex: restore the eaten backslash, fix the layout count ------------
p = R + 'formalization/formalization.tex'
s = io.open(p, encoding='utf-8').read()
if (chr(10) + 'oindent Nine more') in s:
    s = s.replace(chr(10) + 'oindent Nine more', chr(10) + BS + 'noindent Nine more')
    log.append('formalization.tex: restored the backslash on \\noindent')
if 'twelve algebra modules' in s:
    s = s.replace('twelve algebra modules', 'thirteen algebra modules')
    log.append('formalization.tex: twelve -> thirteen algebra modules')
io.open(p, 'w', encoding='utf-8').write(s)

# --- the two counts in the READMEs ----------------------------------------
p = R + 'tools/README.md'
s = io.open(p, encoding='utf-8').read()
s = re.sub(r'injects \d+ corruptions', 'injects 749 corruptions', s)
io.open(p, 'w', encoding='utf-8').write(s)
log.append('tools/README.md: mutation count refreshed')

p = R + 'README.md'
s = io.open(p, encoding='utf-8').read()
s = s.replace('Section 8 lists the two open items',
              'Section 8 lists what remains open')
io.open(p, 'w', encoding='utf-8').write(s)
log.append('README.md: open-items wording')

print('corrections:')
for c in log:
    print('  ' + c)
