"""Measure the prose tics that make writing read as machine-generated, and check
that no scope disclaimer is repeated across the manuscript.

Comments are stripped before measuring: LaTeX comment rules such as
`% ------------------------------` contain `---` and would otherwise swamp the
em-dash count.

Exits nonzero if a disclaimer is repeated or a tic rises above its ceiling.
"""

import io
import re
import sys

TICS = {
    'cleft "X is/are what Y"': r'\b(is|are) what\b',
    'hedge "seem / appear to"': r'\bseems?\b|\bappears? to\b',
    '"worth (v-ing)"': r'\bworth \w+ing\b',
    'em-dash aside': r'---',
    '"It is X that Y"': r'\bIt is [a-z][^.]{0,40}\bthat\b',
    '"not merely / indeed / moreover"': r'\bnot merely\b|\bIndeed,|\bMoreover,',
    'sentence-initial "This is"': r'(?m)(?<=\.\s)This is\b',
}

# occurrences per thousand words, at roughly twice the current level, so that a
# regression trips them
LIMITS = {
    'cleft "X is/are what Y"': 0.6,
    'hedge "seem / appear to"': 0.5,
    '"worth (v-ing)"': 0.5,
    'em-dash aside': 4.0,
    '"It is X that Y"': 0.5,
    '"not merely / indeed / moreover"': 0.5,
    'sentence-initial "This is"': 0.7,
}

DISCLAIMERS = {
    'rate falls to zero': r'rate (of the family )?falls to zero',
    'not for encoding at scale': r'candidate for encoding at scale',
    'lower-bound caveat': r'lower bound',
}

FILES = ['dyadic_lifts.tex']


def strip_comments(src):
    """Drop everything after an unescaped % on each line."""
    out = []
    for line in src.split('\n'):
        cut, esc = None, False
        for k, ch in enumerate(line):
            if ch == '\\':
                esc = not esc
                continue
            if ch == '%' and not esc:
                cut = k
                break
            esc = False
        out.append(line if cut is None else line[:cut])
    return '\n'.join(out)


def strip_captions(src):
    """Remove \\caption{...} bodies. A caption has to stand alone, so a caveat
    repeated between a caption and the body text is not a repetition."""
    out, i, n = [], 0, len(src)
    while i < n:
        j = src.find(r'\caption{', i)
        if j < 0:
            out.append(src[i:])
            break
        out.append(src[i:j])
        k, depth = j + len(r'\caption{'), 1
        while k < n and depth:
            if src[k] == '{':
                depth += 1
            elif src[k] == '}':
                depth -= 1
            k += 1
        i = k
    return ''.join(out)


text = {f: strip_comments(io.open(f, encoding='utf-8').read()) for f in FILES}
# line wrapping must not hide a repeated phrase
flat = {f: ' '.join(t.split()) for f, t in text.items()}
body = {f: ' '.join(strip_captions(t).split()) for f, t in text.items()}
words = sum(len(t.split()) for t in text.values())

print('words in manuscript sources (comments stripped): %d\n' % words)
print('tic                                   count   per 1000   ceiling')
over = 0
for name, pat in sorted(TICS.items()):
    n = sum(len(re.findall(pat, t)) for t in flat.values())
    rate = 1000.0 * n / words
    lim = LIMITS.get(name, 99.0)
    flag = '  <-- over' if rate > lim else ''
    over += 1 if rate > lim else 0
    print('%-36s %5d   %6.2f     %5.1f%s' % (name, n, rate, lim, flag))

print('\ndisclaimer                       occurrences (at most 1; 0 = not made here)')
bad = 0
for name, pat in DISCLAIMERS.items():
    n = sum(len(re.findall(pat, t)) for t in body.values())
    flag = '  <-- repeated' if n > 1 else ('  (absent)' if n == 0 else '')
    bad += 1 if n > 1 else 0
    print('%-32s %d%s' % (name, n, flag))

if bad or over:
    print('\n%d disclaimer(s) repeated, %d tic(s) over ceiling' % (bad, over))
    sys.exit(1)
print('\nno disclaimer repeated, no tic over its ceiling')
sys.exit(0)
