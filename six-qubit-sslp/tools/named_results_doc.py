#!/usr/bin/env python3
"""Generate the human-readable map from each named result to its Lean proof.

`results/paper-claims-20260908.json` is the authority, but it is 1.6 MB of
JSON: correct to check against, useless to read.  This renders the part a
reader actually wants -- every theorem, lemma, proposition, corollary,
definition and example of the two manuscripts, in document order, with the
kernel-checked declarations that carry it and the review that says why -- as
one markdown file.

Two rules are deliberate.

*   **No manuscript text.**  The sources are an unpublished collaborator draft
    and are gitignored; this repository refers to them by label and line
    number only.  So does this document.  Section headings here are written
    from the label names, not copied from the sources, and the prose under
    each entry is the review, which is our own writing.

*   **Fail loud on an unmapped label.**  Grouping is by an explicit table.  A
    label that matches no rule is an error, not an "Other" bucket, because a
    silent catch-all is exactly how a new result would go unlisted.

Usage:
    python tools/named_results_doc.py            # write the document
    python tools/named_results_doc.py --check    # fail if it is out of date
"""
import io
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, 'results', 'paper-claims-20260908.json')
OUTPUT = os.path.join(ROOT, 'results', 'named-results-20260908.md')

CORE_KINDS = ('theorem', 'lemma', 'proposition', 'corollary', 'definition', 'example')
NAMED_KINDS = CORE_KINDS + ('remark', 'table', 'longtable')

# (source, ordered rules).  First match wins; the rules are on the label.
GROUPS = {
    'main.tex': [
        ('Transversality no-go background', [r'^theorem@475$']),
        ('The projective logical group: finiteness, commutativity, finite lifts',
         [r'^thm:finite-projective-group$', r'^lem:phase-sector', r'^lem:phase-sectors$',
          r'^thm:qualitative-finite-lift$', r'^ex:five-qubit-rationalization$',
          r'^lem:denominator-clearing$', r'^thm:colored-finite-lift$',
          r'^cor:quantitative-projective-group$']),
        ('The SSLP normal form', [r'^thm:general-sslp-normal-form$', r'^cor:rank-two-sslp$']),
        ('Bounds on the primitive physical lift order q',
         [r'^cor:K2-q-bound$', r'^thm:d2-sslp-classification$', r'^lem:common-affine-span$',
          r'^thm:d3-bound$', r'^thm:d3-sslp-classification$']),
        ('Exactness of the three-layer pipeline', [r'^thm:sslp-completeness$']),
        ('The six-qubit enumeration and its reduction stages',
         [r'^def:six-', r'^thm:six-66-orbits$', r'^lem:six-', r'^proposition@2397$',
          r'^lemma@2712$']),
        ('Six-qubit results',
         [r'^six:thm:global-status$', r'^thm:six-15-sslp-realization-orbits$',
          r'^thm:six-WE-status$', r'^thm:unique-C5-LU$', r'^remark@', r'^rem:', r'^six:rem:']),
    ],
    'supplementary.tex': [
        ('The 66-orbit directory', [r'^tab:66orbits$']),
        ('Orbit 36: rigidity of the order-five sector',
         [r'^lem:o36', r'^thm:o36']),
        ('Exact weight-enumerator images of the realized orbits',
         [r'^thm:o7weightimage$', r'^lem:o7', r'^thm:o8weightimage$', r'^lem:o8',
          r'^cor:o8', r'^thm:o9weightimage$', r'^lem:o9', r'^cor:o9',
          r'^thm:m2-five-stabilizer-orbits$', r'^thm:o21-enumerator$',
          r'^thm:o45-weightimage$', r'^cor:m2-current-status$',
          r'^tab:angle-record-counts$', r'^tab:fiber-pair-counts$',
          r'^remark@1995$']),
        ('No-gos at physical lift order nine',
         [r'^lem:twoedge$', r'^thm:q9', r'^cor:q9', r'^remark@4105$']),
        ('No-gos at physical lift order eight',
         [r'^prop:q8', r'^thm:q8', r'^cor:q8', r'^remark@4512$']),
        ('No-gos at physical lift order seven',
         [r'^prop:q7', r'^thm:q7', r'^cor:q7', r'^remark@5233$']),
        ('No-gos at physical lift order six',
         [r'^prop:q6', r'^thm:q6', r'^cor:q6', r'^remark@6155$']),
        ('No-gos at physical lift order four',
         [r'^proposition@6382$', r'^lem:q4o', r'^thm:q4o', r'^prop:q4o',
          r'^proposition@6973$', r'^proposition@7018$', r'^proposition@7169$',
          r'^proposition@8442$', r'^proposition@8477$', r'^thm:q4nogo$',
          r'^tab:q4o29faces$', r'^tab:q4o31supportorbits$', r'^tab:q4status$',
          r'^remark@76', r'^remark@81', r'^remark@6214$', r'^remark@8377$']),
        ('The complete order classification', [r'^cor:completeorderclassification$']),
        ('Logical order five: the other seven orbits',
         [r'^thm:m5-', r'^cor:m5-', r'^prop:o5-nogo$', r'^prop:o6-nogo$']),
        ('Logical order three',
         [r'^lem:m3lift-', r'^prop:o4[789]-nogo$', r'^prop:o5[012]-nogo$',
          r'^thm:m3-', r'^cor:m3-']),
        ('Logical order two',
         [r'^prop:o1[2345789]-nogo$', r'^prop:o2[04]-nogo$', r'^prop:o4[12446]',
          r'^prop:o42o43-nogo$', r'^lem:m2-fullrank-matching$', r'^lem:parity4-',
          r'^lem:connected-orthogonality$', r'^thm:m2-fourteen-nogos$',
          r'^cor:m2-eleven-remaining$']),
    ],
}

STATUS_MARK = {'covered': 'covered', 'partial': 'partial', 'conjecture': 'conjecture',
               'unreviewed': 'UNREVIEWED'}


def label_of(entry):
    return entry['id'].split(':', 1)[1]


def group_of(source, label):
    for title, rules in GROUPS[source]:
        for rule in rules:
            if re.search(rule, label):
                return title
    return None


def load():
    with io.open(LEDGER, encoding='utf-8') as handle:
        return json.load(handle)


def render(ledger):
    entries = [c for c in ledger['claims'] if c['kind'] in NAMED_KINDS]
    unmapped = []
    for entry in entries:
        source = entry['source'].split('/')[-1]
        if group_of(source, label_of(entry)) is None:
            unmapped.append('%s (%s, line %d)' % (entry['id'], entry['kind'], entry['line']))
    if unmapped:
        sys.stderr.write('FAIL: %d named results match no grouping rule. Add a rule; '
                         'do not let them fall into a catch-all.\n' % len(unmapped))
        for item in unmapped:
            sys.stderr.write('  %s\n' % item)
        raise SystemExit(1)

    core = [c for c in entries if c['kind'] in CORE_KINDS]
    other = [c for c in entries if c['kind'] not in CORE_KINDS]
    counts = {}
    for entry in entries:
        counts.setdefault(entry['kind'], {'covered': 0, 'partial': 0, 'n': 0})
        counts[entry['kind']]['n'] += 1
        counts[entry['kind']][entry['status']] = \
            counts[entry['kind']].get(entry['status'], 0) + 1

    out = []
    w = out.append
    w('# Named results of the 20260908 manuscripts, and the Lean that carries them')
    w('')
    w('Every `theorem`, `lemma`, `proposition`, `corollary`, `definition` and')
    w('`example` environment of `main.tex` and `supplementary.tex`, in document')
    w('order, with the kernel-checked declarations that carry it. The `remark`')
    w('and `table` environments follow, because nine of them are the only named')
    w('entries that are not fully covered and it would be evasive to omit them.')
    w('')
    w('This file is generated by `tools/named_results_doc.py` from')
    w('`results/paper-claims-20260908.json`, which is the authority. Regenerate')
    w('with `python tools/named_results_doc.py`; `--check` fails if it is stale.')
    w('Edit the generator, never this file.')
    w('')
    w('## What a row means')
    w('')
    w('**covered** means a reviewed pairing: a reader proposed the declarations')
    w('that state or prove the result, and an adversarial checker read those')
    w('declarations and tried to refute the pairing. The rule applied throughout')
    w('is that a checked declaration has to carry the *whole* statement; a')
    w('declaration proving a special case, or one direction of an equivalence, is')
    w('not enough. It is a review judgement, not a mechanical proof that the LaTeX')
    w('and the Lean say the same thing.')
    w('')
    w('**covered does not mean the manuscript\'s own proof was formalized step by')
    w('step.** Several orbit no-gos here take a deliberately repaired route --')
    w('orbit 26 closes a mixed-axis branch the manuscript passes over, orbit 30')
    w('replaces a two-point magnitude argument with a support-graph one. The')
    w('*statement* is proved; a particular intermediate line of the manuscript\'s')
    w('own argument may have no counterpart, and those displays are recorded')
    w('`partial` in the ledger with a reason.')
    w('')
    w('Line numbers are into the manuscript sources, which are not redistributed')
    w('here. No manuscript text appears in this file: the group headings below are')
    w('written from the label names, and the prose under each entry is our review.')
    w('')
    w('## Counts')
    w('')
    w('| environment | total | covered | partial |')
    w('| --- | ---: | ---: | ---: |')
    for kind in NAMED_KINDS:
        if kind not in counts:
            continue
        c = counts[kind]
        w('| %s | %d | %d | %d |' % (kind, c['n'], c.get('covered', 0), c.get('partial', 0)))
    core_n = sum(counts[k]['n'] for k in CORE_KINDS if k in counts)
    core_c = sum(counts[k].get('covered', 0) for k in CORE_KINDS if k in counts)
    w('')
    w('**%d of %d** theorems, lemmas, propositions, corollaries, definitions and'
      % (core_c, core_n))
    w('examples are covered, with no partial and no unreviewed among them. The')
    w('nine partial named entries are all `remark` or `table`, and each says why')
    w('in its own row.')
    w('')
    w('An independent count agrees: `tools/verification/label_sweep.py` sweeps the')
    w('sources for a Lean file citing each labelled result and finds all 33 of')
    w('`main.tex` and all 93 of `supplementary.tex`. Its `KINDS` are theorem,')
    w('lemma, corollary, proposition, definition and conjecture, so the two counts')
    w('are taken different ways over nearly the same set.')
    w('')
    w('## How to check a row yourself')
    w('')
    w('```')
    w('grep -rn "theorem <declaration>" MainTheory SixQubit SS')
    w('python tools/verification/check_audit_names.py    # every cited name resolves')
    w('python tools/verify.py --only axioms              # footprint of every cited name')
    w('```')
    w('')

    for source in ('main.tex', 'supplementary.tex'):
        rows = [c for c in core if c['source'].endswith(source)]
        rows.sort(key=lambda c: c['line'])
        w('---')
        w('')
        w('# `%s` --- %d named results' % (source, len(rows)))
        w('')
        for title, _rules in GROUPS[source]:
            block = [c for c in rows if group_of(source, label_of(c)) == title]
            if not block:
                continue
            w('## %s' % title)
            w('')
            for entry in block:
                w('### `%s` (%s, line %d) --- %s'
                  % (label_of(entry), entry['kind'], entry['line'],
                     STATUS_MARK[entry['status']]))
                w('')
                for declaration in entry['lean_declarations']:
                    w('- `%s`' % declaration)
                w('')
                review = ' '.join((entry.get('review') or '').split())
                w(review if review else '_No review recorded._')
                w('')

    w('---')
    w('')
    w('# Remarks and tables')
    w('')
    w('These are named environments but not stated results. Nine of them are')
    w('`partial`, and they are the only named entries that are: five remarks,')
    w('whose comparative, counting or status sentences have no single declaration')
    w('to point at, and four tables recording audits this development either')
    w('reaches by another means or does not perform.')
    w('')
    for source in ('main.tex', 'supplementary.tex'):
        rows = [c for c in other if c['source'].endswith(source)]
        rows.sort(key=lambda c: c['line'])
        if not rows:
            continue
        w('## `%s`' % source)
        w('')
        for entry in rows:
            w('### `%s` (%s, line %d) --- %s'
              % (label_of(entry), entry['kind'], entry['line'],
                 STATUS_MARK[entry['status']]))
            w('')
            for declaration in entry['lean_declarations']:
                w('- `%s`' % declaration)
            w('')
            review = ' '.join((entry.get('review') or '').split())
            w(review if review else '_No review recorded._')
            w('')

    w('---')
    w('')
    w('# What this document does not claim')
    w('')
    w('* **The displays are a separate question.** The ledger holds 1440 displayed')
    w('  equations besides these named entries; 311 of them are `partial`. Most')
    w('  are steps of a manuscript route this development does not take, or local')
    w('  notation a repaired route never forms. See `README.md` for the breakdown.')
    w('* **Three recorded errata stand.** `eq:quantum-Singleton` is false as')
    w('  written and has a kernel-checked counterexample;')
    w('  `eq:o7knowntransversal` names a cited construction whose gate convention')
    w('  provably fails to preserve the span at theta = 0; the orbit-9 literal')
    w('  witness has an ambiguous printed bit order. They are displays, not named')
    w('  results, so every row above is unaffected -- but the manuscript is not')
    w('  error-free. See `results/errata-20260908.md`.')
    w('* **Running prose is reviewed separately.** Assertions made in text rather')
    w('  than in a display or a named result are not rows here.')
    w('')
    return '\n'.join(out) + '\n'


def main():
    check = '--check' in sys.argv[1:]
    text = render(load())
    if check:
        if not os.path.exists(OUTPUT):
            sys.stderr.write('FAIL: %s does not exist; run the generator.\n' % OUTPUT)
            return 1
        current = io.open(OUTPUT, encoding='utf-8').read()
        if current != text:
            sys.stderr.write('FAIL: %s is stale; regenerate with '
                             'python tools/named_results_doc.py\n' % OUTPUT)
            return 1
        sys.stdout.write('named-results document is current\n')
        return 0
    io.open(OUTPUT, 'w', encoding='utf-8', newline='\n').write(text)
    sys.stdout.write('wrote %s (%d bytes)\n' % (OUTPUT, len(text.encode('utf-8'))))
    return 0


if __name__ == '__main__':
    sys.exit(main())
