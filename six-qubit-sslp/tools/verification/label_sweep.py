"""Sweep the manuscripts' named results for a Lean source citing each one.

A named result of the manuscript is covered by this package only if some Lean
source names it.  This is a necessary condition, not a sufficient one: a
citation means a kernel-checked statement carries the name, not that the
statement has been checked against the manuscript's hypotheses.  It is,
however, the check that repeatedly found real gaps -- the parts of a theorem
proved with the theorem itself never stated.

Results are cited two ways, because the manuscripts name them two ways.

* Most carry a `\\label{...}`, and are cited by that label.
* Some carry only the bracketed title of the environment and no label.  An
  earlier version of this sweep matched `begin{theorem}...label{...}` and so
  silently skipped every unlabelled result -- nine of them, including the
  Eastin--Knill theorem -- while reporting full coverage of the rest.  Those
  are now counted too, and cited by their title text.

Two conventions keep the count honest.

* Only Lean sources count.  Naming a result in `README.md`, in a report, or
  in this file does not make it covered.
* A Lean source may need to name a result in order to say the package does
  *not* prove it -- for instance when the certified argument takes a
  different route and skips an intermediate step.  Such names are listed
  after a `NOT-FORMALIZED:` marker and are subtracted, so saying "we do not
  prove this" cannot be mistaken for proving it.

Exit status is 1 when either manuscript is missing, so the check fails loudly
rather than silently reporting full coverage of nothing.
"""
import argparse
import os
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
LEAN_DIRS = ('MainTheory', 'SixQubit', 'SS')
DEFAULT_SOURCES = ('documents/20260905/main.tex',
                   'documents/20260905/supplementary.tex')
KINDS = 'theorem|lemma|corollary|proposition|definition|conjecture'
B = chr(92)
ENV = re.compile(B + B + r'begin\{(' + KINDS + r')\}'
                 r'(?:\[([^\]]*)\])?'
                 r'(?:\s*' + B + B + r'label\{([^}]+)\})?')
LABEL = re.compile(r'[a-z]+:[A-Za-z0-9_:-]+')


def lean_sources():
    text = []
    for directory in LEAN_DIRS:
        for dirpath, _, filenames in os.walk(os.path.join(ROOT, directory)):
            for name in filenames:
                if name.endswith('.lean'):
                    path = os.path.join(dirpath, name)
                    with open(path, encoding='utf-8', errors='ignore') as handle:
                        text.append(handle.read())
    return '\n'.join(text)


def not_formalized(blob):
    excluded = set()
    for line in blob.splitlines():
        if 'NOT-FORMALIZED:' in line:
            tail = line.split('NOT-FORMALIZED:')[1]
            excluded.update(LABEL.findall(tail))
            for quoted in re.findall(r'"([^"]+)"', tail):
                excluded.add(quoted)
    return excluded


def normalize(text):
    """Collapse runs of whitespace, so a title wrapped across two lines of a
    Lean docstring still matches the manuscript's one-line title."""
    return ' '.join(text.split())


def cited(name, blob, excluded):
    """A result is cited when a Lean source carries its name and no Lean
    source has declared that name absent."""
    return normalize(name) in blob and normalize(name) not in excluded


def sweep(sources):
    raw = lean_sources()
    blob = normalize(raw)
    excluded = {normalize(e) for e in not_formalized(raw)}
    failed = False
    for relative in sources:
        path = os.path.join(ROOT, relative)
        if not os.path.exists(path):
            print('MISSING SOURCE: %s' % relative)
            failed = True
            continue
        with open(path, encoding='utf-8') as handle:
            text = handle.read()
        results = []
        for match in ENV.finditer(text):
            kind, title, label = match.group(1), match.group(2), match.group(3)
            name = label if label else (title or '').strip()
            results.append((kind, name, bool(label)))
        missing = [(k, n, l) for k, n, l in results if not n or not cited(n, blob, excluded)]
        print('%s: %d named results, %d cited in Lean, %d not'
              % (relative, len(results), len(results) - len(missing), len(missing)))
        for kind, name, is_label in missing:
            if not name:
                reason = 'unnamed environment: no label and no title'
            elif name in excluded:
                reason = 'declared not formalized'
            else:
                reason = 'no Lean source names it'
            tag = '' if is_label else '  (title, no label)'
            print('    %-34s %s%s' % (name[:34] or '(anonymous)', reason, tag))
    return 1 if failed else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sources', nargs='*', default=list(DEFAULT_SOURCES))
    arguments = parser.parse_args()
    return sweep(arguments.sources or list(DEFAULT_SOURCES))


if __name__ == '__main__':
    sys.exit(main())
