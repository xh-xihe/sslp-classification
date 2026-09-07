"""Sweep the manuscripts' named results for a Lean source citing each label.

A named result of the manuscript is covered by this package only if some Lean
source names its label.  This is a necessary condition, not a sufficient one:
a cited label means a kernel-checked statement carries it, not that the
statement has been checked against the manuscript's hypotheses.  It is,
however, the check that repeatedly found real gaps -- the parts of a theorem
proved with the theorem itself never stated.

Two conventions keep the count honest.

* Only Lean sources count.  Naming a label in `README.md`, in a report, or in
  this file does not make it covered; an earlier version of this sweep counted
  README mentions and so scored labels that the README named precisely as
  *missing*.
* A Lean source may need to name a label in order to say the package does
  *not* prove it -- for instance when the certified argument takes a different
  route from the manuscript's and skips an intermediate step.  Such labels are
  listed after a `NOT-FORMALIZED:` marker and are subtracted, so saying "we do
  not prove this" cannot be mistaken for proving it.

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
NAMED = re.compile(B + B + r'begin\{(' + KINDS + r')\}'
                   r'(?:\[[^\]]*\])?\s*' + B + B + r'label\{([^}]+)\}')
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
            excluded.update(LABEL.findall(line.split('NOT-FORMALIZED:')[1]))
    return excluded


def sweep(sources):
    blob = lean_sources()
    excluded = not_formalized(blob)
    failed = False
    for relative in sources:
        path = os.path.join(ROOT, relative)
        if not os.path.exists(path):
            print('MISSING SOURCE: %s' % relative)
            failed = True
            continue
        with open(path, encoding='utf-8') as handle:
            text = handle.read()
        labels = [match.group(2) for match in NAMED.finditer(text)]
        missing = [label for label in labels
                   if label not in blob or label in excluded]
        print('%s: %d named results, %d cited in Lean, %d not'
              % (relative, len(labels), len(labels) - len(missing), len(missing)))
        for label in missing:
            reason = ('declared not formalized' if label in excluded
                      else 'no Lean source names it')
            print('    %-32s %s' % (label, reason))
    return 1 if failed else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sources', nargs='*', default=list(DEFAULT_SOURCES))
    arguments = parser.parse_args()
    return sweep(arguments.sources or list(DEFAULT_SOURCES))


if __name__ == '__main__':
    sys.exit(main())
