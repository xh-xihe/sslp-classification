#!/usr/bin/env python3
"""Check that every root in a Lean axiom audit is declared.

Both `#certification_axioms` inventories and legacy `#print axioms` commands
are read using the shared Lean source lexer. A misspelled declaration is invisible until
the serial build reaches that file, which is hours in.  This resolves every
name against the declarations actually present in the sources, by tracking
`namespace` / `end` per file so the match is on the fully qualified name and
not merely on the last component.

It is a source-level check, deliberately cheaper and weaker than elaboration:
it does not know about `export`, `open ... in`, or names introduced by macros,
so a reported miss is a prompt to look rather than a proof of absence. Imported
Mathlib roots are also resolved against their declarations in the locally
installed dependency sources. Names it cannot resolve are printed with the
closest same-basename candidates. Kernel elaboration and the transitive axiom
audit remain separate checks.

Usage:  python tools/verification/check_audit_names.py
Exit code 1 if any name is unresolved.
"""
import io
import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'tools'))
from lean_source import code_only
from lean_audit import audit_names
LEAN_DIRS = ('MainTheory', 'SS', 'SixQubit', 'QECC', 'Orbit2')
AUDIT_FILES = ('MainTheory/Audit.lean', 'SixQubit/Audit.lean',
               'SixQubit/CodeWrapAudit.lean',
               'SixQubit/Orbit7CollinearAxiomCheck.lean',
               'MainTheory/ProseCitationAudit.lean', 'QECC/Audit.lean',
               'MainTheory/OrbitCertificationAudit.lean',
               'MainTheory/OrbitCertificationFinalAudit.lean',
               'MainTheory/ReviewedDeclarationsAudit.lean',
               'MainTheory/ManuscriptCertificationAudit20261005.lean', 'Orbit2.lean')

# Lean identifiers admit far more than ASCII: subscripts (`cov_eq₂`), Greek
# letters, primes.  Narrowing this to `[A-Za-z0-9_]` produces false misses, so
# the continuation class is everything outside the delimiters a declaration
# head can end on.
HEAD = '[A-Za-z_À-￿]'
TAIL = '[A-Za-z0-9_.\'!?À-￿]*'
IDENT = '(' + HEAD + TAIL + ')'

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|inductive|instance|alias|class)\s+'
    + IDENT)
STRUCTURE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:structure|class)\s+' + IDENT)
FIELD = re.compile(r'^\s{2,}' + IDENT + r'\s*(?:\{[^}]*\}\s*)?'
                   r'(?:\([^)]*\)\s*)*:')
NAMESPACE = re.compile(r'^\s*namespace\s+' + IDENT)
END = re.compile(r'^\s*end\s+' + IDENT + r'\s*$')


def lean_sources():
    for directory in LEAN_DIRS:
        base = os.path.join(ROOT, directory)
        for root, _dirs, files in os.walk(base):
            for name in sorted(files):
                if name.endswith('.lean'):
                    yield os.path.join(root, name)
        top = os.path.join(ROOT, directory + '.lean')
        if os.path.exists(top):
            yield top


def declarations(paths=None):
    """Every fully qualified declaration name the sources introduce."""
    names = set()
    for path in lean_sources() if paths is None else paths:
        stack = []
        current_structure = None
        for line in io.open(path, encoding='utf-8', errors='replace'):
            m = NAMESPACE.match(line)
            if m:
                stack.append(m.group(1))
                current_structure = None
                continue
            m = END.match(line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
                current_structure = None
                continue
            m = DECL.match(line)
            if m:
                prefix = '.'.join(stack)
                base = m.group(1)
                names.add(prefix + '.' + base if prefix else base)
                s = STRUCTURE.match(line)
                current_structure = (prefix + '.' + base if prefix else base) if s else None
                continue
            if current_structure is not None:
                if line.strip() and not line.startswith((' ', '\t')):
                    current_structure = None
                    continue
                f = FIELD.match(line)
                if f:
                    names.add(current_structure + '.' + f.group(1))
    return names


def mathlib_candidate_sources(names):
    """Locate source declarations for unresolved imported roots, without an allowlist."""
    basenames = {name.rsplit('.', 1)[-1] for name in names}
    base = os.path.join(ROOT, '.lake', 'packages', 'mathlib', 'Mathlib')
    for directory, _dirs, files in os.walk(base):
        for filename in files:
            if not filename.endswith('.lean'):
                continue
            path = os.path.join(directory, filename)
            with io.open(path, encoding='utf-8') as source:
                for line in source:
                    match = DECL.match(line)
                    if match and match.group(1).rsplit('.', 1)[-1] in basenames:
                        yield path
                        break


def audited_names():
    out = []
    for relative in AUDIT_FILES:
        path = os.path.join(ROOT, relative)
        source = io.open(path, encoding='utf-8').read()
        names = audit_names(source)
        if not names:
            raise ValueError('audit file contains no declarations: ' + relative)
        code = code_only(source)
        for name in names:
            match = re.search(r'(?<![A-Za-z0-9_.])' + re.escape(name) + r'(?![A-Za-z0-9_.])', code)
            number = code.count('\n', 0, match.start()) + 1 if match else 1
            out.append((relative, number, name))
    return out


def ledger_names(paper_version=None):
    """Every declaration the claims ledger says a reviewed claim rests on."""
    import glob
    import json
    out = []
    if paper_version is not None and not re.fullmatch(r'[0-9]{8}', paper_version):
        raise ValueError('paper version must be an eight-digit date')
    paths = ([os.path.join(ROOT, 'results', f'paper-claims-{paper_version}.json')]
             if paper_version else sorted(glob.glob(os.path.join(ROOT, 'results', 'paper-claims-*.json'))))
    for path in paths:
        try:
            ledger = json.loads(io.open(path, encoding='utf-8').read())
        except (OSError, ValueError):
            if paper_version:
                raise
            continue
        relative = os.path.relpath(path, ROOT).replace(os.sep, '/')
        for entry in ledger.get('claims', []):
            for name in entry.get('lean_declarations', []):
                out.append((relative, entry['id'], name))
    return out


def resolve(name, declared, suffixes):
    if name in declared:
        return True
    # a shorter path is accepted when some declared name ends with it, which is
    # how a file inside the namespace may refer to its own declarations.
    return name.rsplit('.', 1)[-1] in suffixes and any(
        d.endswith('.' + name) for d in declared)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper-version')
    args = parser.parse_args(argv)
    cited = ledger_names(args.paper_version)
    audited = audited_names()
    declared = declarations()
    suffixes = set(name.rsplit('.', 1)[-1] for name in declared)
    unresolved = {entry[2] for entry in audited + cited
                  if not resolve(entry[2], declared, suffixes)}
    imported = declarations(mathlib_candidate_sources(unresolved)) if unresolved else set()
    imported = imported & unresolved
    if imported:
        sys.stdout.write('imported roots resolved from local Mathlib sources: %d\n' % len(imported))
        declared.update(imported)
        suffixes.update(name.rsplit('.', 1)[-1] for name in imported)
    by_base = {}
    for name in declared:
        by_base.setdefault(name.rsplit('.', 1)[-1], []).append(name)

    sys.stdout.write('declarations found in %s: %d\n'
                     % (', '.join(LEAN_DIRS), len(declared)))

    failures = 0
    for label, entries in (('audit', audited),
                           ('claims-ledger', cited)):
        missing = [e for e in entries if not resolve(e[2], declared, suffixes)]
        sys.stdout.write('%s names checked: %d, unresolved: %d\n'
                         % (label, len(entries), len(missing)))
        for where, which, name in missing:
            base = name.rsplit('.', 1)[-1]
            sys.stdout.write('  %s  %s  %s\n' % (where, which, name))
            for candidate in by_base.get(base, [])[:3]:
                sys.stdout.write('      same basename: %s\n' % candidate)
        failures += len(missing)

    if not failures:
        sys.stdout.write('all audited and ledger-cited names resolve\n')
        return 0
    return 1


if __name__ == '__main__':
    raise SystemExit(main())
