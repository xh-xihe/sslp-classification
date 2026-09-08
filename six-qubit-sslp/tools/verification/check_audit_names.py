#!/usr/bin/env python3
"""Check that every name an audit file asks `#print axioms` about is declared.

`MainTheory/Audit.lean` and its siblings are long lists of `#print axioms`
lines.  A misspelled or renamed declaration in one of them is invisible until
the serial build reaches that file, which is hours in.  This resolves every
name against the declarations actually present in the sources, by tracking
`namespace` / `end` per file so the match is on the fully qualified name and
not merely on the last component.

It is a source-level check, deliberately cheaper and weaker than elaboration:
it does not know about `export`, `open ... in`, or names introduced by macros,
so a reported miss is a prompt to look rather than a proof of absence.  Names
it cannot resolve are printed with the closest same-basename candidates.

Usage:  python tools/verification/check_audit_names.py
Exit code 1 if any name is unresolved.
"""
import io
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN_DIRS = ('MainTheory', 'SS', 'SixQubit')
AUDIT_FILES = ('MainTheory/Audit.lean', 'SixQubit/Audit.lean',
               'SixQubit/CodeWrapAudit.lean',
               'SixQubit/Orbit7CollinearAxiomCheck.lean')

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|inductive|instance|alias|class)\s+'
    r'([A-Za-z_][A-Za-z0-9_.\'!?]*)')
STRUCTURE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:structure|class)\s+([A-Za-z_][A-Za-z0-9_.\'!?]*)')
FIELD = re.compile(r'^\s{2,}([a-zA-Z_][A-Za-z0-9_\'!?]*)\s*(?:\{[^}]*\}\s*)?'
                   r'(?:\([^)]*\)\s*)*:')
NAMESPACE = re.compile(r'^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.\']*)')
END = re.compile(r'^\s*end\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$')
PRINT = re.compile(r'^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_.\'!?]*)')


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


def declarations():
    """Every fully qualified declaration name the sources introduce."""
    names = set()
    for path in lean_sources():
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


def audited_names():
    out = []
    for relative in AUDIT_FILES:
        path = os.path.join(ROOT, relative)
        if not os.path.exists(path):
            continue
        for number, line in enumerate(io.open(path, encoding='utf-8'), 1):
            m = PRINT.match(line)
            if m:
                out.append((relative, number, m.group(1)))
    return out


def main():
    declared = declarations()
    by_base = {}
    for name in declared:
        by_base.setdefault(name.rsplit('.', 1)[-1], []).append(name)

    audited = audited_names()
    missing = []
    for relative, number, name in audited:
        if name in declared:
            continue
        # an audit file may name a declaration through a shorter path when the
        # file itself is inside that namespace; accept any declared name whose
        # tail matches the audited one.
        if any(d == name or d.endswith('.' + name) for d in declared):
            continue
        missing.append((relative, number, name))

    sys.stdout.write('declarations found in %s: %d\n'
                     % (', '.join(LEAN_DIRS), len(declared)))
    sys.stdout.write('#print axioms names audited: %d\n' % len(audited))
    if not missing:
        sys.stdout.write('all audited names resolve\n')
        return 0
    sys.stdout.write('UNRESOLVED: %d\n' % len(missing))
    for relative, number, name in missing:
        base = name.rsplit('.', 1)[-1]
        near = by_base.get(base, [])
        sys.stdout.write('  %s:%d %s\n' % (relative, number, name))
        for candidate in near[:3]:
            sys.stdout.write('      same basename: %s\n' % candidate)
    return 1


if __name__ == '__main__':
    raise SystemExit(main())
