#!/usr/bin/env python3
"""Check that every Lean identifier the documentation of record names exists.

Documentation drift is invisible to the build: a document can cite a theorem
that was renamed, moved, or never existed, and `lake build` will not notice.

The names come from two places, and both are required.  The README supplies
whatever it cites in backticks; the claims ledger supplies the declarations its
reviewed claims rest on.  Taking the union matters: when the README was
rewritten from 665 lines to 135, its citation count fell from 159 names to a
single one belonging to Lean core, and this check passed unconditionally while
appearing green.  A check whose input set can silently empty is worse than no
check, so `main` now fails when the ledger contributes nothing.

Usage:  python tools/check-readme-names.py
It writes a scratch Lean file of `#check`s and runs it; a nonzero exit means
the documentation cites something that is not there.
"""
import io
import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
import tempfile
from lean_source import imports

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SKIP_SUFFIX = ('.lean', '.tex', '.py', '.sh', '.json', '.txt', '.md', '.tsv')
SKIP_PREFIX = ('six:', 'thm:', 'eq:', 'lem:', 'cor:', 'def:', 'sec:', 'tab:')


def live_entry_imports(root=ROOT):
    """Read import-only entry points from source, so stale umbrella oleans cannot hide new proofs."""
    sys.path.insert(0, str(Path(__file__).resolve().parent / 'verification'))
    from check_audit_names import AUDIT_FILES
    entries = tuple(dict.fromkeys(('MainTheory.lean',) + AUDIT_FILES))
    wrappers = {name[:-5].replace('/', '.') for name in entries}
    modules = {module for relative in entries
               for module in imports((Path(root) / relative).read_text(encoding='utf-8'))}
    return sorted(modules - wrappers)


def candidates(readme: str):
    names = set()
    for m in re.finditer(r'`([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+)`',
                         readme):
        n = m.group(1)
        if n.endswith(SKIP_SUFFIX) or n.startswith(SKIP_PREFIX):
            continue
        names.add(n)
    return sorted(names)


def owning_modules(root=ROOT):
    """Fully qualified declaration name -> the module that declares it.

    Same source scan as tools/verification/check_audit_names.py, which this
    reuses rather than reimplements, but keeping the file it came from.
    """
    sys.path.insert(0, os.path.join(root, 'tools', 'verification'))
    import check_audit_names as audit
    owner = {}
    for path in audit.lean_sources():
        module = os.path.relpath(path, root).replace(os.sep, '/')[:-5].replace('/', '.')
        stack, structure = [], None
        for line in io.open(path, encoding='utf-8', errors='replace'):
            m = audit.NAMESPACE.match(line)
            if m:
                stack.append(m.group(1)); structure = None; continue
            m = audit.END.match(line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop(); structure = None; continue
            m = audit.DECL.match(line)
            if m:
                prefix = '.'.join(stack)
                full = prefix + '.' + m.group(1) if prefix else m.group(1)
                owner.setdefault(full, module)
                structure = full if audit.STRUCTURE.match(line) else None
                continue
            if structure is not None:
                if line.strip() and not line.startswith((' ', '\t')):
                    structure = None; continue
                f = audit.FIELD.match(line)
                if f:
                    owner.setdefault(structure + '.' + f.group(1), module)
    return owner


def diagnose(output, root=ROOT):
    """Say WHY the harness could not see a name.

    An unknown identifier has two very different causes and the raw Lean
    diagnostics do not distinguish them: the declaration may genuinely not
    exist, or it may exist in a module the harness does not import -- and the
    second is repaired by an import line, not by mathematics.  A third cause
    is a stale olean, since `lake env lean` never rebuilds; when the harness
    can see almost nothing at all, that is what it usually means.
    """
    unknown = re.findall(r'Unknown identifier `([^`]+)`', output)
    if not unknown:
        return ''
    owner = owning_modules(root)
    by_module, absent = {}, []
    for name in sorted(set(unknown)):
        module = owner.get(name)
        if module is None:
            absent.append(name)
        else:
            by_module.setdefault(module, []).append(name)
    report = ['', '%d unknown identifier(s); by cause:' % len(set(unknown))]
    if by_module:
        report.append('')
        report.append('  DECLARED IN SOURCE BUT OUTSIDE THE HARNESS CLOSURE '
                      '(%d names in %d modules).' % (sum(len(v) for v in by_module.values()),
                                                     len(by_module)))
        report.append('  The harness reads the current entry-point imports from source.')
        report.append('  Check that these modules belong to that closure and that their')
        report.append('  dependency oleans were content-validated: `lake env lean` does not rebuild.')
        for module in sorted(by_module):
            report.append('    %-52s %d' % (module, len(by_module[module])))
    if absent:
        report.append('')
        report.append('  NOT DECLARED ANYWHERE IN THE SOURCES (%d). These are real drift:'
                      % len(absent))
        for name in absent[:40]:
            report.append('    %s' % name)
        if len(absent) > 40:
            report.append('    ... and %d more' % (len(absent) - 40))
    return '\n'.join(report) + '\n'


def check_names(names, runner=subprocess.run, root=ROOT, paper_version=None) -> int:
    """Fail on every Lean failure, including errors unrelated to name lookup."""
    work = Path(root) / 'tmp' / 'verification'
    if paper_version:
        work = work / paper_version
    module_imports = live_entry_imports(root)
    work.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='readme-',
                                     dir=work, encoding='utf-8', newline='\n',
                                     delete=False) as handle:
        scratch = Path(handle.name)
        handle.write(''.join('import %s\n' % module for module in module_imports))
        # The default cap of 100 truncates the diagnosis of a systematic
        # failure -- a stale root olean, or a batch of names in one unimported
        # module -- into an arbitrary alphabetical prefix of it.
        handle.write('set_option maxErrors 100000\n')
        handle.write('open MainTheory SixQubit\n')
        for name in names:
            handle.write('#check @%s\n' % name)
    try:
        proc = runner(['lake', 'env', 'lean', '-j', '1', '-DwarningAsError=true', str(scratch)],
                      cwd=root, capture_output=True, text=True,
                      encoding='utf-8', errors='replace')
        output = proc.stdout + proc.stderr
        (work / 'readme-names.log').write_text(output, encoding='utf-8')
        print('checked %d identifiers named in README.md' % len(names))
        if proc.returncode != 0:
            print('FAIL: Lean exited %d; diagnostics in %s' %
                  (proc.returncode, work / 'readme-names.log'))
            # The console codepage here is GBK; Lean's output carries
            # unicode, and printing it raw crashes the reporter before
            # the caller ever sees the failure.
            text = output.rstrip() or '(no diagnostics)'
            try:
                text += chr(10) + diagnose(output, root)
            except Exception as exc:              # a diagnosis must never mask the failure
                text += chr(10) + '(diagnosis unavailable: %s)' % exc
            sys.stdout.write(text.encode(sys.stdout.encoding or 'utf-8',
                                         'replace').decode(sys.stdout.encoding
                                                           or 'utf-8') + chr(10))
            return 1
        print('all present')
        return 0
    finally:
        scratch.unlink(missing_ok=True)


def ledger_declarations(root=ROOT, paper_version=None):
    """Declarations the claims ledger says are covered.  These are the names a
    reader is invited to check, so they are part of the documentation of
    record."""
    import glob
    import json
    names = set()
    if paper_version is not None and not re.fullmatch(r'[0-9]{8}', paper_version):
        raise ValueError('paper version must be an eight-digit date')
    paths = ([os.path.join(root, 'results', f'paper-claims-{paper_version}.json')]
             if paper_version else sorted(glob.glob(os.path.join(root, 'results', 'paper-claims-*.json'))))
    for path in paths:
        with io.open(path, encoding='utf-8') as handle:
            for claim in json.load(handle).get('claims', []):
                if claim.get('status') in ('covered', 'partial'):
                    names.update(claim.get('lean_declarations', []))
    return names


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper-version')
    args = parser.parse_args(argv)
    readme = io.open(os.path.join(ROOT, 'README.md'), encoding='utf-8').read()
    from_readme = set(candidates(readme))
    from_ledger = ledger_declarations(paper_version=args.paper_version)
    if not from_ledger:
        print('FAIL: the claims ledger names no declarations, so this check '
              'would verify only whatever the README happens to cite; refusing '
              'to report a pass on an input set that can silently empty.')
        return 1
    names = sorted(from_readme | from_ledger)
    print('%d identifiers: %d from README.md, %d from the claims ledger'
          % (len(names), len(from_readme), len(from_ledger)))
    return check_names(names, paper_version=args.paper_version)


if __name__ == '__main__':
    sys.exit(main())
