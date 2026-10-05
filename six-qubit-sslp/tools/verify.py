#!/usr/bin/env python3
"""Resource-bounded certification acceptance gate.

Default: serial content-validated build, shared-state Lean core axiom audit,
source sweep, generated SHA/coverage checks, current manuscript correspondence,
semantic no-go/moment gates and mutation tests, and README-name verification.
Use --only for explicitly partial diagnostics; it never implies a full release
verification. Full logs and a machine-readable run report remain under tmp/.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

from lean_source import code_only, imports
from lean_audit import audit_names
DEFAULT_PAPER_VERSION = '20260908'

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_DIRS = ('MainTheory', 'SS', 'SixQubit', 'QECC', 'Orbit2')
AUDIT_FILES = ('MainTheory/Audit.lean', 'SixQubit/Audit.lean',
               'SixQubit/CodeWrapAudit.lean',
               'SixQubit/Orbit7CollinearAxiomCheck.lean',
               'MainTheory/ProseCitationAudit.lean', 'QECC/Audit.lean',
               'MainTheory/OrbitCertificationAudit.lean',
               'MainTheory/OrbitCertificationFinalAudit.lean',
               'MainTheory/ReviewedDeclarationsAudit.lean',
               'MainTheory/ManuscriptCertificationAudit20261005.lean', 'Orbit2.lean')
REPORT_DIR = ROOT / 'tmp' / 'verification'
FORBIDDEN = re.compile(
    r'(?<![\w])(?:sorry|admit|sorryAx|axiom|native_decide|ofReduceBool|ofReduceNat|'
    r'implemented_by|unsafe|extern|trustLevel|skipKernelTC|mkSorry|mkAxiom|axiomDecl)(?![\w])')
AXIOM_SUCCESS = re.compile(r'CERTIFICATION_AXIOMS_OK roots=(\d+) axioms=\[([^\]]*)\]')


def run(cmd, **kwargs):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True,
                          encoding='utf-8', errors='replace', **kwargs)


def recorded_command(name, command):
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    proc = run(command)
    output = proc.stdout + proc.stderr
    path = REPORT_DIR / (name + '.log')
    path.write_text(output, encoding='utf-8')
    detail = 'exit=%d; log=%s' % (proc.returncode, path.relative_to(ROOT))
    if output.strip():
        detail += '; ' + (output.strip().splitlines()[-1] if proc.returncode == 0
                          else output.strip()[-2500:])
    return proc.returncode == 0, detail


def check_build():
    # This driver runs one Lean process at a time; it never calls lake build.
    return recorded_command('build', [sys.executable, 'tools/build_lean.py'])


def axiom_inventory(root=ROOT, paper_version=DEFAULT_PAPER_VERSION):
    import paper_release
    roots, module_imports, source_hashes = [], [], {}
    for relative in AUDIT_FILES:
        data = (Path(root) / relative).read_bytes()
        source = data.decode('utf-8')
        names = audit_names(source)
        if not names:
            raise ValueError('audit file contains no declarations: ' + relative)
        roots.extend(names)
        source_hashes[relative] = hashlib.sha256(data).hexdigest()
        module_imports.extend(imports(source))
    if len(set(roots)) != len(roots):
        raise ValueError('duplicate declarations in the audit inventory')
    ledger = paper_release.paths(paper_version, root)['ledger']
    if ledger.exists():
        data = ledger.read_bytes()
        source_hashes[ledger.relative_to(root).as_posix()] = hashlib.sha256(data).hexdigest()
        for claim in json.loads(data)['claims']:
            if claim['status'] == 'covered':
                for declaration in claim['lean_declarations']:
                    if declaration not in roots:
                        roots.append(declaration)
    else:
        raise ValueError('missing selected release ledger: ' + str(ledger))
    prose = paper_release.paths(paper_version, root)['prose']
    data = prose.read_bytes()
    source_hashes[prose.relative_to(root).as_posix()] = hashlib.sha256(data).hexdigest()
    for row in json.loads(data)['assertions']:
        if row['kind'] == 'covered':
            if not row.get('declarations'):
                raise ValueError('covered prose assertion has no kernel declarations')
            for declaration in row['declarations']:
                if declaration not in roots:
                    roots.append(declaration)
    return roots, sorted(set(module_imports)), source_hashes


ROOT_CHUNK = 200


def render_axiom_harness(roots, module_imports):
    # Use the current audit source imports, not a possibly older Audit.olean.
    header = ''.join('import %s\n' % name for name in module_imports)
    header += 'import Lean.Util.CollectAxioms\n\n'
    # One array literal per couple of hundred roots.  A single literal over the
    # whole inventory overflows the code generator's recursion limit once the
    # ledger grows past a few thousand covered declarations, which is a limit
    # of the harness and not of the proofs; chunking keeps each literal small
    # and the `++` chain shallow.  The raised recursion depth covers the rest.
    header += 'set_option maxRecDepth 100000 in\nrun_cmd do\n'
    chunks = [roots[i:i + ROOT_CHUNK] for i in range(0, len(roots), ROOT_CHUNK)]
    header += '  let roots : Array Lean.Name :=\n'
    rendered = []
    for chunk in chunks:
        rendered.append('    #[' + ', '.join('`' + name for name in chunk) + ']')
    header += ' ++\n'.join(rendered) + '\n'
    return header + '''  let env <- Lean.getEnv
  for root in roots do
    if (env.checked.get.find? root).isNone then
      throwError "Missing kernel declaration: {root}"
  let action : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in state.axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected transitive axiom: {axiomName}"
  Lean.logInfo m!"CERTIFICATION_AXIOMS_OK roots={roots.size} axioms={state.axioms}"
'''


def check_axioms(paper_version=DEFAULT_PAPER_VERSION):
    try:
        roots, module_imports, source_hashes = axiom_inventory(paper_version=paper_version)
    except (OSError, UnicodeError, ValueError) as exc:
        return False, str(exc)
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    harness = REPORT_DIR / 'axiom-union.lean'
    harness.write_text(render_axiom_harness(roots, module_imports), encoding='utf-8')
    proc = run(['lake', 'env', 'lean', '-j', '1', '-DwarningAsError=true', str(harness)])
    output = proc.stdout + proc.stderr
    (REPORT_DIR / 'axioms.log').write_text(output, encoding='utf-8')
    matches = AXIOM_SUCCESS.findall(output)
    footprint = None
    if len(matches) == 1:
        count, axioms = matches[0]
        footprint = {name.strip() for name in axioms.split(',') if name.strip()}
        valid = int(count) == len(roots) and footprint <= ALLOWED
    else:
        valid = False
    ok = proc.returncode == 0 and valid
    (REPORT_DIR / 'axioms.json').write_text(json.dumps({
        'method': 'Lean.CollectAxioms.collect with shared visited state',
        'paper_version': paper_version,
        'audit_sources_sha256': source_hashes, 'roots': roots,
        'axiom_union': sorted(footprint) if footprint is not None else None,
        'exit_code': proc.returncode, 'passed': ok,
    }, indent=2) + '\n', encoding='utf-8')
    if not ok:
        return False, 'axiom audit failed, exit=%d; %s' % (proc.returncode, output[-2500:])
    return True, '%d declarations; union=%s; log=%s' % (
        len(roots), ', '.join(sorted(footprint)), (REPORT_DIR / 'axioms.log').relative_to(ROOT))


def check_sources():
    findings, count = [], 0
    files = [path for directory in LEAN_DIRS for path in (ROOT / directory).rglob('*.lean')]
    files += [ROOT / (directory + '.lean') for directory in LEAN_DIRS]
    for path in sorted(files):
        try:
            source = code_only(path.read_text(encoding='utf-8'))
        except (OSError, UnicodeError, ValueError) as exc:
            return False, '%s: %s' % (path, exc)
        count += 1
        for match in FORBIDDEN.finditer(source):
            findings.append('%s:%d %s' % (path.relative_to(ROOT),
                source.count('\n', 0, match.start()) + 1, match.group()))
    return not findings, ('%d Lean sources clean' % count if not findings else '\n'.join(findings))


def check_names(paper_version=DEFAULT_PAPER_VERSION):
    return recorded_command('readme-names', [sys.executable, 'tools/check-readme-names.py',
                                           '--paper-version', paper_version])


def script_check(name, script, *arguments):
    return recorded_command(name, [sys.executable, 'tools/run.py', script, *arguments])


def check_release(paper_version, source_dir=None):
    import paper_release
    report = paper_release.binding(paper_version, ROOT, source_dir)
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / 'release.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    return True, 'version-bound manuscripts, review records and orbit data; review completeness checked separately'


def checks(source_dir=None, paper_version=DEFAULT_PAPER_VERSION):
    import paper_release
    release = paper_release.paths(paper_version, ROOT)
    common = ['--source-dir', str(source_dir or release['source_dir']),
              '--manifest', str(release['manifest'])]
    version_args = ['--paper-version', paper_version]
    private_args = ['--source-dir', str(source_dir)] if source_dir else []
    return {
        'release': lambda: check_release(paper_version, source_dir),
        'build': check_build,
        'axioms': lambda: check_axioms(paper_version),
        'sources': check_sources,
        'generated': lambda: script_check('generated', 'verification/generated_manifests.py'),
        'paper': lambda: script_check('paper', 'verification/mkmanifest.py', '--check', *common),
        'table-kernel': lambda: script_check('table-kernel',
            'verification/orbit_table_kernel.py', *common,
            '--output-dir', str(REPORT_DIR / 'orbit-table-kernel')),
        'table-kernel-selftest': lambda: script_check('table-kernel-selftest',
            'verification/orbit_table_kernel.py', '--selftest', *common,
            '--output-dir', str(REPORT_DIR / 'orbit-table-kernel')),
        'claims': lambda: recorded_command('claims',
            [sys.executable, 'tools/paper_claims.py', 'check', '--require-complete', *version_args, *private_args]),
        'gate': lambda: script_check('gate', 'verification/gate.py'),
        'gate-selftest': lambda: script_check('gate-selftest', 'verification/gate.py', '--selftest'),
        'moments': lambda: script_check('moments', 'verification/momentgate.py'),
        'moments-selftest': lambda: script_check('moments-selftest', 'verification/momentgate.py', '--selftest'),
        'readme': lambda: check_names(paper_version),
        'audit-names': lambda: recorded_command('audit-names',
            [sys.executable, 'tools/verification/check_audit_names.py', *version_args]),
        # The named-results document is generated from the ledger.  Checking it
        # here is what stops it drifting: a result added to a manuscript, or a
        # declaration swapped in a review, changes the ledger and this fails
        # until the document is regenerated.
        'named-results': lambda: recorded_command('named-results',
            [sys.executable, 'tools/named_results_doc.py', '--check', *version_args, *private_args]),
        # The prose-review document is generated from its own record, and the
        # generator refuses if that record ever carries verbatim manuscript
        # text.  Checking it here keeps both properties from rotting.
        'prose-review': lambda: recorded_command('prose-review',
            [sys.executable, 'tools/prose_review_doc.py', '--check', '--require-complete', *version_args, *private_args]),
        'errata': lambda: paper_release.check_errata(paper_version, ROOT, source_dir),
    }


def main(argv=None):
    import paper_release
    global REPORT_DIR
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', nargs='+', choices=list(checks()),
                        help='run only these explicitly partial diagnostics')
    parser.add_argument('--source-dir', type=Path,
                        help='private directory containing main.tex and supplementary.tex')
    parser.add_argument('--paper-version', default=paper_release.DEFAULT_VERSION,
                        type=paper_release.version, help='manuscript date; historical default 20260908')
    args = parser.parse_args(argv)
    REPORT_DIR = ROOT / 'tmp' / 'verification' / args.paper_version
    selected = checks(args.source_dir, args.paper_version)
    if args.only:
        selected = {name: selected[name] for name in dict.fromkeys(args.only)}
        print('PARTIAL verification: ' + ', '.join(selected), flush=True)
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    print('Paper version: ' + args.paper_version, flush=True)
    outcomes = []
    for name, function in selected.items():
        print('START ' + name, flush=True)
        start = time.monotonic()
        try:
            ok, detail = function()
        except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
            ok, detail = False, str(exc)
        elapsed = time.monotonic() - start
        outcomes.append(dict(check=name, passed=ok, detail=detail, seconds=round(elapsed, 3)))
        print('[%s] %s (%.1fs): %s' % ('PASS' if ok else 'FAIL', name, elapsed, detail), flush=True)
        # Auditing imports after a failed build can report an older cached environment.
        if name in {'release', 'build'} and not ok:
            print('Stopping: release binding or source build failed.', flush=True)
            break
    all_passed = len(outcomes) == len(selected) and all(row['passed'] for row in outcomes)
    report = {'paper_version': args.paper_version, 'full_suite': args.only is None,
              'passed': all_passed, 'checks': outcomes}
    (REPORT_DIR / 'report.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    return 0 if all_passed else 1


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    raise SystemExit(main())
