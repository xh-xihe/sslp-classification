#!/usr/bin/env python3
"""Local SSLP case service and portable evidence bundles (first slice: class 36).

Commands: example, verify, bundle, check-bundle. Kernel checking is explicit;
exact Python checks alone never produce kernel certification. No HTTP service,
arbitrary Lean input or manuscript redistribution is enabled by this CLI.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import zipfile

from explorer import class36, research
import build_lean
from lean_source import imports, code_only
from verify import FORBIDDEN

ROOT = Path(__file__).resolve().parent.parent
TARGET = 'SixQubit.Orbit36Code'
TOOL_FILES = ['tools/sslp_explorer.py', 'tools/explorer/__init__.py', 'tools/explorer/class36.py', 'tools/explorer/research.py',
              'tools/generators/gen36code.py', 'tools/core/orbit.py',
              'tools/build_lean.py', 'tools/lean_source.py', 'tools/verify.py']


def read_json(path):
    if path.stat().st_size > 2_000_000:
        raise ValueError('input JSON exceeds 2 MB')
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('duplicate JSON key: ' + key)
            result[key] = value
        return result
    value = json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique,
                       parse_constant=lambda x: (_ for _ in ()).throw(ValueError('non-finite JSON number')))
    if not isinstance(value, dict):
        raise ValueError('JSON object required')
    return value


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + '\n', encoding='utf-8')


def case_adapter(data):
    return research if isinstance(data, dict) and data.get('schema') == research.SCHEMA else class36


def local_closure(root=ROOT, target=TARGET):
    """Read only reachable modules; avoid scanning the entire classification library."""
    sources, graph, external, active = {}, {}, set(), set()
    def visit(name):
        if name in active:
            raise ValueError('cyclic local imports: ' + name)
        if name in sources:
            return
        path = root / (name.replace('.', '/') + '.lean')
        if not path.is_file():
            raise ValueError('missing local source: ' + name)
        active.add(name)
        dependencies = imports(path.read_text(encoding='utf-8'))
        local = [x for x in dependencies if x.split('.')[0] in build_lean.LIVE_DIRS]
        for dependency in local:
            visit(dependency)
        graph[name] = local
        external.update(x for x in dependencies if x not in local)
        sources[name] = path
        active.remove(name)
    visit(target)
    return sources, graph, external


def kernel_check(data, output, timeout=180):
    """Validate imported artifacts, check a new input-bound proof, audit its axioms."""
    adapter = case_adapter(data)
    sources, graph, external = local_closure(target=getattr(adapter, 'TARGET', TARGET))
    source_hashes = {name: build_lean.file_hash(path) for name, path in sources.items()}
    for path in sources.values():
        if FORBIDDEN.search(code_only(path.read_text(encoding='utf-8'))):
            raise ValueError('forbidden proof path in ' + str(path))
    certificate = output / 'Certificate.lean'
    certificate.write_text(adapter.lean_certificate(data), encoding='utf-8')
    start = time.monotonic()
    with build_lean.build_lock(ROOT):
        print('Validating pinned dependency artifacts...', flush=True)
        context, configuration, artifacts = build_lean.external_context(ROOT, required_imports=external)
        keys, expected, reused, rebuilt = {}, {}, 0, 0
        for name, path in sources.items():
            expected[name] = build_lean.fingerprint(source_hashes[name], {x: keys[x] for x in graph[name]}, context)
            record = build_lean.valid_cache(ROOT, name, expected[name])
            if record is None:
                print('Building ' + name, flush=True)
                record = build_lean.compile_module(ROOT, name, path, source_hashes[name], expected[name])
                rebuilt += 1
            else:
                reused += 1
            keys[name] = record['key']
        print('Checking supplied amplitudes and proof obligations in Lean...', flush=True)
        command = ['lake', 'env', 'lean', '-j', '1', '-DwarningAsError=true', str(certificate)]
        try:
            process = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                     encoding='utf-8', errors='replace', timeout=timeout)
            log = process.stdout + process.stderr
            exit_code = process.returncode
        except subprocess.TimeoutExpired:
            log = 'Lean certificate timed out; no mathematical conclusion.\n'
            exit_code = None
        (output / 'lean.log').write_text(log, encoding='utf-8')
        roots = getattr(adapter, 'ROOT_COUNT', 7)
        match = re.fullmatch(r'\s*SSLP_CASE_KERNEL_OK roots=' + str(roots) + r' axioms=\[([^\]]*)\]\s*', log)
        axioms = {x.strip() for x in match[1].split(',') if x.strip()} if match else None
        valid = exit_code == 0 and axioms is not None and axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
        for name, path in sources.items():
            if source_hashes[name] != build_lean.file_hash(path) or not build_lean.valid_cache(ROOT, name, expected[name]):
                raise ValueError('source or compiled artifact changed during verification: ' + name)
        end_context, _, _ = build_lean.external_context(ROOT, required_imports=external)
        if context != end_context:
            raise ValueError('external dependencies changed during verification')
    return {'status': 'passed' if valid else ('timeout' if exit_code is None else 'failed'),
            'scope': getattr(adapter, 'SCOPE', 'supplied amplitudes equal canonical pair; normalization, orthogonality, '
                     'distance at least 3, physical phase layer on every logical superposition '
                     '(gate theorem assumes zeta^5=1)'),
            'not_certified': ['gate-level encoder', 'classification exhaustiveness', 'full manuscript',
                              'minimal physical or logical gate order'],
            'input_sha256': class36.digest(data), 'certificate_sha256': build_lean.file_hash(certificate),
            'axioms': sorted(axioms) if axioms is not None else None, 'exit_code': exit_code,
            'seconds': round(time.monotonic() - start, 3), 'dependency_context_sha256': context,
            'dependency_modules': keys, 'source_sha256': source_hashes,
            'configuration_sha256': configuration, 'rebuilt': rebuilt, 'content_validated_reused': reused}


def verify_case(data, output, lean=False, timeout=180):
    adapter = case_adapter(data)
    adapter.validate(data)
    if output.exists() and any(output.iterdir()):
        raise ValueError('use a new or empty output directory to avoid mixing evidence runs')
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / 'case.json', data)
    result = adapter.exact_checks(data)
    write_json(output / 'exact.json', result)
    tooling = {p: build_lean.file_hash(ROOT / p) for p in TOOL_FILES}
    evidence = {'schema': 'sslp.evidence.v1', 'scope': 'single_instance',
                'input_sha256': class36.digest(data), 'exact_passed': result['passed'],
                'exact_report_sha256': build_lean.file_hash(output / 'exact.json'),
                'tooling_sha256': tooling, 'python_version': sys.version,
                'manuscript_correspondence': 'requires separate semantic review; source hashes are provenance only',
                'kernel': {'status': 'not_run'}, 'full_manuscript_certified': False}
    if lean:
        # Even a damaged input can reach Lean, allowing independent rejection.
        try:
            evidence['kernel'] = kernel_check(data, output, timeout)
        except (OSError, ValueError, build_lean.BuildError) as exc:
            evidence['kernel'] = {'status': 'failed', 'error': str(exc)}
    evidence['passed_requested_checks'] = result['passed'] and (not lean or evidence['kernel']['status'] == 'passed')
    if any(build_lean.file_hash(ROOT / p) != digest for p, digest in tooling.items()):
        evidence['passed_requested_checks'] = False
        evidence['kernel'] = {'status': 'failed', 'error': 'verification tools changed during execution'}
    write_json(output / 'evidence.json', evidence)
    return evidence


def check_bundle(directory):
    manifest = read_json(directory / 'bundle-manifest.json')
    if manifest.get('schema') != 'sslp.bundle.v1':
        raise ValueError('unsupported bundle manifest')
    required = {'case.json', 'exact.json', 'evidence.json', 'lakefile.lean',
                'lean-toolchain', 'lake-manifest.json', 'requirements.txt', 'README.md', *TOOL_FILES}
    data = read_json(directory / 'case.json')
    adapter = case_adapter(data)
    adapter.validate(data)
    sources, _, _ = local_closure(directory, getattr(adapter, 'TARGET', TARGET))
    required.update(p.relative_to(directory).as_posix() for p in sources.values())
    if not required <= manifest['files_sha256'].keys():
        raise ValueError('required bundle files are absent from the hash manifest')
    for relative, expected in manifest['files_sha256'].items():
        path = (directory / relative).resolve()
        if not path.is_relative_to(directory.resolve()) or not path.is_file():
            raise ValueError('missing or out-of-bundle file: ' + relative)
        if build_lean.file_hash(path) != expected:
            raise ValueError('bundle hash mismatch: ' + relative)
    if class36.digest(data) != manifest['input_sha256']:
        raise ValueError('bundle input mismatch')
    evidence = read_json(directory / 'evidence.json')
    if evidence['input_sha256'] != manifest['input_sha256']:
        raise ValueError('evidence/input mismatch')
    if evidence['exact_report_sha256'] != build_lean.file_hash(directory / 'exact.json'):
        raise ValueError('exact report/evidence mismatch')
    for relative, expected in evidence['tooling_sha256'].items():
        if manifest['files_sha256'].get(relative) != expected:
            raise ValueError('tooling/evidence mismatch: ' + relative)
    if evidence['kernel']['status'] == 'passed':
        if not {'Certificate.lean', 'lean.log'} <= manifest['files_sha256'].keys():
            raise ValueError('kernel run files missing from manifest')
        if evidence['kernel']['input_sha256'] != manifest['input_sha256']:
            raise ValueError('kernel/input mismatch')
        if evidence['kernel']['certificate_sha256'] != build_lean.file_hash(directory / 'Certificate.lean'):
            raise ValueError('certificate/evidence mismatch')
        expected_source = adapter.lean_certificate(data)
        if (directory / 'Certificate.lean').read_text(encoding='utf-8') != expected_source:
            raise ValueError('certificate is not generated from the bundled input')
        for name, expected in evidence['kernel']['source_sha256'].items():
            if manifest['files_sha256'].get(name.replace('.', '/') + '.lean') != expected:
                raise ValueError('proof source/evidence mismatch: ' + name)
        for name in ('lakefile.lean', 'lean-toolchain', 'lake-manifest.json'):
            if manifest['files_sha256'][name] != evidence['kernel']['configuration_sha256'][name]:
                raise ValueError('configuration/evidence mismatch: ' + name)
    return {'hashes_match': True, 'file_count': len(manifest['files_sha256']),
            'note': 'Integrity check only, not a new Lean execution or publisher authentication.'}


def export_bundle(run_dir, output):
    evidence = read_json(run_dir / 'evidence.json')
    if not evidence.get('passed_requested_checks'):
        raise ValueError('cannot export failed run as a successful example bundle')
    if output.exists() or output.with_suffix('.zip').exists():
        raise ValueError('bundle destination already exists')
    data = read_json(run_dir / 'case.json')
    if class36.digest(data) != evidence['input_sha256']:
        raise ValueError('run input was changed after verification')
    if build_lean.file_hash(run_dir / 'exact.json') != evidence['exact_report_sha256']:
        raise ValueError('exact report was changed after verification')
    for relative, expected in evidence['tooling_sha256'].items():
        if build_lean.file_hash(ROOT / relative) != expected:
            raise ValueError('tools changed after verification: ' + relative)
    adapter = case_adapter(data)
    adapter.validate(data)
    sources, _, _ = local_closure(target=getattr(adapter, 'TARGET', TARGET))
    # Bind copied proof sources to the checked input closure, not just the current file names.
    if evidence['kernel']['status'] == 'passed':
        for name, path in sources.items():
            if evidence['kernel']['source_sha256'].get(name) != build_lean.file_hash(path):
                raise ValueError('proof sources changed since run: ' + name)
    output.mkdir(parents=True)
    relative_files = [p.relative_to(ROOT).as_posix() for p in sources.values()]
    relative_files += ['lakefile.lean', 'lean-toolchain', 'lake-manifest.json', *TOOL_FILES]
    for relative in relative_files:
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    for name in ('case.json', 'exact.json', 'evidence.json', 'Certificate.lean', 'lean.log'):
        if (run_dir / name).is_file():
            shutil.copyfile(run_dir / name, output / name)
    (output / 'requirements.txt').write_text('sympy==1.14.0\n', encoding='utf-8')
    (output / 'README.md').write_text('''# SSLP input-bound local verification bundle

This bundle covers one concrete code instance. It does not certify the entire
manuscript, classification, or a gate-level encoder. Private manuscript text
is omitted; the input records source hashes and formula locators.

Install Python >= 3.10, the pinned Lean toolchain via elan, and the Python
dependency (`python -m pip install -r requirements.txt`). Fetch the exact
dependencies from lake-manifest.json; `lake exe cache get` can obtain the
mathlib artifacts. The checker verifies clean dependency revisions and hashes
the installed artifacts. It builds missing local modules serially.

From this directory run:

```text
python tools/sslp_explorer.py check-bundle .
python tools/sslp_explorer.py verify case.json --lean --output fresh-run
```

The first command checks integrity only. The second executes the exact
checks and a fresh input-bound Lean certificate, and audits its transitive
axioms. Review fresh-run/evidence.json and fresh-run/lean.log. Dependency
artifacts can be reused only after content validation. The timeout option
limits the final certificate invocation, not dependency preparation/builds.

Encoding is represented as an abstract isometry. The displayed transversal
phase layer is a symbolic circuit description. Status fields state the exact
scope of the checked gate action. The original run log is historical evidence;
it is not a fresh check on your machine. A changed manifest is not authenticated
by its own hashes; obtain the bundle from the intended publisher.
''', encoding='utf-8')
    files = {p.relative_to(output).as_posix(): build_lean.file_hash(p)
             for p in sorted(output.rglob('*')) if p.is_file()}
    write_json(output / 'bundle-manifest.json', {'schema': 'sslp.bundle.v1',
               'scope': 'single_instance', 'input_sha256': class36.digest(data), 'files_sha256': files})
    check_bundle(output)
    with zipfile.ZipFile(output.with_suffix('.zip'), 'w', zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(output.rglob('*')):
            if path.is_file():
                archive.write(path, path.relative_to(output).as_posix())
    return output.with_suffix('.zip')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    sample = sub.add_parser('example')
    sample.add_argument('--output', type=Path, required=True)
    verify = sub.add_parser('verify')
    verify.add_argument('input', type=Path)
    verify.add_argument('--lean', action='store_true')
    verify.add_argument('--timeout', type=int, default=180)
    verify.add_argument('--output', type=Path, required=True)
    bundle = sub.add_parser('bundle')
    bundle.add_argument('run', type=Path)
    bundle.add_argument('--output', type=Path, required=True)
    integrity = sub.add_parser('check-bundle')
    integrity.add_argument('directory', type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'example':
            if args.output.exists():
                raise ValueError('example destination already exists')
            write_json(args.output, class36.example())
            print(args.output)
        elif args.command == 'verify':
            if args.timeout <= 0:
                raise ValueError('timeout must be positive')
            result = verify_case(read_json(args.input), args.output.resolve(), args.lean, args.timeout)
            print(json.dumps(result, ensure_ascii=False))
            return 0 if result['passed_requested_checks'] else 1
        elif args.command == 'bundle':
            print(export_bundle(args.run.resolve(), args.output.resolve()))
        else:
            print(json.dumps(check_bundle(args.directory.resolve())))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    raise SystemExit(main())
