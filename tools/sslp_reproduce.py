#!/usr/bin/env python3
"""Prepare, diagnose and rerun a trusted SSLP ZIP in a fresh directory.

This standalone standard-library launcher does not certify anything itself.
It executes the bundled verifier and reports its fresh input-bound evidence.
"""
import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
import zipfile


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as handle:
        while chunk := handle.read(1024 * 1024):
            value.update(chunk)
    return value.hexdigest()


def read_json_bytes(raw):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def safe_member(name):
    if not isinstance(name, str) or len(name) > 240 or not re.fullmatch(r'[A-Za-z0-9_./-]+', name):
        return False
    parts = name.split('/')
    return all(p not in ('', '.', '..') and not p.endswith('.') and
               not re.fullmatch(r'(?i)(con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\..*)?', p)
               for p in parts)


def prepare(archive_path, destination, expected_sha):
    """Validate everything before creating files; never execute ZIP contents here."""
    archive_path, destination = Path(archive_path).resolve(), Path(destination).resolve()
    if not re.fullmatch(r'[0-9a-f]{64}', expected_sha) or digest(archive_path) != expected_sha:
        raise ValueError('ZIP SHA-256 differs from the expected publisher value')
    if destination.exists():
        raise ValueError('destination must be a new directory')
    with zipfile.ZipFile(archive_path) as archive:
        entries = archive.infolist()
        names = [e.filename for e in entries]
        if len(names) > 4096 or len(set(n.casefold() for n in names)) != len(names):
            raise ValueError('too many or duplicate/case-colliding ZIP members')
        if sum(e.file_size for e in entries) > 64 * 1024 * 1024:
            raise ValueError('uncompressed bundle exceeds 64 MiB')
        for entry in entries:
            mode = entry.external_attr >> 16
            if not safe_member(entry.filename) or (stat.S_IFMT(mode) not in (0, stat.S_IFREG)) or entry.flag_bits & 1:
                raise ValueError('unsafe ZIP member: ' + entry.filename)
        manifest = read_json_bytes(archive.read('bundle-manifest.json'))
        declared = manifest.get('files_sha256')
        if manifest.get('schema') != 'sslp.bundle.v1' or not isinstance(declared, dict):
            raise ValueError('unsupported bundle manifest')
        required = {'case.json', 'exact.json', 'evidence.json', 'lean-toolchain', 'lakefile.lean',
                    'lake-manifest.json', 'requirements.txt', 'tools/sslp_explorer.py'}
        if not required <= declared.keys() or set(names) != set(declared) | {'bundle-manifest.json'}:
            raise ValueError('missing or unlisted bundle files')
        contents = {name: archive.read(name) for name in names}
        for name, expected in declared.items():
            if not isinstance(expected, str) or hashlib.sha256(contents[name]).hexdigest() != expected:
                raise ValueError('bundle member hash mismatch: ' + name)
    destination.mkdir(parents=True)
    for name, payload in contents.items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as handle:
            handle.write(payload)
    write_json(destination / 'reproduction-origin.json', {
        'schema': 'sslp.reproduction-origin.v1', 'zip_sha256': expected_sha,
        'input_sha256': manifest['input_sha256'], 'prepared_at': time.time(),
        'existing_local_build_cache': False,
        'scope': 'hash-checked extraction only; no new mathematical verification'})
    return {'prepared': str(destination), 'zip_sha256': expected_sha, 'files': len(contents)}


def clean_env():
    environment = dict(os.environ)
    for name in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN',
                 'PYTHONPATH', 'PYTHONHOME', 'GIT_DIR', 'GIT_WORK_TREE'):
        environment.pop(name, None)
    environment.update(PYTHONIOENCODING='utf-8', GIT_TERMINAL_PROMPT='0', MATHLIB_NO_CACHE_ON_UPDATE='1')
    return environment


def command(args, cwd, log, timeout=1800):
    """Run a known argument array; timeout terminates only this command's tree."""
    print('Running:', Path(args[0]).name, ' '.join(args[1:3]), flush=True)
    with Path(log).open('wb') as handle:
        process = subprocess.Popen(args, cwd=cwd, env=clean_env(), stdout=handle, stderr=subprocess.STDOUT,
                                   start_new_session=os.name != 'nt',
                                   creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)
        try:
            code = process.wait(timeout=timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt):
            if os.name == 'nt':
                subprocess.run(['taskkill', '/PID', str(process.pid), '/T', '/F'],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            else:
                os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise
    if code:
        raise ValueError(f'command failed (exit {code}); see {log}')


def package_pins(directory):
    manifest = read_json_bytes((directory / 'lake-manifest.json').read_bytes())
    if manifest.get('packagesDir') != '.lake/packages' or not isinstance(manifest.get('packages'), list):
        raise ValueError('unsupported package layout')
    names = set()
    for package in manifest['packages']:
        name = package.get('name', '')
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name) or name.casefold() in names:
            raise ValueError('invalid or duplicate package name')
        names.add(name.casefold())
        if (package.get('type') != 'git' or package.get('subDir') is not None or
            not re.fullmatch(r'[0-9a-f]{40}', package.get('rev', '')) or
            not re.fullmatch(r'https://github\.com/[A-Za-z0-9_-]+/[A-Za-z0-9_.-]+', package.get('url', ''))):
            raise ValueError('only pinned HTTPS GitHub dependencies are supported')
    return manifest['packages']


def fetch_dependencies(directory):
    directory = Path(directory).resolve()
    pins = package_pins(directory)
    logs = directory / 'setup-logs'
    logs.mkdir(exist_ok=True)
    manifest_hash = digest(directory / 'lake-manifest.json')
    packages = directory / '.lake/packages'
    packages.mkdir(parents=True, exist_ok=True)
    for package in pins:
        destination = packages / package['name']
        if destination.exists():
            # Resume a completed exact checkout; never reset or clean an existing tree.
            actual = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=destination, env=clean_env(), capture_output=True, text=True)
            dirty = subprocess.run(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=destination, env=clean_env(), capture_output=True, text=True)
            if actual.returncode or actual.stdout.strip() != package['rev'] or dirty.returncode or dirty.stdout.strip():
                raise ValueError('existing dependency is not the clean pin: ' + package['name'])
        else:
            destination.mkdir()
            command(['git', 'init', '--quiet'], destination, logs / (package['name'] + '-init.log'))
            command(['git', '-c', 'core.autocrlf=false', 'fetch', '--depth=1', package['url'], package['rev']],
                    destination, logs / (package['name'] + '-fetch.log'))
            command(['git', '-c', 'core.autocrlf=false', 'checkout', '--detach', package['rev']],
                    destination, logs / (package['name'] + '-checkout.log'))
            # Lake uses origin to validate package identity; fetch alone does not set it.
            command(['git', 'remote', 'add', 'origin', package['url']], destination, logs / (package['name'] + '-origin.log'))
        # ProofWidgets' cloud release needs its tag, absent in a commit-only
        # shallow fetch. Fetch only the manifest's version tag and bind it to
        # the exact revision; never update to a moving branch or newer release.
        tag = package.get('inputRev')
        if isinstance(tag, str) and re.fullmatch(r'v[0-9][A-Za-z0-9_.-]*', tag):
            reference = 'refs/tags/' + tag
            lookup = ['git', 'rev-parse', '--verify', reference + '^{commit}']
            actual = subprocess.run(lookup, cwd=destination, env=clean_env(), capture_output=True, text=True, timeout=20)
            if actual.returncode or actual.stdout.strip() != package['rev']:
                command(['git', 'fetch', '--depth=1', '--no-tags', package['url'], reference+':'+reference],
                        destination, logs / (package['name'] + '-tag.log'))
                actual = subprocess.run(lookup, cwd=destination, env=clean_env(), capture_output=True, text=True, timeout=20)
                if actual.returncode or actual.stdout.strip() != package['rev']:
                    raise ValueError('release tag does not match pinned commit: ' + package['name'])
    command(['lake', 'exe', 'cache', 'get'], directory, logs / 'mathlib-cache.log')
    if digest(directory / 'lake-manifest.json') != manifest_hash:
        raise ValueError('dependency setup changed the pinned manifest')
    result = {'schema': 'sslp.dependency-setup.v1', 'packages': pins,
              'manifest_sha256': manifest_hash, 'cache': 'mathlib publisher cache; not a source rebuild of mathlib',
              'platform': platform.platform(), 'finished_at': time.time()}
    write_json(directory / 'dependency-setup.json', result)
    return result


def doctor(directory):
    """Bounded diagnostics. Does not install, modify pins or run a proof."""
    directory = Path(directory).resolve()
    checks = []
    def add(name, okay, detail, fix):
        checks.append({'check': name, 'okay': bool(okay), 'detail': detail, 'remedy': None if okay else fix})
    add('python', sys.version_info >= (3, 10), platform.python_version(), 'Use Python 3.10 or later.')
    for name, expected in [('sympy', '1.14.0'), ('mpmath', '1.3.0')]:
        try:
            actual = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            actual = None
        add(name, actual == expected, actual, f'Install {name}=={expected} in the selected Python environment.')
    for executable in ('git', 'lake', 'elan'):
        add(executable, shutil.which(executable), shutil.which(executable), 'Install Git and elan, then put their executables on PATH.')
    pin = (directory / 'lean-toolchain').read_text().strip()
    if shutil.which('elan'):
        result = subprocess.run(['elan', 'which', 'lean'], cwd=directory, env=clean_env(), capture_output=True,
                                text=True, timeout=20)
        add('installed_pinned_lean', result.returncode == 0, result.stdout.strip(), 'Run elan toolchain install ' + pin)
        if result.returncode == 0:
            version = subprocess.run([result.stdout.strip(), '--version'], cwd=directory, env=clean_env(),
                                     capture_output=True, text=True, timeout=20)
            expected = pin.rsplit(':', 1)[-1].removeprefix('v')
            add('lean_version', version.returncode == 0 and ('version ' + expected + ',') in version.stdout,
                version.stdout.strip(), 'Remove a conflicting elan directory override or select the pinned toolchain.')
    else:
        add('installed_pinned_lean', False, pin, 'Install elan and the pinned Lean toolchain.')
    packages = directory / '.lake/packages'
    for package in package_pins(directory):
        path = packages / package['name']
        okay, revision = False, None
        if path.is_dir() and shutil.which('git'):
            head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=path, env=clean_env(), capture_output=True, text=True, timeout=20)
            dirty = subprocess.run(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=path, env=clean_env(), capture_output=True, text=True, timeout=20)
            revision = head.stdout.strip()
            okay = head.returncode == 0 and revision == package['rev'] and dirty.returncode == 0 and not dirty.stdout.strip()
        add('dependency:' + package['name'], okay, revision, 'Run fetch in the prepared directory; inspect existing changed checkouts manually.')
    add('mathlib_artifacts', (packages / 'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file(),
        'presence check only; verifier hashes actual artifacts', 'Run lake exe cache get in the prepared directory.')
    lock = directory / '.lake/build/certification/build.lock'
    add('build_lock', not lock.exists(), 'present' if lock.exists() else 'absent',
        'Inspect the recorded PID; wait for its verifier or confirm the owner has stopped before removing a stale lock.')
    return {'schema': 'sslp.reproduction-doctor.v1', 'ready': all(c['okay'] for c in checks),
            'platform': platform.platform(), 'python_executable': sys.executable, 'toolchain': pin,
            'checks': checks, 'note': 'Readiness only, not kernel certification or proof of artifact integrity.'}


def run_verifier(directory, output, timeout=1800):
    directory = Path(directory).resolve()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', output):
        raise ValueError('output must be a simple new directory name')
    destination = directory / output
    if destination.exists():
        raise ValueError('verification output already exists')
    health = doctor(directory)
    write_json(directory / 'reproduction-doctor.json', health)
    if not health['ready']:
        raise ValueError('environment is not ready; see reproduction-doctor.json')
    initial = {'local_artifacts': len(list((directory / '.lake/build/lib/lean').rglob('*.olean'))),
               'local_stamps': len(list((directory / '.lake/build/certification/stamps').rglob('*.json')))}
    command([sys.executable, '-E', '-s', 'tools/sslp_explorer.py', 'check-bundle', '.'], directory,
            directory / (output + '-integrity.log'), timeout=60)
    start = time.monotonic()
    command([sys.executable, '-E', '-s', 'tools/sslp_explorer.py', 'verify', 'case.json', '--lean', '--output', output],
            directory, directory / (output + '-execution.log'), timeout=timeout)
    evidence = read_json_bytes((destination / 'evidence.json').read_bytes())
    if not evidence.get('passed_requested_checks') or evidence['kernel']['status'] != 'passed':
        raise ValueError('fresh verification did not pass')
    report = {'schema': 'sslp.reproduction-run.v1', 'status': 'passed',
              'environment': health, 'initial_local_cache': initial, 'seconds': round(time.monotonic() - start, 3),
              'launcher_sha256': digest(Path(__file__)),
              'extraction': read_json_bytes((directory / 'reproduction-origin.json').read_bytes()) if (directory / 'reproduction-origin.json').is_file() else None,
              'evidence_sha256': digest(destination / 'evidence.json'), 'input_sha256': evidence['input_sha256'],
              'kernel': evidence['kernel'], 'full_manuscript_certified': False,
              'independent_machine': 'not established by this command; document host provenance separately'}
    write_json(directory / (output + '-reproduction.json'), report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    prepare_parser = sub.add_parser('prepare', help='Hash-check a trusted ZIP and extract into a new directory')
    prepare_parser.add_argument('archive', type=Path)
    prepare_parser.add_argument('--directory', type=Path, required=True)
    prepare_parser.add_argument('--sha256', required=True)
    for action in ('fetch', 'doctor', 'run'):
        p = sub.add_parser(action)
        p.add_argument('directory', type=Path)
        if action == 'run':
            p.add_argument('--output', default='fresh-run')
            p.add_argument('--timeout', type=int, default=1800)
    args = parser.parse_args()
    try:
        if args.action == 'prepare':
            result = prepare(args.archive, args.directory, args.sha256)
        elif args.action == 'fetch':
            result = fetch_dependencies(args.directory)
        elif args.action == 'doctor':
            result = doctor(args.directory)
        else:
            if not 1 <= args.timeout <= 14400:
                raise ValueError('timeout must be between 1 and 14400 seconds')
            result = run_verifier(args.directory, args.output, args.timeout)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 1 if args.action == 'doctor' and not result['ready'] else 0
    except (OSError, ValueError, KeyError, zipfile.BadZipFile, subprocess.TimeoutExpired) as exc:
        print('Reproduction failed: ' + str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    raise SystemExit(main())
