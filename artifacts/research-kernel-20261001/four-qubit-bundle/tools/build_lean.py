#!/usr/bin/env python3
"""Build the local Lean dependency graph serially with content-based certificates.

No `lake build`, cache deletion, or timestamp-only cache adoption occurs. Each
module compiles with one thread into a staging directory. Its old outputs remain
until successful elaboration; outputs are promoted before a success stamp is
written. A failure is resumable. Existing unrecorded caches are never declared
validated merely because an .olean exists.

`--plan` is read-only and reports topology/initial stamp coverage; it performs no
Lean invocation or expensive external artifact hashing. The first real run must
validate all requested unstamped sources. `--module X` includes X's entire local
import closure; the default includes all three live libraries and root modules.
External packages must already be fetched/built for the pinned toolchain.
"""
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import uuid

from lean_source import imports, MODULE_NAME

ROOT = Path(__file__).resolve().parent.parent
LIVE_DIRS = ('SS', 'SixQubit', 'MainTheory')
SCHEMA = 1
LEAN_FLAGS = ['-j', '1', '-DwarningAsError=true']
OUTPUT_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean')


class BuildError(RuntimeError):
    pass


def file_hash(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def value_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile('w', dir=path.parent, encoding='utf-8',
                                     newline='\n', delete=False) as handle:
        temporary = Path(handle.name)
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write('\n')
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def local_graph(root=ROOT):
    root = Path(root)
    paths = [path for directory in LIVE_DIRS for path in (root / directory).rglob('*.lean')]
    paths += [root / (directory + '.lean') for directory in LIVE_DIRS
              if (root / (directory + '.lean')).is_file()]
    modules = {path.relative_to(root).with_suffix('').as_posix().replace('/', '.'): path
               for path in paths}
    graph, external, sources = {}, set(), {}
    for name, path in sorted(modules.items()):
        data = path.read_bytes()
        sources[name] = hashlib.sha256(data).hexdigest()
        dependencies = imports(data.decode('utf-8'))
        missing_local = [dep for dep in dependencies if dep.split('.')[0] in LIVE_DIRS
                         and dep not in modules]
        if missing_local:
            raise BuildError('%s has missing local imports: %s' % (name, missing_local))
        graph[name] = [dep for dep in dependencies if dep in modules]
        external.update(dep for dep in dependencies if dep not in modules)
    return modules, graph, sources, external


def topological_order(graph, targets=None):
    visited, active, order = set(), set(), []

    def visit(name):
        if name not in graph:
            raise BuildError('unknown local module: ' + name)
        if name in active:
            raise BuildError('local import cycle at ' + name)
        if name in visited:
            return
        active.add(name)
        for dependency in graph[name]:
            visit(dependency)
        active.remove(name)
        visited.add(name)
        order.append(name)

    for name in sorted(targets if targets is not None else graph):
        visit(name)
    return order


def fingerprint(source_sha, dependency_keys, context):
    return value_hash({'schema': SCHEMA, 'source': source_sha,
                       'dependencies': dependency_keys, 'context': context,
                       'lean_flags': LEAN_FLAGS})


def stamp_path(root, module):
    return Path(root) / '.lake/build/certification/stamps' / (module.replace('.', '/') + '.json')


def valid_cache(root, module, expected):
    try:
        record = json.loads(stamp_path(root, module).read_text(encoding='utf-8'))
        if not isinstance(record, dict):
            return None
        if record.get('schema') != SCHEMA or record.get('fingerprint') != expected:
            return None
        outputs = record.get('outputs', {})
        if not isinstance(outputs, dict):
            return None
        required = '.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'
        if required not in outputs:
            return None
        for relative, digest in outputs.items():
            path = (Path(root) / relative).resolve()
            if not path.is_relative_to((Path(root) / '.lake/build').resolve()):
                return None
            if not path.is_file() or file_hash(path) != digest:
                return None
        key = value_hash({'fingerprint': expected, 'outputs': outputs})
        if record.get('key') != key:
            return None
        return record
    except (OSError, UnicodeError, ValueError, TypeError):
        return None


def external_context(root, runner=subprocess.run, required_imports=()):
    """Hash configuration and actual external compiled artifacts, not mtimes.

    This deliberately hashes the installed package/toolchain artifact inventory:
    a changed transitive external .olean must invalidate local stamps even when
    its importing umbrella module or lake-manifest revision is unchanged.
    """
    root = Path(root)
    proc = runner(['lake', 'env', 'lean', '--print-prefix'], cwd=root,
                  capture_output=True, text=True, encoding='utf-8', errors='replace')
    if proc.returncode:
        raise BuildError('cannot resolve pinned Lean toolchain: ' + proc.stdout + proc.stderr)
    prefix = Path(proc.stdout.strip()).resolve()
    if not (prefix / 'lib/lean').is_dir():
        raise BuildError('Lean returned no usable toolchain prefix')
    configuration = {name: file_hash(root / name)
                     for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean')}
    configuration['driver'] = file_hash(Path(__file__))
    configuration['source_lexer'] = file_hash(Path(__file__).with_name('lean_source.py'))
    lean_executable = prefix / 'bin' / ('lean.exe' if os.name == 'nt' else 'lean')
    configuration['lean_executable'] = file_hash(lean_executable)
    directories = [('toolchain', prefix / 'lib/lean')]
    manifest = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))
    package_root = root / manifest.get('packagesDir', '.lake/packages')
    for package in manifest['packages']:
        package_directory = package_root / package['name']
        if package.get('type') == 'git':
            actual = runner(['git', 'rev-parse', 'HEAD'], cwd=package_directory,
                            capture_output=True, text=True, encoding='utf-8', errors='replace')
            dirty = runner(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=package_directory,
                           capture_output=True, text=True, encoding='utf-8', errors='replace')
            if actual.returncode or actual.stdout.strip() != package['rev'] or dirty.returncode or dirty.stdout.strip():
                raise BuildError('dependency checkout differs from its clean pinned revision: ' + package['name'])
        directory = package_directory / '.lake/build/lib/lean'
        # Some manifest entries (notably Cli) are Lake-tooling dependencies and
        # have no compiled Lean library in this environment. Require artifacts
        # for the imports used by this build, rather than every manifest entry.
        if directory.is_dir():
            directories.append(('package/' + package['name'], directory))
    for module in sorted(required_imports):
        relative = Path(*module.split('.')).with_suffix('.olean')
        if not any((directory / relative).is_file() for _, directory in directories):
            raise BuildError('missing prebuilt external import: ' + module)
    inventory = {}
    for label, directory in directories:
        count = 0
        for path in sorted(directory.rglob('*')):
            if path.is_file() and (path.name.endswith(('.olean', '.olean.private', '.olean.server',
                                                        '.ir', '.dll', '.so', '.dylib'))):
                inventory[label + '/' + path.relative_to(directory).as_posix()] = file_hash(path)
                count += 1
        print('External snapshot: %s, %d artifacts' % (label, count), flush=True)
    if not inventory:
        raise BuildError('external artifact inventory is empty')
    return value_hash({'configuration': configuration, 'artifacts': inventory}), configuration, inventory


@contextmanager
def build_lock(root):
    path = Path(root) / '.lake/build/certification/build.lock'
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError as exc:
        raise BuildError('another driver owns %s; inspect its PID before removing a stale lock' % path) from exc
    try:
        with os.fdopen(descriptor, 'w') as handle:
            handle.write(str(os.getpid()) + '\n')
        yield
    finally:
        path.unlink(missing_ok=True)


def compile_module(root, module, source, source_sha, expected, runner=subprocess.run):
    root = Path(root)
    if file_hash(source) != source_sha:
        raise BuildError('source changed after planning: ' + module)
    work = root / '.lake/build/certification'
    work.mkdir(parents=True, exist_ok=True)
    # Python 3.13's Windows mkdtemp uses a private mode-0700 DACL, which can
    # exclude a restricted-token workspace process. Inherit this workspace's
    # existing ACL instead; the random name still prevents accidental reuse.
    staging = work / ('module-' + uuid.uuid4().hex)
    staging.mkdir()
    # The source file's module identity comes from its original path; output paths
    # may be staged elsewhere without replacing or importing temporary sources.
    stem = staging / module.split('.')[-1]
    command = ['lake', 'env', 'lean', *LEAN_FLAGS, str(source),
               '-o', str(stem) + '.olean', '-i', str(stem) + '.ilean',
               '-c', str(stem) + '.c', '--json']
    log_path = work / 'logs' / (module.replace('.', '/') + '.log')
    log_path.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    try:
        with log_path.open('w', encoding='utf-8') as log:
            proc = runner(command, cwd=root, stdout=log, stderr=subprocess.STDOUT,
                          text=True, encoding='utf-8', errors='replace')
        if proc.returncode:
            raise BuildError('%s failed, exit=%d; old outputs preserved; log=%s' %
                             (module, proc.returncode, log_path))
        if file_hash(source) != source_sha:
            raise BuildError('source changed during compilation; old outputs preserved: ' + module)
        if not Path(str(stem) + '.olean').is_file():
            raise BuildError('Lean exited successfully without producing .olean: ' + module)
        outputs = {}
        for suffix in (*OUTPUT_SUFFIXES, '.c'):
            staged = Path(str(stem) + suffix)
            if not staged.is_file():
                continue
            area = '.lake/build/ir' if suffix == '.c' else '.lake/build/lib/lean'
            relative = area + '/' + module.replace('.', '/') + suffix
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            digest = file_hash(staged)
            os.replace(staged, target)
            outputs[relative] = digest
        # A newer .olean must not accidentally load an obsolete private/server
        # sidecar left by an earlier compiler mode. Only after successful staging
        # do we remove absent, precisely named outputs for this one module.
        for suffix in (*OUTPUT_SUFFIXES, '.c'):
            area = '.lake/build/ir' if suffix == '.c' else '.lake/build/lib/lean'
            relative = area + '/' + module.replace('.', '/') + suffix
            if relative not in outputs:
                (root / relative).unlink(missing_ok=True)
        record = {'schema': SCHEMA, 'fingerprint': expected, 'source_sha256': source_sha,
                  'outputs': outputs, 'seconds': round(time.monotonic() - start, 3)}
        record['key'] = value_hash({'fingerprint': expected, 'outputs': outputs})
        atomic_json(stamp_path(root, module), record)
        return record
    finally:
        # Only this invocation's freshly allocated directory is removed.
        if staging.resolve().parent == work.resolve():
            shutil.rmtree(staging)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--module', action='append', help='target module (repeatable), with local dependencies')
    parser.add_argument('--plan', action='store_true', help='read-only topology/stamp inventory; no Lean or hashing packages')
    parser.add_argument('--plan-json', type=Path, help='write the plan for review')
    args = parser.parse_args(argv)
    try:
        if args.module and any(not MODULE_NAME.fullmatch(name) for name in args.module):
            raise BuildError('invalid target module name')
        modules, graph, sources, external = local_graph()
        order = topological_order(graph, args.module)
        required_external = {dep for name in order
                             for dep in imports(modules[name].read_text(encoding='utf-8'))
                             if dep not in modules}
        plan = {'schema': SCHEMA, 'modules': order, 'count': len(order),
                'missing_stamps': sum(not stamp_path(ROOT, name).is_file() for name in order),
                'external_imports': sorted(required_external),
                'note': 'stamp presence alone is not cache validation; actual build hashes inputs and outputs'}
        if args.plan_json:
            atomic_json(args.plan_json, plan)
        print('Serial plan: %d modules; %d without content-validation stamps' %
              (plan['count'], plan['missing_stamps']), flush=True)
        if args.plan:
            print('No Lean invoked and no build caches modified.', flush=True)
            return 0
        with build_lock(ROOT):
            success = ROOT / '.lake/build/certification/success.json'
            if success.exists():
                os.replace(success, success.with_name('previous-success.json'))
            context, configuration, artifacts = external_context(ROOT, required_imports=required_external)
            atomic_json(ROOT / '.lake/build/certification/external-snapshot.json',
                        {'context': context, 'configuration': configuration, 'artifacts': artifacts})
            keys, fingerprints = {}, {}
            reused = rebuilt = 0
            for index, name in enumerate(order, 1):
                expected = fingerprint(sources[name], {dep: keys[dep] for dep in graph[name]}, context)
                fingerprints[name] = expected
                record = valid_cache(ROOT, name, expected)
                if record is None:
                    print('[%d/%d] BUILD %s' % (index, len(order), name), flush=True)
                    record = compile_module(ROOT, name, modules[name], sources[name], expected)
                    rebuilt += 1
                else:
                    reused += 1
                keys[name] = record['key']
            # Fail if another process edited inputs or promoted artifacts during
            # this run. Per-module stamps remain resumable, never a false final pass.
            for name in order:
                if file_hash(modules[name]) != sources[name] or not valid_cache(ROOT, name, fingerprints[name]):
                    raise BuildError('inputs/artifacts changed during build: ' + name)
            final_context, _, _ = external_context(ROOT, required_imports=required_external)
            if final_context != context:
                raise BuildError('external artifacts/configuration changed during build')
            atomic_json(ROOT / '.lake/build/certification/success.json',
                        {'schema': SCHEMA, 'context': context, 'modules': keys,
                         'rebuilt': rebuilt, 'reused': reused})
            print('PASS: %d serially rebuilt, %d content-validated cached modules' % (rebuilt, reused), flush=True)
        return 0
    except (BuildError, OSError, UnicodeError, ValueError) as exc:
        print('FAIL: ' + str(exc), flush=True)
        return 1


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    raise SystemExit(main())
