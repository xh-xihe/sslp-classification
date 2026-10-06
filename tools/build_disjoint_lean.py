#!/usr/bin/env python3
"""Compile only new modules outside a running serial build's frozen closure.

Uses the ordinary driver's exact compile command and content stamps. Dependencies
outside the requested prefixes must already have valid stamps in its current
external snapshot. This helper never writes the global success record.
"""
import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import time

import build_lean as b


def target_graph(targets):
    """Read the exact import closure, without scanning unrelated large payloads."""
    modules, graph, sources, external = {}, {}, {}, set()
    def visit(name):
        if name in modules:
            return
        source = b.ROOT / Path(*name.split('.')).with_suffix('.lean')
        if not source.is_file():
            raise b.BuildError('Missing local source: ' + name)
        data = source.read_bytes()
        modules[name] = source
        sources[name] = b.hashlib.sha256(data).hexdigest()
        dependencies = b.imports(data.decode('utf8'))
        local = [dep for dep in dependencies if dep.split('.')[0] in b.LIVE_DIRS]
        graph[name] = local
        external.update(set(dependencies) - set(local))
        for dep in local:
            visit(dep)
    for name in targets:
        visit(name)
    return modules, graph, sources, external


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--module', action='append', required=True)
    parser.add_argument('--prefix', action='append', required=True)
    parser.add_argument('--workers', type=int, default=3)
    parser.add_argument('--evidence', type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    modules, graph, sources, _ = target_graph(args.module)
    order = b.topological_order(graph, args.module)
    snapshot_path = b.ROOT / '.lake/build/certification/external-snapshot.json'
    snapshot_sha = b.file_hash(snapshot_path)
    snapshot = json.loads(snapshot_path.read_text(encoding='utf8'))
    context = snapshot['context']
    # Check the inexpensive configuration fields; final serial builds independently
    # rehash the complete external inventory before accepting these stamps.
    for name in ('lean-toolchain', 'lake-manifest.json'):
        if b.file_hash(b.ROOT / name) != snapshot['configuration'][name]:
            raise b.BuildError('Configuration changed: ' + name)
    if b.driver_fingerprint() != snapshot['configuration']['driver']:
        raise b.BuildError('Compilation policy differs from the frozen snapshot')
    prefix = b.subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                    cwd=b.ROOT, text=True).strip()
    if b.value_hash(b.compile_environment(b.ROOT, prefix)) != snapshot['configuration']['compile_environment']:
        raise b.BuildError('Lake compilation environment changed')
    selected = {name for name in order if any(name == p or name.startswith(p + '.') for p in args.prefix)}
    # A currently running serial build records its immutable module closure in
    # the plan supplied at launch. All selected modules must be disjoint from it.
    frozen = b.ROOT / 'artifacts/orbit-certification-20261003/active-collected-kl-plan.json'
    if (b.ROOT / '.lake/build/certification/build.lock').exists():
        if not frozen.is_file():
            raise b.BuildError('Need the running build\'s immutable module plan')
        overlap = selected & set(json.loads(frozen.read_text(encoding='utf8'))['modules'])
        if overlap:
            raise b.BuildError('Would modify active modules: ' + repr(sorted(overlap)))
    # The original one-prefix helper may still be running. Inspect its explicit
    # prefix arguments, rather than assuming a PID belongs to a particular job.
    legacy = b.ROOT / '.lake/build/certification/disjoint.lock'
    if legacy.exists():
        import psutil
        command = psutil.Process(int(legacy.read_text())).cmdline()
        if not any(Path(part).name == 'build_disjoint_lean.py' for part in command):
            raise b.BuildError('Cannot establish the legacy disjoint job scope')
        occupied = [command[i + 1] for i, part in enumerate(command[:-1]) if part == '--prefix']
        if not occupied or any(name == p or name.startswith(p + '.') for name in selected for p in occupied):
            raise b.BuildError('Overlap with the running disjoint job')
    registry = b.ROOT / '.lake/build/certification/disjoint-builds'
    registry.mkdir(exist_ok=True)
    registration = registry / 'registration.lock'
    register_fd = os.open(registration, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    os.close(register_fd)
    lock = registry / (b.value_hash(sorted(args.prefix)) + '.json')
    try:
        for other in registry.glob('*.json'):
            occupied = json.loads(other.read_text(encoding='utf8'))
            if selected & set(occupied['selected']):
                raise b.BuildError('Overlap with registered disjoint job: ' + str(other))
        b.atomic_json(lock, {'pid': os.getpid(), 'selected': sorted(selected), 'prefixes': args.prefix})
    finally:
        registration.unlink(missing_ok=True)
    keys, records = {}, {}
    pending = set(order)
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            while pending:
                ready = sorted(name for name in pending if all(dep in keys for dep in graph[name]))
                if not ready:
                    raise b.BuildError('No ready dependency')
                expected = {name: b.fingerprint(sources[name], {dep: keys[dep] for dep in graph[name]}, context)
                            for name in ready}
                jobs = {}
                for name in ready:
                    cached = b.valid_cache(b.ROOT, name, expected[name])
                    if cached is not None:
                        keys[name] = cached['key']
                        records[name] = {'action': 'validated-cache', **cached}
                    elif name not in selected:
                        raise b.BuildError('External local dependency needs a serial build: ' + name)
                    else:
                        print('BUILD', name, flush=True)
                        jobs[pool.submit(b.compile_module, b.ROOT, name, modules[name],
                                         sources[name], expected[name])] = name
                for future in concurrent.futures.as_completed(jobs):
                    name = jobs[future]
                    record = future.result()
                    keys[name] = record['key']
                    records[name] = {'action': 'compiled', **record}
                    print('PASS', name, record['seconds'], flush=True)
                pending.difference_update(ready)
        if b.file_hash(snapshot_path) != snapshot_sha:
            raise b.BuildError('External snapshot changed during this build')
        for name in order:
            if b.file_hash(modules[name]) != sources[name] or b.valid_cache(b.ROOT, name, records[name]['fingerprint']) is None:
                raise b.BuildError('Final source/output check failed: ' + name)
        b.atomic_json(args.evidence, {'status': 'PASS', 'policy': 'ordinary driver compile_module',
            'context': context, 'workers': args.workers, 'modules': len(order),
            'selected': sorted(selected), 'records': records,
            'seconds': round(time.monotonic() - start, 3),
            'note': 'The final serial build must validate the external inventory and all stamps.'})
        print('PASS disjoint build', len(selected), 'selected modules', flush=True)
    finally:
        lock.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
