#!/usr/bin/env python3
"""Re-key build stamps from the whole-file context formula to the current one.

Until 2026-10-02 the build context in every stamp hashed lakefile.lean and
tools/build_lean.py byte for byte (formula v1). It now hashes what decides how
a module compiles (see `build_lean.external_context`). Every stamp written
under v1 is therefore unreadable to the builder, although each output is still
exactly what compiling its source produced. Rebuilding this repository costs
about 178 CPU-hours, so this tool re-keys the stamps instead, and fails closed.

* Each v1 configuration is given explicitly, as the lakefile and driver files
  that were in force. Its context is recomputed from those two hashes and the
  entries v1 shares with the current formula (toolchain, manifest, source
  lexer, Lean executable, external artifact inventory).
* Modules are visited dependencies first. A stamp is accepted only if, under
  one of the given v1 contexts, its fingerprint equals the one recomputed from
  the module's current source hash and its dependencies' keys under that same
  context, its key equals hash(fingerprint, outputs), and every recorded
  output exists with its recorded hash. Dependency keys are recomputed the
  same way, so every edge is checked, not assumed.
* A module that is not accepted keeps its stamp untouched, and so does every
  module that imports it. The builder rebuilds them.
* An accepted stamp is rewritten with the current context's fingerprint and
  key. Its outputs are unchanged. It gains a `migrated_from` field naming the
  v1 context it was accepted under.

Whether a configuration change can affect compilation is not judged here. The
migration record names the configurations and the person or commit that judged
them; the evidence belongs in that commit.

Usage:
  python tools/migrate_build_context.py --previous LAKEFILE DRIVER [...] --record PATH [--dry-run]
"""
import argparse
import json
import sys
from pathlib import Path

import build_lean as B


def v1_context(configuration, inventory, lakefile, driver):
    """The v1 formula: the current shared entries plus two whole-file hashes."""
    shared = {name: configuration[name]
              for name in ('lean-toolchain', 'lake-manifest.json', 'source_lexer', 'lean_executable')}
    v1 = dict(shared, **{'lakefile.lean': B.file_hash(lakefile), 'driver': B.file_hash(driver)})
    return B.value_hash({'configuration': v1, 'artifacts': inventory}), v1


def outputs_intact(root, record):
    outputs = record.get('outputs')
    if not isinstance(outputs, dict):
        return False
    for relative, digest in outputs.items():
        path = (Path(root) / relative).resolve()
        if not path.is_relative_to((Path(root) / '.lake/build').resolve()):
            return False
        if not path.is_file() or B.file_hash(path) != digest:
            return False
    return True


def migrate(root, previous, dry_run):
    modules, graph, sources, _ = B.local_graph(root)
    order = B.topological_order(graph)
    required = {dep for name in order
                for dep in B.imports(modules[name].read_text(encoding='utf-8')) if dep not in modules}
    current, configuration, inventory = B.external_context(root, required_imports=required)
    contexts = []
    for lakefile, driver in previous:
        context, v1 = v1_context(configuration, inventory, lakefile, driver)
        contexts.append({'context': context, 'configuration': v1,
                         'lakefile': str(lakefile), 'driver': str(driver)})

    keys = {c['context']: {} for c in contexts}      # v1 key of every module, per context
    new_keys, accepted, unchanged = {}, {}, []
    rejected, blocked = {}, {}
    for name in order:
        path = B.stamp_path(root, name)
        try:
            record = json.loads(path.read_text(encoding='utf-8'))
        except (OSError, ValueError):
            record = None
        bad = [dep for dep in graph[name] if dep in rejected or dep in blocked]
        if bad:
            blocked[name] = bad[0]
            continue
        new_fp = B.fingerprint(sources[name], {dep: new_keys[dep] for dep in graph[name]}, current)
        if record and B.valid_cache(root, name, new_fp):
            # Already current: written by the builder under the current formula,
            # or by an earlier run of this tool, which kept the v1 key it replaced.
            new_keys[name] = record['key']
            unchanged.append(name)
            for c in contexts:
                keys[c['context']][name] = (record.get('previous_key')
                                            if record.get('migrated_from') == c['context'] else None)
            continue
        if not record:
            rejected[name] = 'no stamp'
            continue
        if record.get('schema') != B.SCHEMA:
            rejected[name] = 'schema'
            continue
        if not outputs_intact(root, record):
            rejected[name] = 'outputs differ from the recorded hashes'
            continue
        match = None
        for c in contexts:
            ctx = c['context']
            deps = {dep: keys[ctx].get(dep) for dep in graph[name]}
            if None in deps.values():
                continue
            fp = B.fingerprint(sources[name], deps, ctx)
            keys[ctx][name] = B.value_hash({'fingerprint': fp, 'outputs': record['outputs']})
            if (match is None and record.get('fingerprint') == fp
                    and record.get('key') == keys[ctx][name]):
                match = ctx
        if match is None:
            rejected[name] = 'no given context reproduces its fingerprint and key'
            continue
        new_key = B.value_hash({'fingerprint': new_fp, 'outputs': record['outputs']})
        new_keys[name] = new_key
        accepted[name] = match
        if not dry_run:
            rewritten = dict(record, fingerprint=new_fp, key=new_key, migrated_from=match,
                             previous_fingerprint=record['fingerprint'], previous_key=record['key'])
            B.atomic_json(path, rewritten)
    return {'current_context': current, 'current_configuration': configuration,
            'previous': contexts, 'modules': len(order),
            'already_current': len(unchanged), 'migrated': len(accepted),
            'migrated_by_context': {c['context']: sum(v == c['context'] for v in accepted.values())
                                    for c in contexts},
            'rejected': rejected, 'blocked_by_rejected': blocked}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--previous', nargs=2, action='append', metavar=('LAKEFILE', 'DRIVER'), required=True)
    parser.add_argument('--record', type=Path, required=True)
    parser.add_argument('--note', default='')
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args(argv)
    previous = [(Path(a), Path(b)) for a, b in args.previous]
    with B.build_lock(B.ROOT):
        report = migrate(B.ROOT, previous, args.dry_run)
    report['dry_run'] = args.dry_run
    report['note'] = args.note
    B.atomic_json(args.record, report)
    print('modules %d: already current %d, migrated %d %s, rejected %d, blocked %d%s' % (
        report['modules'], report['already_current'], report['migrated'],
        {k[:12]: v for k, v in report['migrated_by_context'].items()},
        len(report['rejected']), len(report['blocked_by_rejected']),
        ' (dry run: no stamp written)' if args.dry_run else ''))
    for name, reason in report['rejected'].items():
        print('  rejected %s: %s' % (name, reason))
    return 0


if __name__ == '__main__':
    sys.exit(main())
