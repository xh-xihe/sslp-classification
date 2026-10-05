#!/usr/bin/env python3
"""Import the reviewed orbit-2 proofs, preserving a precise upstream ledger."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
UPSTREAM = ROOT / 'scratch/orbit2-colleague-review/six-qubit-orbit2/lean'
COMMIT = 'f84bbd39451a3e0648fd1bd4ccf0ad38f558245a'
ADAPTERS = {
    'Orbit2/PhysicalMacWilliams.lean': 'SixQubit.MacWilliams',
    'Orbit2/PhysicalShadow.lean': 'SixQubit.Shadow',
    'Orbit2/PhysicalB.lean': 'SixQubit.BEnumerator',
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream-dir', type=Path, default=UPSTREAM,
                        help='reviewed package Lean directory containing Orbit2.lean and Orbit2/')
    args = parser.parse_args()
    upstream = args.upstream_dir.resolve()
    if not (upstream / 'Orbit2.lean').is_file() or not (upstream / 'Orbit2').is_dir():
        parser.error('reviewed upstream package is absent; use --upstream-dir. The published proofs already build without this import step.')
    evidence = json.loads((ROOT / 'artifacts/orbit-certification-20261003/'
                           'colleague-orbit2-fresh-build.json').read_text(encoding='utf8'))
    if evidence.get('status') != 'PASS':
        raise RuntimeError('The independent fresh build must pass first')
    records = []
    sources = sorted((upstream / 'Orbit2').rglob('*.lean')) + [upstream / 'Orbit2.lean']
    for source in sources:
        relative = source.relative_to(upstream).as_posix()
        original = source.read_bytes()
        text = original.decode('utf8')
        module = relative[:-5].replace('/', '.')
        if sha(original) != evidence['records'][module]['source_sha256']:
            raise RuntimeError('Upstream source differs from the fresh kernel build: ' + module)
        changes = []
        if relative in ADAPTERS:
            dependency = ADAPTERS[relative]
            text = ('import ' + dependency + '\n\n'
                    '/-! The shared physical definitions are provided by the main library. -/\n')
            changes.append({'kind': 'shared-definition-adapter', 'import': dependency})
        else:
            log = upstream / '.lake/review-logs' / (module + '.log')
            options = sorted(set(re.findall(r'set_option (linter\.\w+) false',
                log.read_text(encoding='utf8') if log.exists() else '')))
            if options:
                lines = text.splitlines(keepends=True)
                end = max(i for i, line in enumerate(lines) if line.startswith('import ')) + 1
                lines[end:end] = ['\n-- Preserve upstream proofs; suppress only the recorded style linters.\n'] + [
                    'set_option ' + option + ' false\n' for option in options]
                text = ''.join(lines)
                changes.append({'kind': 'local-style-linter-options', 'options': options})
        data = text.encode('utf8')
        destination = ROOT / relative
        if destination.exists() and destination.read_bytes() != data:
            raise RuntimeError('Refusing to overwrite a different local module: ' + relative)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        records.append({'module': module, 'path': relative, 'upstream_sha256': sha(original),
                        'integrated_sha256': sha(data), 'changes': changes})
    target = ROOT / 'artifacts/orbit-certification-20261003/orbit2-integration-sources.json'
    target.write_text(json.dumps({'schema': 1, 'upstream_commit': COMMIT,
        'upstream_repository': 'https://github.com/xh-xihe/dyadic-lifts.git',
        'scope': 'actual-encoder orbit-2 enumerator image',
        'module_count': len(records), 'modules': records}, indent=2) + '\n', encoding='utf8')
    print('Imported', len(records), 'modules; recorded adapters and local style options.')


if __name__ == '__main__':
    main()
