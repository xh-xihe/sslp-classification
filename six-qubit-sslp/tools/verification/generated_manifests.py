"""Check exact generated-source coverage, hashes, and topological build lists."""
import hashlib
import gzip
import json
from pathlib import Path
import re
import sys

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / 'tools'))
from lean_source import imports, code_only

MANIFEST_DIRS = ('MainTheory/Generated/BinaryBetaFiveFast',
                 'MainTheory/Generated/BinaryBetaSixKernel',
                 'SixQubit/Generated/OpenMParity',
                 'SixQubit/Generated/OpenLFamilies')
MANIFEST_DIRS += ('SixQubit/Generated/Orbit2Gram',)
MANIFEST_DIRS += ('SixQubit/Generated/Orbit2Spectra',
                  'SixQubit/Generated/Orbit3TargetTraces',
                  'SixQubit/Generated/Orbit3CollectedRows',)

SIGN_ORDERS = (7, 8, 9)


def check_sign_family(repo, binary_order):
    repo = Path(repo)
    relative = f'MainTheory/Generated/SignBeta{binary_order}'
    prefix = relative.replace('/', '.')
    directory = repo / relative
    manifest = json.loads((directory / 'manifest.json').read_text(encoding='utf-8'))
    compressed = (repo / f'results/sign-beta-proposals/beta{binary_order}.json.gz').read_bytes()
    raw = gzip.decompress(compressed)
    # Earlier development inputs were plain JSON. Both encodings must name
    # precisely the same persistent proposal, never an unavailable temp file.
    if manifest.get('proposal_sha256') not in {
            hashlib.sha256(compressed).hexdigest(), hashlib.sha256(raw).hexdigest()}:
        raise ValueError('sign proposal SHA-256 mismatch: ' + relative)
    proposal = json.loads(raw)
    if proposal['sign_order'] != binary_order + 1:
        raise ValueError('wrong sign order in proposal: ' + relative)
    if manifest.get('schema') != 1 or not isinstance(manifest.get('modules'), list):
        raise ValueError('invalid sign manifest schema: ' + relative)
    entries, nodes = {}, set()
    for row in manifest['modules']:
        module = row['module']
        if not re.fullmatch(re.escape(prefix) + r'\.(Data|Proof)\.G[0-9_]+', module):
            raise ValueError('sign module leaves expected family: ' + module)
        if module in entries:
            raise ValueError('duplicate sign module: ' + module)
        path = repo / (module.replace('.', '/') + '.lean')
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError('sign source SHA-256 mismatch: ' + module)
        source = data.decode('utf-8')
        if imports(source) != row['imports']:
            raise ValueError('sign import inventory differs: ' + module)
        actual_nodes = re.findall(r'^namespace\s+(' + re.escape(prefix) +
                                  r'\.(?:Data|Proof)\.N[0-9_]+)\s*$', code_only(source), re.M)
        if actual_nodes != row['nodes'] or nodes.intersection(actual_nodes):
            raise ValueError('sign node inventory differs or repeats: ' + module)
        nodes.update(actual_nodes)
        entries[module] = row
    expected_nodes = {f'{prefix}.{kind}.N{depth:02d}_{index:04d}'
                      for depth, level in enumerate(proposal['levels'], 1)
                      for index in range(len(level)) for kind in ('Data', 'Proof')}
    if nodes != expected_nodes:
        raise ValueError('sign proposal node coverage differs: ' + relative)
    actual_files = {p.relative_to(repo).as_posix() for p in directory.rglob('*.lean')}
    expected_files = {m.replace('.', '/') + '.lean' for m in entries}
    if not entries or actual_files != expected_files:
        raise ValueError('sign generated file coverage differs: ' + relative)
    visiting, visited = set(), set()

    def visit(module):
        if module in visited:
            return
        if module in visiting:
            raise ValueError('cyclic sign dependencies: ' + module)
        visiting.add(module)
        for dependency in entries[module]['imports']:
            if dependency.startswith(prefix + '.'):
                if dependency not in entries:
                    raise ValueError('missing sign dependency: ' + dependency)
                visit(dependency)
        visiting.remove(module)
        visited.add(module)

    for module in entries:
        visit(module)
    return len(entries)


def check_directory(repo, relative):
    repo = Path(repo)
    directory = repo / relative
    text = (directory / 'generation-manifest.sha256').read_text(encoding='utf-8')
    count_match = re.findall(r'^# lean_files=(\d+)$', text, re.M)
    if len(count_match) != 1:
        raise ValueError('missing or duplicate generated file count: ' + relative)
    entries = {}
    for line in text.splitlines():
        if not line or line.startswith('#'):
            continue
        match = re.fullmatch(r'([0-9a-f]{64})\s+([A-Za-z_][A-Za-z0-9_.]*)', line)
        if not match:
            raise ValueError('malformed manifest row: ' + relative)
        digest, module = match.groups()
        if module in entries:
            raise ValueError('duplicate manifest module: ' + module)
        path = Path(module.replace('.', '/') + '.lean')
        if not path.as_posix().startswith(relative + '/'):
            raise ValueError('manifest module leaves expected directory: ' + module)
        entries[module] = (digest, path)
    if len(entries) != int(count_match[0]) or not entries:
        raise ValueError('generated file count disagrees: ' + relative)
    actual = {path.relative_to(repo) for path in directory.rglob('*.lean')}
    expected = {path for _, path in entries.values()}
    if actual != expected:
        raise ValueError('generated coverage mismatch: missing=%d unexpected=%d' %
                         (len(expected - actual), len(actual - expected)))
    order = [line.strip() for line in (directory / 'serial-build-order.txt').read_text(
        encoding='utf-8').splitlines() if line.strip() and not line.startswith('#')]
    if len(order) != len(entries) or set(order) != set(entries):
        raise ValueError('serial build list differs from manifest: ' + relative)
    seen = set()
    for module in order:
        digest, relative_path = entries[module]
        data = (repo / relative_path).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError('generated SHA-256 mismatch: ' + str(relative_path))
        for dependency in imports(data.decode('utf-8')):
            if dependency in entries and dependency not in seen:
                raise ValueError('serial build list is not topological: ' + module)
        seen.add(module)
    return len(entries)


def main():
    try:
        counts = [check_directory(REPO, relative) for relative in MANIFEST_DIRS]
        counts += [check_sign_family(REPO, order) for order in SIGN_ORDERS]
        print('PASS: generated coverage, SHA-256, and build order (%s files)' %
              ' + '.join(map(str, counts)))
        return 0
    except (OSError, UnicodeError, ValueError) as exc:
        print('FAIL: ' + str(exc))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
