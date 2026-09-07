"""Check exact generated-source coverage, hashes, and topological build lists."""
import hashlib
from pathlib import Path
import re
import sys

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / 'tools'))
from lean_source import imports

MANIFEST_DIRS = ('MainTheory/Generated/BinaryBetaFiveFast',
                 'MainTheory/Generated/BinaryBetaSixKernel',
                 'SixQubit/Generated/OpenMParity',
                 'SixQubit/Generated/OpenLFamilies')


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
        print('PASS: generated coverage, SHA-256, and build order (%s files)' %
              ' + '.join(map(str, counts)))
        return 0
    except (OSError, UnicodeError, ValueError) as exc:
        print('FAIL: ' + str(exc))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
