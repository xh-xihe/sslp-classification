"""Regenerate/check the orbit manifest against both current private manuscripts.

Only representative data and SHA-256 provenance are written. Missing, duplicate,
malformed, or inconsistent rows fail before writing. The reviewed no-go module
mapping is preserved and checked against the complete 66-row table.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from math import gcd

REPO = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE = REPO / 'documents' / '20260908'
ROW = re.compile(
    r'^\s*(\d+)\s*&\s*(\d+)\s*&\s*(\d+)\s*&\s*\$\(([0-9,\s]+)\)\$'
    r'\s*&\s*\$\((\d+),(\d+)\)\$\s*&\s*(\d+)\s*&\s*(\d+)'
    r'\s*&\s*(\d+)\s*&\s*\\textsf\{([^}]+)\}\s*\\\\\s*$')


class ManifestError(ValueError):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fiber_size(angle, modulus, residue):
    return sum(sum(angle[i] for i in range(6) if bits & (1 << i)) % modulus == residue
               for bits in range(64))


def parse_table(text):
    text = re.sub(r'(?<!\\)%[^\n]*', '', text)
    label = r'\label{tab:66orbits}'
    if text.count(label) != 1:
        raise ManifestError('expected exactly one table labelled tab:66orbits')
    position = text.index(label)
    begin = text.rfind(r'\begin{longtable}', 0, position)
    end = text.find(r'\end{longtable}', position)
    if begin < 0 or end < 0:
        raise ManifestError('tab:66orbits is not a complete longtable')
    rows = {}
    for line in text[begin:end].splitlines():
        if not re.match(r'^\s*\d+\s*&', line):
            continue
        match = ROW.fullmatch(line)
        if not match:
            raise ManifestError('unparseable numeric row in tab:66orbits')
        values = match.groups()
        oid, q, logical_order = map(int, values[:3])
        if oid in rows:
            raise ManifestError('duplicate orbit ID %d' % oid)
        angle = [int(value.strip()) for value in values[3].split(',')]
        n0, n1 = map(int, values[4:6])
        r_star, lp_dimension, multiplicity = map(int, values[6:9])
        if len(angle) != 6 or angle != sorted(angle):
            raise ManifestError('orbit %d has no sorted six-coordinate angle' % oid)
        if q < 2 or logical_order < 2 or q % logical_order:
            raise ManifestError('orbit %d has invalid lift/projective orders' % oid)
        if not 0 <= r_star <= 6 or lp_dimension > n0 + n1 or multiplicity < 1:
            raise ManifestError('orbit %d has invalid rank/dimension/multiplicity columns' % oid)
        if any(value < 0 or value >= q for value in angle) or gcd(q, *angle) != 1:
            raise ManifestError('orbit %d has a nonprimitive or out-of-range angle' % oid)
        residue = q // logical_order
        actual = (fiber_size(angle, q, 0), fiber_size(angle, q, residue))
        if actual != (n0, n1):
            raise ManifestError('orbit %d ordered fiber sizes disagree: %s != %s' %
                                (oid, actual, (n0, n1)))
        status = values[9]
        if status not in {'open', 'WE', 'rigid', 'no-go', 'realized'}:
            raise ManifestError('orbit %d has unrecognized status %r' % (oid, status))
        rows[oid] = (dict(q=q, m=logical_order, a=angle, d=residue,
                          ord=q // gcd(residue, q), n0=n0, n1=n1,
                          r_star=r_star, lp_dimension=lp_dimension,
                          multiplicity=multiplicity), status)
    if set(rows) != set(range(1, 67)):
        raise ManifestError('expected IDs 1..66 exactly; missing=%s extra=%s' %
                            (sorted(set(range(1, 67)) - set(rows)),
                             sorted(set(rows) - set(range(1, 67)))))
    return rows


def build_manifest(source_dir, existing, repo=REPO):
    source_dir, repo = Path(source_dir).resolve(), Path(repo).resolve()
    texts, hashes = {}, {}
    for filename in ('main.tex', 'supplementary.tex'):
        path = source_dir / filename
        if not path.is_file():
            raise ManifestError('required private manuscript is missing: ' + str(path))
        data = path.read_bytes()
        texts[filename] = data.decode('utf-8')
        try:
            display = path.relative_to(repo).as_posix()
        except ValueError:
            display = filename
        hashes[display] = digest(data)
    rows = parse_table(texts['supplementary.tex'])
    inventory = existing.get('_no_go', {})
    mapping = inventory.get('lean_modules', {}) if isinstance(inventory, dict) else {}
    expected_ids = {str(oid) for oid, (_, status) in rows.items() if status == 'no-go'}
    if len(expected_ids) != 51 or not isinstance(mapping, dict) or set(mapping) != expected_ids:
        raise ManifestError('reviewed no-go inventory must match all 51 table no-go IDs')
    for oid, module in mapping.items():
        if module != ('Order9' if oid == '66' else 'Orbit' + oid):
            raise ManifestError('unexpected reviewed no-go module for orbit ' + oid)
    result = {str(oid): row for oid, (row, _) in sorted(rows.items())}
    result['_no_go'] = inventory
    result['_paper'] = {
        'schema': 1,
        'sources_sha256': hashes,
        'table_source': next(key for key in hashes if key.endswith('supplementary.tex')),
        'table_label': 'tab:66orbits',
        'orbit_count': 66,
        'numeric_rows_sha256': digest(json.dumps(
            {key: value for key, value in result.items() if key.isdigit()},
            sort_keys=True, separators=(',', ':')).encode('utf-8')),
    }
    return result


def atomic_json(path, value):
    path = Path(path)
    with tempfile.NamedTemporaryFile('w', dir=path.parent, prefix=path.name + '.',
                                     suffix='.tmp', encoding='utf-8', newline='\n',
                                     delete=False) as handle:
        temporary = Path(handle.name)
        json.dump(value, handle, indent=1, sort_keys=True)
        handle.write('\n')
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=DEFAULT_SOURCE)
    parser.add_argument('--manifest', type=Path, default=REPO / 'tools' / 'manifest.json')
    parser.add_argument('--check', action='store_true', help='compare without writing')
    args = parser.parse_args(argv)
    try:
        old = json.loads(args.manifest.read_text(encoding='utf-8'))
        new = build_manifest(args.source_dir, old)
        if args.check:
            if old != new:
                raise ManifestError('manifest data or manuscript hashes differ; review and regenerate')
            print('PASS: all 66 orbit rows, 51 no-go mappings, and both private-source hashes match')
        else:
            atomic_json(args.manifest, new)
            print('Wrote %s: 66 orbit rows with both private-source SHA-256 hashes' % args.manifest)
        return 0
    except (OSError, UnicodeError, ValueError) as exc:
        print('FAIL: ' + str(exc))
        return 1


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    raise SystemExit(main())
