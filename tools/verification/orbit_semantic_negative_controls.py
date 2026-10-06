#!/usr/bin/env python3
"""Confirm that wrong target coefficients and spectral formulas are rejected."""
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
ARTIFACTS = ROOT / 'artifacts/orbit-certification-20261003'


def check(name, source, mutation, expected_failure):
    temp = ROOT / 'tmp/orbit-semantic-negative-controls'
    temp.mkdir(exist_ok=True)
    original = source.read_text(encoding='utf8')
    changed = mutation(original)
    if changed == original:
        raise ValueError('Mutation did not change the source')
    records = []
    for suffix, text, code in [('pass', original, 0), ('fail', changed, 1)]:
        path = temp / (name + '-' + suffix + '.lean')
        path.write_text(text, encoding='utf8', newline='\n')
        start = time.monotonic()
        result = subprocess.run(['lake', 'env', 'lean', '-j', '1', '-DwarningAsError=true', str(path)],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf8', errors='replace')
        log = ARTIFACTS / (name + '-negative-' + suffix + '.log')
        log.write_text(result.stdout, encoding='utf8')
        if (result.returncode == 0) != (code == 0):
            raise ValueError('Unexpected result for ' + str(path) + ': ' + result.stdout[-2500:])
        if code and expected_failure not in result.stdout:
            raise ValueError('Failure was not the intended mathematical rejection: ' + result.stdout[-2500:])
        records.append({'case': suffix, 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'returncode': result.returncode, 'seconds': round(time.monotonic() - start, 3),
                        'log': log.relative_to(ROOT).as_posix(),
                        'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()})
        print('PASS control', name, suffix, flush=True)
    return {'name': name, 'original': source.relative_to(ROOT).as_posix(),
            'original_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'records': records}


def main():
    results = [check('orbit3-target-coefficient', ROOT / 'SixQubit/Generated/Orbit3TargetData.lean',
        lambda s: s.replace('Orbit3SexticIdentity.target j := by decide +kernel',
            'Orbit3SexticIdentity.target j + (if j = 6 then 1 else 0) := by decide +kernel'),
        'Tactic `decide` failed')]
    results.append(check('orbit2-spectrum-formula', ROOT / 'SixQubit/Generated/Orbit2Spectra/Pattern2.lean',
        lambda s: s.replace('def polynomial : Polynomial ℚ := (X - C 52)',
                            'def polynomial : Polynomial ℚ := (X - C 53)'),
        'unsolved goals'))
    (ARTIFACTS / 'orbit-semantic-negative-controls.json').write_text(
        json.dumps({'status': 'PASS', 'controls': results}, indent=2) + '\n', encoding='utf8')


if __name__ == '__main__':
    main()
