"""Check all nine canonical final bridge sources against their strict-pilot hashes."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
D = ROOT / 'artifacts/manuscript-certification-20261005'
snapshot = json.loads((D / 'final-bridge-staged-proof-snapshot-9.json').read_text(encoding='utf8'))
assert len(snapshot['staged_modules']) == 9
for row in snapshot['staged_modules']:
    raw = (ROOT / row['canonical_source']).read_bytes().replace(b'\r\n', b'\n')
    if hashlib.sha256(raw).hexdigest() != row['canonical_sha256_lf']:
        raise SystemExit('FAIL source changed: ' + row['canonical_source'])
print('PASS: all nine final bridge source hashes match their strict-pilot snapshot')
