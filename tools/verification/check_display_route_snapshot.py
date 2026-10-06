"""Check the promoted display-route source hashes against strict-pilot records."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
D=ROOT/'artifacts/manuscript-certification-20261005'
snapshot=json.loads((D/'display-route-staged-proof-snapshot-20.json').read_text(encoding='utf8'))
checks=[]
for row in snapshot['staged_modules']:
 raw=(ROOT/row['canonical_source']).read_bytes().replace(b'\r\n',b'\n')
 passed=hashlib.sha256(raw).hexdigest()==row['canonical_sha256_lf']
 checks.append({'source':row['canonical_source'],'passed':passed})
 if not passed:raise SystemExit('FAIL source changed: '+row['canonical_source'])
print('PASS: all twenty display-route source hashes match their strict-pilot snapshot')
