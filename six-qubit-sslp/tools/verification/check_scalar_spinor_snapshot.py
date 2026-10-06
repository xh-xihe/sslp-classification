"""Check accepted-batch source hashes; kernel building remains separate."""
import argparse,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--snapshot',type=Path,default=ROOT/'artifacts/manuscript-certification-20261005/scalar-spinor-staged-proof-snapshot-12.json')
parser.add_argument('--output',type=Path)
args=parser.parse_args()
snapshot=json.loads(args.snapshot.read_text(encoding='utf8'))
rows=snapshot['staged_modules']
assert len(rows)==12 and len({r['canonical_source'] for r in rows})==12
checks=[]
for row in rows:
    relative=row['canonical_source']
    path=(ROOT/relative).resolve()
    assert path.is_relative_to(ROOT/'MainTheory')
    value=hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
    passed=value==row['canonical_sha256_lf']
    checks.append({'path':relative,'sha256_lf':value,'passed':passed})
    print(('PASS' if passed else 'FAIL')+': '+relative)
passed=all(r['passed'] for r in checks)
if args.output:
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps({'schema':1,'passed':passed,'checks':checks,
        'source_hashes_lf':{r['path']:r['sha256_lf'] for r in checks},
        'scope':'LF source-snapshot consistency only; mathematical acceptance requires whole kernel build and fresh transitive axiom audit.'},
        ensure_ascii=False,indent=2)+'\n',encoding='utf8',newline='\n')
raise SystemExit(0 if passed else 1)
