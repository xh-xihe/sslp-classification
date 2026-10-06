"""Reconstruct the literal orbit-30 finite matrices and table certificates.

Source equality is a provenance check. The whole Lean kernel build and fresh
transitive axiom audit independently check every generated proof.
"""
import argparse,hashlib,json,subprocess,sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
GENERATORS=[
 'generate_orbit30_moment_rank.py','generate_orbit30_printed_moments.py',
 'generate_orbit30_probability_labels.py','generate_orbit30_physical_rows.py',
 'generate_orbit30_normalized_determinant.py','generate_orbit30_graph_classification.py',
 'generate_orbit30_proper_graph_tables.py','generate_orbit30_full_support.py',
]
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def source_hashes():return {p.relative_to(ROOT).as_posix():sha(p) for p in sorted((ROOT/'MainTheory').glob('Orbit30*.lean'))}
def check(name):
 p=ROOT/'tools/verification'/name
 r=subprocess.run([sys.executable,'-X','utf8',str(p),'--check'],cwd=ROOT,capture_output=True,encoding='utf8')
 return {'tool':p.relative_to(ROOT).as_posix(),'sha256_lf':sha(p),'exit_code':r.returncode,'output':r.stdout+r.stderr}
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 if args.output and args.output.exists():raise ValueError('Refusing to overwrite a reproduction record')
 before=source_hashes()
 with ThreadPoolExecutor(max_workers=2) as pool:checks=list(pool.map(check,GENERATORS))
 after=source_hashes()
 if before!=after:raise ValueError('Proof sources changed during reproduction checks')
 passed=all(r['exit_code']==0 for r in checks)
 record={'schema':1,'passed':passed,'scope':'Source reproduction only; ordinary kernel proofs and axiom audit are separately required.',
  'source_hashes_lf':after,'checks':checks}
 if args.output:
  args.output.parent.mkdir(parents=True,exist_ok=True)
  args.output.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8',newline='\n')
 for row in checks:
  print(('PASS' if row['exit_code']==0 else 'FAIL')+': '+row['tool'])
  if row['exit_code']:print(row['output'])
 print(len(checks),'source reconstruction checks;',len(after),'source bindings;', 'PASS' if passed else 'FAIL')
 return 0 if passed else 1
if __name__=='__main__':raise SystemExit(main())
