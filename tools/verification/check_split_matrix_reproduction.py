"""Check literal split, orbit-28 probability and orbit-26 physical block sources."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
checks=[]
for name in ('generate_split_family_displays.py','generate_orbit28_printed_probabilities.py',
             'generate_orbit26_physical_matrices.py'):
    command=[sys.executable,str(ROOT/'tools/verification'/name),'--check']
    result=subprocess.run(command,cwd=ROOT,capture_output=True,encoding='utf8')
    checks.append({'generator':name,'passed':result.returncode==0,
                   'output':result.stdout+result.stderr})
    print(('PASS' if result.returncode==0 else 'FAIL')+': '+name)
names=('ArbitrarySplitTrace','ArbitrarySplitEnumerators','Orbit3SplitScalarDisplays',
       'Orbit3SplitEnumerators','Orbit2SplitScalarDisplays','Orbit2SplitEnumerators',
       'PrimitiveW3SplitScalarDisplays','PrimitiveW3SplitEnumerators',
       'Orbit28PrintedProbabilities','Orbit32ParityNotation','Orbit26PhysicalMatrices',
       'Orbit26DependentAnchors')
hashes={f'MainTheory/{n}.lean':hashlib.sha256((ROOT/'MainTheory'/(n+'.lean')).read_bytes()
   .replace(b'\r\n',b'\n')).hexdigest() for n in names}
passed=all(row['passed'] for row in checks)
if args.output:
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps({'schema':1,'passed':passed,'checks':checks,
      'source_hashes_lf':hashes,'scope':'Exact-source reconstruction; separate whole kernel build and audit required.'},ensure_ascii=False,indent=2)+'\n',encoding='utf8',newline='\n')
raise SystemExit(0 if passed else 1)
