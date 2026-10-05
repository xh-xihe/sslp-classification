"""Select the literal orbit-30 proof roots without assigning manuscript coverage."""
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
from lean_audit import audit_names
from prepare_orbit31_audit_20261005 import declarations
import verify
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--apply',action='store_true')
args=parser.parse_args()
D=ROOT/'artifacts/manuscript-certification-20261005'
snapshot=json.loads((D/'orbit30-staged-proof-snapshot-21.json').read_text(encoding='utf8'))
paths=[ROOT/'MainTheory'/(r['module']+'.lean') for r in snapshot['staged_modules']]
assert all(p.is_file() for p in paths)
roots=sorted({n for p in paths for n in declarations(p)})
(D/'orbit30-extra-roots.json').write_text(json.dumps(roots,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
if args.apply:
 p=ROOT/'MainTheory/ManuscriptCertificationAudit20261005.lean'
 s=p.read_text(encoding='utf8')
 marker='\n-- BEGIN CURRENT ORBIT30 CORRESPONDENCE ROOTS\n'
 if marker in s:s=s.split(marker)[0]
 begin='-- BEGIN CURRENT ORBIT30 IMPORTS\n'
 end='-- END CURRENT ORBIT30 IMPORTS\n'
 if begin in s:
  before,tail=s.split(begin,1)
  _,after=tail.split(end,1)
  s=before+after
 s=begin+''.join('import MainTheory.'+p.stem+'\n' for p in paths)+end+s
 existing=set(audit_names(s))
 for rel in verify.AUDIT_FILES:
  if ROOT/rel!=p:existing.update(audit_names((ROOT/rel).read_text(encoding='utf8')))
 new=[n for n in roots if n not in existing]
 s+=marker
 for start in range(0,len(new),64):s+='#certification_axioms [\n  '+',\n  '.join(new[start:start+64])+'\n]\n\n'
 p.write_text(s,encoding='utf8',newline='\n')
print('Explicit orbit-30 inspection roots:',len(roots),'modules:',len(paths))
