"""Print bounded error summaries without expanding enormous matrix goals."""
import argparse
import json
from pathlib import Path
import sys

sys.stdout.reconfigure(encoding='utf8')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('module')
parser.add_argument('--characters',type=int,default=1800)
args=parser.parse_args()
root=Path(__file__).resolve().parents[2]
path=root/'.lake/build/certification/logs'/Path(*args.module.split('.')).with_suffix('.log')
count=0
for line in path.read_text(encoding='utf8').splitlines():
    try:
        entry=json.loads(line)
    except json.JSONDecodeError:
        print('Incomplete log line; compilation is still writing output.')
        continue
    if entry.get('severity')=='error':
        count+=1
        message=entry.get('data','')
        print('line',entry.get('pos',{}).get('line'),message[:args.characters])
        if len(message)>args.characters:
            print('[remaining goal omitted; full data retained in',path.relative_to(root),']')
print('Errors:',count)
