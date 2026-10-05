"""Publish current-source locators for unfinished review; never infer proof gaps."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
import paper_claims
from review_sources_20261005 import SOURCES

def main():
    ledger = json.loads((ROOT/'results/paper-claims-20261003.json').read_text(encoding='utf8'))
    paper_claims.validate(ledger,sources=paper_claims.sources_for_version('20261003'))
    if ledger['sources'] != SOURCES:
        raise ValueError('Current-source review bindings changed')
    section_ranges = {}
    for relative in SOURCES:
        lines = (ROOT/relative).read_text(encoding='utf8').splitlines()
        starts = [i for i,line in enumerate(lines,1) if re.match(r'^\s*\\section\{',line)]
        section_ranges[relative] = [(n,start) for n,start in enumerate(starts,1)]
    rows = []
    for claim in ledger['claims']:
        if claim['status'] not in {'partial','unreviewed'}:
            continue
        section = max((n for n,start in section_ranges[claim['source']]
                       if start<=claim['line']),default=0)
        rows.append({**{k:claim[k] for k in ('id','source','kind','line','end_line',
                                            'statement_sha256','status','lean_declarations')},
                     'section_number':section,
                     'work_scope':('author-held frozen statement' if claim['status']=='partial'
                                   else 'pending statement/context/type review; not a finding of falsehood')})
    prose = json.loads((ROOT/'results/prose-review-20261003.json').read_text(encoding='utf8'))
    payload = {'schema':1,'date':'2026-10-05','sources_sha256':SOURCES,
               'scope':'Current unfinished semantic correspondence; compiled final results do not discharge intermediate statements.',
               'claim_status_counts':dict(sorted(Counter(c['status'] for c in ledger['claims']).items())),
               'pending_by_source_section':dict(sorted(Counter(
                   Path(c['source']).name+':'+str(c['section_number']) for c in rows).items())),
               'pending_assertions':rows,
               'prose_review':{'status':prose['status'],'reviewed_blocks':len(prose['assertions']),
                               'record':'results/prose-review-20261003.json'},
               'held_main_errata':'notes/main-errata-hold-20261003.md',
               'fully_kernel_manuscript_certification':'not_complete'}
    path = ROOT/'artifacts/manuscript-certification-20261005/remaining-obligations.json'
    path.write_text(json.dumps(payload,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Remaining current assertion obligations:',len(rows))
    print('Pending SI by section:',json.dumps({k:v for k,v in payload['pending_by_source_section'].items()
                                             if k.startswith('supplementary')},sort_keys=True))

if __name__ == '__main__':
    main()
