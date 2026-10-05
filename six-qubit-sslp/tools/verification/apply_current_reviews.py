"""Persist explicit current-source decisions, rejecting changed manuscript contexts."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
from review_core_claims_20261003 import SOURCES


def apply_reviews(source, groups, evidence_name, apply=False):
    reviews = {}
    for group in groups:
        ids, declarations, review = group[:3]
        status = group[3] if len(group) == 4 else 'covered'
        for ident in ids:
            key = source + '.tex:' + ident
            if key in reviews:
                raise ValueError('Duplicate review: ' + key)
            reviews[key] = (declarations, review, status)
    path = ROOT / 'results/paper-claims-20261003.json'
    ledger = json.loads(path.read_text(encoding='utf8'))
    paper_claims.validate(ledger, sources=paper_claims.sources_for_version('20261003'))
    if ledger['sources'] != SOURCES:
        raise ValueError('The reviewed manuscript context changed')
    decisions = []
    for entry in ledger['claims']:
        if entry['id'] not in reviews:
            continue
        declarations, review, status = reviews[entry['id']]
        if not review or (status == 'covered' and not declarations):
            raise ValueError('Missing review/proof roots: ' + entry['id'])
        entry.update(status=status, lean_declarations=declarations,
                     review='20261003 current-source review (2026-10-04): ' + review)
        decisions.append({k: entry[k] for k in
                         ('id', 'statement_sha256', 'status', 'lean_declarations', 'review')})
    if len(decisions) != len(reviews):
        raise ValueError('Missing reviewed statement: ' + str(set(reviews) - {e['id'] for e in decisions}))
    if apply:
        path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        (ROOT / 'artifacts/orbit-certification-20261003' / (evidence_name + '.json')).write_text(
            json.dumps({'schema': 1, 'sources': SOURCES, 'claims': decisions},
                       ensure_ascii=False, indent=2) + '\n', encoding='utf8')
    print('Reviewed current-source claims:', len(decisions))
