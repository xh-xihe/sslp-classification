"""Check complete current SI correspondence separately from frozen main errata.

This checks integrity and the explicit semantic review record. Kernel build,
actual declaration types and transitive axioms remain independent gates.
"""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
import paper_release
from review_sources_20261005 import SOURCES
from review_running_contexts_20261005 import COUNTS, ORIGIN, inventory

def read(p):
    return json.loads(p.read_text(encoding='utf8'))

def main():
    ledger = read(ROOT / 'results/paper-claims-20261003.json')
    prose = read(ROOT / 'results/prose-review-20261003.json')
    paper_claims.validate(ledger, sources=paper_claims.sources_for_version('20261003'))
    paper_release.validate_review(prose, '20261003', ROOT)
    assert ledger['sources'] == SOURCES
    si = [c for c in ledger['claims'] if c['source'].endswith('/supplementary.tex')]
    assert len(si) == 1625
    assert sum(c['status'] == 'covered' and bool(c['lean_declarations']) for c in si) == 1622
    assert sum(c['status'] == 'expository' and bool(c['review']) for c in si) == 3
    assert ledger['prose_review']['documents/20261003/supplementary.tex']['status'] == 'covered'
    assert prose['source_status']['supplementary.tex'] == 'covered'
    assert not any(r['source'] == 'supplementary.tex' and r['kind'] == 'gap' for r in prose['assertions'])
    current = inventory(ledger, prose)
    key = lambda r: (r['source'], r['line'], r['end_line'])
    reviewed = [r for r in prose['assertions'] if r.get('origin') == ORIGIN]
    assert len(reviewed) == sum(COUNTS.values()) and {key(r) for r in current} == {key(r) for r in reviewed}
    binding = read(ROOT / 'artifacts/manuscript-certification-20261005/complete-running-context-type-binding-v1.json')
    assert binding['sources_sha256'] == SOURCES and binding['reading_blocks'] == COUNTS
    assert binding['reviewed_rows'] == reviewed
    p = ROOT / binding['type_evidence']
    assert hashlib.sha256(p.read_bytes()).hexdigest() == binding['type_evidence_sha256']
    types = read(p)
    assert types['sources_sha256'] == SOURCES
    inspected = {r['name'] for r in types['declarations']}
    required = {n for c in si for n in c['lean_declarations']} | {
        n for r in prose['assertions'] if r['source'] == 'supplementary.tex' for n in r.get('declarations', [])}
    assert not required - inspected
    assert sum(r['kind'] == 'gap' for r in prose['assertions']) == 5
    print('PASS: 1622 SI mathematical assertions, three scope-only remarks and 1622 remaining running blocks have current correspondence; the five frozen main issues remain explicit')

if __name__ == '__main__':
    main()
