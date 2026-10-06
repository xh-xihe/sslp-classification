"""Revalidate one explicit weighted-degree qualification without transferring historical coverage."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims

D = ROOT / 'artifacts/manuscript-certification-20261005'
A = ROOT / 'archive/reviews/20261005-before-weighted-graph-qualification'
OLD_SI = '1ffc6d2a59dd413f5e1ee70e67f01b8ce928f8ecdb85ca888e449669b56d4039'
MAIN = 'fb694c01b1144ce99d9a6d602c1a2629269bdd4c906a95fe9654f43f54a70958'

def read(p):
    return json.loads(p.read_text(encoding='utf8'))

def save(p, value):
    p.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf8', newline='\n')

def sha(value):
    return hashlib.sha256(value).hexdigest()

def main():
    ledger_path = ROOT / 'results/paper-claims-20261003.json'
    old = read(ledger_path)
    assert old['sources']['documents/20261003/supplementary.tex'] == OLD_SI
    assert sha((ROOT / 'documents/20261003/main.tex').read_bytes()) == MAIN
    raw = (ROOT / 'documents/20261003/supplementary.tex').read_bytes()
    needle = b'It remains to show that a graph with weighted degree $1/4$ at every vertex cannot support'
    prior = b'It remains to show that a graph with no isolated vertex cannot support'
    assert raw.count(needle) == 1
    before = raw.replace(needle, prior)
    if sha(before) != OLD_SI:
        # Preserve the author's CRLF convention on the two edited lines.
        candidate = before.replace(b'\r\n', b'\n').replace(b'\n', b'\r\n')
        assert sha(candidate) == OLD_SI
        before = candidate
        raw = candidate.replace(prior, needle)
        (ROOT / 'documents/20261003/supplementary.tex').write_bytes(raw)
    assert sha(before) == OLD_SI
    old_lines, new_lines = before.decode('utf8').splitlines(), raw.decode('utf8').splitlines()
    changed = [i + 1 for i, (a, b) in enumerate(zip(old_lines, new_lines)) if a != b]
    assert len(old_lines) == len(new_lines) and changed == [15214]
    fresh = paper_claims.snapshot(old, sources=paper_claims.sources_for_version('20261003'))
    assert len(fresh['claims']) == len(old['claims']) == 1830
    for a, b in zip(old['claims'], fresh['claims']):
        for key in ('id', 'source', 'kind', 'line', 'end_line', 'statement_sha256'):
            assert a[key] == b[key], (key, a['id'])
        for key in ('status', 'lean_declarations', 'review'):
            b[key] = a[key]
        if b['review']:
            b['review'] += ' Context rechecked with the explicit weighted-degree hypothesis in orbit 17; see weighted-graph-context-revalidation.json.'
    fresh['prose_review'] = old['prose_review']
    paper_claims.validate(fresh, sources=paper_claims.sources_for_version('20261003'))
    prose = read(ROOT / 'results/prose-review-20261003.json')
    assert prose['sources_sha256'] == old['sources']
    repaired_contexts = []
    for row in prose['assertions']:
        lines = new_lines if row['source'] == 'supplementary.tex' else (ROOT / 'documents/20261003/main.tex').read_text(encoding='utf8').splitlines()
        context = '\n'.join(lines[row['line'] - 1:row['end_line']])
        if sha(context.encode()) != row['context_sha256_lf']:
            assert (row['source'], row['line'], row['end_line']) == ('supplementary.tex', 12122, 12123)
            prior_context = context.replace('For a nonempty mask', 'For a mask')
            assert sha(prior_context.encode()) == row['context_sha256_lf']
            repaired_contexts.append({'source': row['source'], 'line': row['line'], 'end_line': row['end_line'],
                                     'prior_context_sha256_lf': row['context_sha256_lf'], 'context_sha256_lf': sha(context.encode()),
                                     'reason': 'Revalidate the overlapping convex-face block after the earlier nonempty-mask qualification; its general convex-hull theorem remains applicable.'})
            row['context_sha256_lf'] = sha(context.encode())
        assert sha(context.encode()) == row['context_sha256_lf'], row['line']
    inputs = ['results/paper-claims-20261003.json', 'results/prose-review-20261003.json',
              'results/errata-20261003.json', 'results/orbit-manifest-20261003.json',
              'results/correspondence-candidates-20261005.json', 'tools/verification/review_sources_20261005.py']
    assert not A.exists()
    A.mkdir(parents=True)
    archived = []
    for relative in inputs:
        data = (ROOT / relative).read_bytes()
        destination = A / Path(relative).name
        destination.write_bytes(data)
        archived.append({'path': relative, 'archive': destination.relative_to(ROOT).as_posix(), 'sha256': sha(data)})
    save(ledger_path, fresh)
    prose['sources_sha256'] = fresh['sources']
    prose['method'] += ' The orbit-17 graph argument now explicitly retains its preceding weighted-degree hypothesis; all unchanged assertion and reviewed prose contexts were rechecked.'
    save(ROOT / 'results/prose-review-20261003.json', prose)
    for relative in ('results/errata-20261003.json', 'results/correspondence-candidates-20261005.json'):
        record = read(ROOT / relative)
        assert record['sources_sha256'] == old['sources']
        record['sources_sha256'] = fresh['sources']
        if 'method' in record:
            record['method'] += ' Orbit 17 now expressly retains weighted degree one quarter at every vertex; no displayed assertion changed.'
        save(ROOT / relative, record)
    manifest = read(ROOT / 'results/orbit-manifest-20261003.json')
    assert manifest['_paper']['sources_sha256'] == old['sources']
    manifest['_paper']['sources_sha256'] = fresh['sources']
    save(ROOT / 'results/orbit-manifest-20261003.json', manifest)
    p = ROOT / 'tools/verification/review_sources_20261005.py'
    value = p.read_text(encoding='utf8')
    assert value.count(OLD_SI) == 1
    p.write_text(value.replace(OLD_SI, sha(raw)), encoding='utf8', newline='\n')
    for p in (D / 'run.json', ROOT / 'results/repository-status.json'):
        record = read(p)
        assert record['sources_sha256'] == old['sources']
        record['sources_sha256'] = fresh['sources']
        record['current_context_revalidation'] = {'record': 'artifacts/manuscript-certification-20261005/weighted-graph-context-revalidation.json', 'status': 'fresh_type_and_axiom_evidence_pending'}
        save(p, record)
    save(D / 'weighted-graph-context-revalidation.json', {
        'schema': 1, 'date': '2026-10-05', 'prior_sources_sha256': old['sources'],
        'sources_sha256': fresh['sources'], 'changed_lines': changed,
        'main_bytes_unchanged': True, 'all_1830_statement_bytes_and_locations_unchanged': True,
        'reason': 'The no-isolated-vertex condition alone permits stars. The actual physical graph has weighted degree one quarter at every vertex; that hypothesis is essential in the final star case and is now explicit.',
        'archived_records': archived, 'repaired_overlapping_context_bindings': repaired_contexts,
        'fresh_type_inspection': 'pending', 'fresh_axiom_audit': 'pending'})
    print('Revalidated 1830 unchanged statements; main frozen; SI SHA:', sha(raw))

if __name__ == '__main__':
    main()
