"""Version-bound manuscript acceptance inputs; never inherit review status."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_VERSION = '20260908'


def version(value):
    if not re.fullmatch(r'[0-9]{8}', value):
        raise ValueError('paper version must be an eight-digit date')
    return value


def paths(paper_version=DEFAULT_VERSION, root=ROOT):
    v, root = version(paper_version), Path(root)
    return {
        'source_dir': root / 'documents' / v,
        'ledger': root / 'results' / f'paper-claims-{v}.json',
        'named': root / 'results' / f'named-results-{v}.md',
        'prose': root / 'results' / f'prose-review-{v}.json',
        'prose_doc': root / 'results' / f'prose-review-{v}.md',
        'errata': root / 'results' / f'errata-{v}.json',
        'manifest': (root / 'tools/manifest.json' if v == DEFAULT_VERSION else
                     root / 'results' / f'orbit-manifest-{v}.json'),
    }


def source_hashes(paper_version, root=ROOT, source_dir=None):
    v, root = version(paper_version), Path(root)
    directory = Path(source_dir) if source_dir else paths(v, root)['source_dir']
    return {f'documents/{v}/{name}.tex': hashlib.sha256(
        (directory / f'{name}.tex').read_bytes()).hexdigest()
        for name in ('main', 'supplementary')}


def validate_review(record, paper_version, root=ROOT, require_complete=False, source_dir=None):
    v = version(paper_version)
    if record.get('paper_version') != v or record.get('sources_sha256') != source_hashes(v, root, source_dir):
        raise ValueError('review version or manuscript hashes do not match selected release')
    if record.get('status') not in {'unreviewed', 'partial', 'covered'}:
        raise ValueError('invalid review status')
    if not record.get('method', '').strip():
        raise ValueError('missing review method/scope')
    context_lines = {}
    for row in record['assertions']:
        if 'quote' in row:
            raise ValueError('review record must not contain a manuscript quote field')
        if row.get('source') not in {'main.tex', 'supplementary.tex'} or not row.get('reason', '').strip():
            raise ValueError('invalid prose review assertion')
        if row.get('kind') not in {'gap', 'covered', 'tracked', 'nonmath'}:
            raise ValueError('invalid prose review classification')
        if row['kind'] == 'covered' and not row.get('declarations'):
            raise ValueError('covered prose has no Lean declarations')
        if 'context_sha256_lf' in row:
            directory = Path(source_dir) if source_dir else paths(v, root)['source_dir']
            if row['source'] not in context_lines:
                context_lines[row['source']] = (directory / row['source']).read_text(encoding='utf-8').splitlines()
            lines = context_lines[row['source']]
            start, end = row['line'], row.get('end_line', row['line'])
            if not 1 <= start <= end <= len(lines):
                raise ValueError('prose context has an invalid line range')
            context = '\n'.join(lines[start - 1:end]).encode('utf-8')
            if hashlib.sha256(context).hexdigest() != row['context_sha256_lf']:
                raise ValueError('prose context changed: ' + row['source'] + ':' + str(start))
    if require_complete and (record['status'] != 'covered' or not record['assertions'] or
                             any(a['kind'] == 'gap' for a in record['assertions'])):
        raise ValueError('selected release prose review is not complete')


def binding(paper_version, root=ROOT, source_dir=None):
    """Bind every release-specific input before expensive verification runs.

    The legacy mathematical no-go/moment tools share orbit data. Explicitly
    require identical numeric data and module mappings, not identical paper
    provenance; future data changes must migrate those tools before acceptance.
    """
    v, root = version(paper_version), Path(root)
    p = paths(v, root)
    hashes = source_hashes(v, root, source_dir)
    ledger = json.loads(p['ledger'].read_text(encoding='utf-8'))
    if ledger['sources'] != hashes:
        raise ValueError('--source-dir differs from the selected release manuscripts (ledger source hashes differ)'
                         if source_dir else 'selected release ledger source hashes differ')
    manifest = json.loads(p['manifest'].read_text(encoding='utf-8'))
    if manifest['_paper']['sources_sha256'] != hashes:
        raise ValueError('selected release orbit manifest source hashes differ')
    shared = json.loads((root / 'tools/manifest.json').read_text(encoding='utf-8'))
    data = lambda m: {k: val for k, val in m.items() if k != '_paper'}
    if data(manifest) != data(shared):
        raise ValueError('selected orbit data differ from shared mathematical gates; migrate gates first')
    files = [p['ledger'], p['manifest'], p['prose'], p['named'], p['prose_doc']]
    if v != DEFAULT_VERSION:
        validate_review(json.loads(p['prose'].read_text(encoding='utf-8')), v, root, source_dir=source_dir)
        errata = json.loads(p['errata'].read_text(encoding='utf-8'))
        if errata.get('paper_version') != v or errata.get('sources_sha256') != hashes:
            raise ValueError('errata review is not bound to the selected release')
        if errata.get('status') not in {'unreviewed', 'partial', 'covered'} or not errata.get('issues'):
            raise ValueError('missing errata dispositions')
        files.append(p['errata'])
    else:
        files.append(root / 'results/errata-20260908.md')
    return {'paper_version': v, 'sources_sha256': hashes,
            'inputs_sha256': {f.relative_to(root).as_posix(): hashlib.sha256(f.read_bytes()).hexdigest()
                              for f in files},
            'shared_orbit_data_equal': True}


def check_errata(paper_version, root=ROOT, source_dir=None):
    v = version(paper_version)
    if v == DEFAULT_VERSION:
        return True, 'historical errata are tracked by the historical claims/prose gates'
    record = json.loads(paths(v, root)['errata'].read_text(encoding='utf-8'))
    if record.get('paper_version') != v or record.get('sources_sha256') != source_hashes(v, root, source_dir):
        raise ValueError('stale or wrong-version errata review')
    if not record.get('issues'):
        raise ValueError('missing errata dispositions')
    pending = [r['id'] for r in record['issues']
               if r.get('status') not in {'resolved_in_text', 'not_applicable'}]
    if record.get('status') != 'covered' or pending:
        return False, 'errata review incomplete; outstanding: ' + ', '.join(pending)
    return True, 'all recorded errata have reviewed dispositions for this release'
