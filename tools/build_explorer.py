#!/usr/bin/env python3
"""Bundle the committed proof navigation into a standalone, offline HTML explorer.

Source catalog, curated proof index and version-bound status remain authoritative.
No manuscript files are read. This tool adds navigation, not coverage decisions.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
INPUTS = ('results/proof-modules.json', 'results/repository-status.json', 'docs/proof-index.md')
REPOSITORY = 'https://github.com/xh-xihe/sslp-classification'
ALLOWED_LIBRARIES = ('SS', 'QECC', 'MainTheory', 'SixQubit', 'Orbit2')


def orbit_tags(text):
    values = set()
    for group in re.findall(r'\bOrbits?\s+([0-9][0-9, /and]*)', text, flags=re.I):
        values.update(map(int, re.findall(r'\d+', group)))
    values.update(map(int, re.findall(r'(?:^|[/\.])(?:Open)?Orbit(\d+)(?=[A-Z/\.]|$)', text)))
    return sorted(values)


def parse_guides(text, paths):
    section, rows = '', []
    for line in text.splitlines():
        if line.startswith('## '):
            section = line[3:].strip()
        if section not in ('Main-text theory', 'Supplementary material') or not line.startswith('|'):
            continue
        links = list(dict.fromkeys(re.findall(r'\]\(\.\./([A-Za-z0-9_./-]+\.lean)\)', line)))
        if not links:
            continue
        missing = set(links) - set(paths)
        if missing:
            raise ValueError('Proof guide names uncataloged sources: ' + ', '.join(sorted(missing)))
        title = line.split('|')[1].strip()
        rows.append({'id':'guide:' + hashlib.sha256((title + '|'.join(links)).encode()).hexdigest()[:12],
                     'title':title, 'section':section, 'paths':links,
                     'orbits':sorted({n for value in [title] + links for n in orbit_tags(value)})})
    if not rows:
        raise ValueError('No curated proof guides found; refusing an empty explorer')
    return rows


def payload(root=ROOT):
    root = Path(root)
    catalog = json.loads((root / INPUTS[0]).read_text(encoding='utf-8'))
    status = json.loads((root / INPUTS[1]).read_text(encoding='utf-8'))
    modules = catalog['modules']
    paths = {row['path'] for row in modules}
    if len(paths) != len(modules) or len(modules) != catalog['module_count']:
        raise ValueError('Source inventory count or uniqueness mismatch')
    if status['active_lean_modules'] != len(modules):
        raise ValueError('Status and source inventory name different module counts')
    for row in modules:
        path = Path(row['path'])
        if path.is_absolute() or '..' in path.parts or row['library'] not in ALLOWED_LIBRARIES:
            raise ValueError('Unsafe or unknown source path: ' + row['path'])
        if not (root / path).is_file():
            raise ValueError('Missing catalog source: ' + row['path'])
    guides = parse_guides((root / INPUTS[2]).read_text(encoding='utf-8'), paths)
    topics = sorted({row['topic'] for row in modules})
    libraries = list(ALLOWED_LIBRARIES)
    packed = [[row['path'], libraries.index(row['library']), topics.index(row['topic']), orbit_tags(row['path'])] for row in modules]
    endpoints = {
        'MainTheory/Orbit2FullImage.lean': {
            'declaration':'MainTheory.Orbit2FullImage.directory_image', 'status_key':'orbit2_full_image',
            'resources':[['Exact quartic data','results/orbit2-kernel/gram-blocks.json'],
                         ['Rational matrix reconstruction','tools/certificates/orbit2_exact_certificate.py']]},
        'MainTheory/Orbit3FullImage.lean': {
            'declaration':'MainTheory.Orbit3FullImage.directory_image', 'status_key':'orbit3_full_image',
            'resources':[['Exact sextic certificate','results/orbit3-kernel/certificate.json'],
                         ['Scalar dual certificates','results/orbit3-kernel/scalar-certificate.json'],
                         ['Rational sextic reconstruction','tools/certificates/orbit3_exact_sextic_certificate.py']]}
    }
    for path, endpoint in endpoints.items():
        if not any(path in guide['paths'] for guide in guides):
            raise ValueError('Missing curated full-image guide: ' + path)
        if path not in paths or status.get(endpoint['status_key']) != 'kernel_checked':
            raise ValueError('Full-image endpoint is absent from the recorded proof status')
        if not re.search(r'\btheorem\s+directory_image\b', (root / path).read_text(encoding='utf-8')):
            raise ValueError('Full-image declaration no longer exists')
        for _, resource in endpoint['resources']:
            if not (root / resource).is_file():
                raise ValueError('Missing exact certificate resource: ' + resource)
        del endpoint['status_key']
    evidence = [
        ['Proof acceptance','artifacts/manuscript-certification-20261005/proof-acceptance-16227.json'],
        ['Transitive axiom audit','artifacts/manuscript-certification-20261005/axioms-9375.json'],
        ['Publication source binding','artifacts/manuscript-certification-20261005/publication-binding-16227.json'],
        ['Version-specific correspondence','docs/manuscript-correspondence.md']]
    for _, path in evidence:
        if not (root / path).is_file():
            raise ValueError('Missing acceptance evidence: ' + path)
    sources = {path:hashlib.sha256((root / path).read_bytes().replace(b'\r\n', b'\n')).hexdigest() for path in INPUTS}
    return {'schema':1,'repository':REPOSITORY,'branch':'main','source_hashes_lf':sources,
            'libraries':libraries,'topics':topics,'modules':packed,'guides':guides,'endpoints':endpoints,
            'evidence':evidence,'library_counts':dict(Counter(row['library'] for row in modules)),
            'status':{key:status[key] for key in ('paper_version','date','active_lean_modules','axiom_roots',
                'held_main_issues','open_enumerator_images','si_fully_kernel_correspondence')},
            'default_selected_path':'MainTheory/Orbit2FullImage.lean'}


def script_json(data):
    # JSON is an inert script element; escaped delimiters cannot end it early.
    return json.dumps(data, ensure_ascii=False, separators=(',', ':')).replace('&', '\\u0026').replace('<', '\\u003c').replace('>', '\\u003e').replace('\u2028', '\\u2028').replace('\u2029', '\\u2029')


def render(root=ROOT):
    root = Path(root)
    source = root / 'tools/proof_explorer'
    template = (source / 'template.html').read_text(encoding='utf-8')
    replacements = {'__STYLE__':(source / 'explorer.css').read_text(encoding='utf-8'),
                    '__SCRIPT__':(source / 'explorer.js').read_text(encoding='utf-8'),
                    '__DATA__':script_json(payload(root))}
    for token, value in replacements.items():
        if template.count(token) != 1:
            raise ValueError('Expected one template marker: ' + token)
        template = template.replace(token, value)
    return template


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args(argv)
    content = render(args.root)
    target = args.root / 'docs/explorer/index.html'
    if args.check:
        if not target.is_file() or target.read_text(encoding='utf-8') != content:
            raise SystemExit('FAIL: regenerate with python tools/build_explorer.py')
    else:
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_text(content,encoding='utf-8',newline='\n')
    print('PASS: standalone proof explorer matches the catalog, curated index, and recorded status')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
