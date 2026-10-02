"""Export the existing input-bound certificate bundle; never mint kernel status."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / 'apps/sslp-explorer'
DEFAULT_BUNDLE = ROOT / 'tmp/sslp-explorer/class36-bundle-v2.zip'

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=DEFAULT_BUNDLE)
    parser.add_argument('--check', action='store_true', help='Check the published snapshot without writing')
    args = parser.parse_args()
    payload = args.bundle.read_bytes()
    with zipfile.ZipFile(args.bundle) as archive:
        manifest = json.loads(archive.read('bundle-manifest.json'))
        declared = manifest['files_sha256']
        assert len(set(archive.namelist())) == len(archive.namelist()), 'duplicate ZIP members'
        assert set(archive.namelist()) == set(declared) | {'bundle-manifest.json'}, 'unlisted ZIP members'
        for name, expected in declared.items():
            assert sha(archive.read(name)) == expected, f'bundle integrity: {name}'
        instance = json.loads(archive.read('case.json'))
        exact = json.loads(archive.read('exact.json'))
        evidence = json.loads(archive.read('evidence.json'))
        canonical = json.dumps(instance, sort_keys=True, ensure_ascii=False, separators=(',', ':'), allow_nan=False).encode()
        input_hash = sha(canonical)
        assert input_hash == manifest['input_sha256'] == exact['input_sha256'] == evidence['input_sha256'] == evidence['kernel']['input_sha256']
        assert sha(archive.read('Certificate.lean')) == evidence['kernel']['certificate_sha256']
        assert sha(archive.read('exact.json')) == evidence['exact_report_sha256']
        assert evidence['kernel']['status'] == 'passed' and not evidence['full_manuscript_certified']
        assert set(evidence['kernel']['axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
        for name, expected in evidence['tooling_sha256'].items():
            assert sha((ROOT / name).read_bytes()) == expected, f'tooling changed: {name}'
        for module, expected in evidence['kernel']['source_sha256'].items():
            path = ROOT / (module.replace('.', '/') + '.lean')
            assert sha(path.read_bytes()) == expected, f'proof changed: {module}'
        for name, expected in instance['paper']['sources_sha256'].items():
            assert sha((ROOT / name).read_bytes()) == expected, f'manuscript changed: {name}'
        generated = {
            'app/data/class36.json': json.dumps({'instance':instance, 'exact':exact, 'evidence':evidence}, ensure_ascii=False, indent=2).encode() + b'\n',
            'public/downloads/class36-verification.zip': payload,
            **{f'public/downloads/{name}': archive.read(name) for name in ('case.json','Certificate.lean','evidence.json')},
            'public/downloads/integrity.json': json.dumps({'input_sha256':input_hash, 'bundle_sha256':sha(payload), 'certificate_sha256':evidence['kernel']['certificate_sha256'], 'scope':'existing single-instance evidence; not a new Lean run'}, indent=2).encode() + b'\n',
        }
        for name, content in generated.items():
            dest = SITE / name
            if args.check:
                assert dest.read_bytes() == content, f'site snapshot mismatch: {name}'
            else:
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(content)
    print(json.dumps({'status':'checked' if args.check else 'exported','files':len(generated),'input_sha256':input_hash,'bundle_sha256':sha(payload)}))

if __name__ == '__main__':
    main()
