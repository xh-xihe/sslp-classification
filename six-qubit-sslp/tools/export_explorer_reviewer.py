"""Package the unchanged case ZIP with a standalone reproduction launcher."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT/'apps/sslp-explorer'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    folder = SITE/'public/downloads'
    bundle = (folder/'class36-verification.zip').read_bytes()
    integrity = json.loads((folder/'integrity.json').read_text())
    sha = lambda b: hashlib.sha256(b).hexdigest()
    assert sha(bundle) == integrity['bundle_sha256'], 'original bundle changed'
    with zipfile.ZipFile(io.BytesIO(bundle)) as archive:
        manifest = json.loads(archive.read('bundle-manifest.json'))
        assert len(set(archive.namelist())) == len(archive.namelist())
        assert set(archive.namelist()) == set(manifest['files_sha256']) | {'bundle-manifest.json'}
        for name, expected in manifest['files_sha256'].items():
            assert sha(archive.read(name)) == expected, name
    guide = (ROOT/'tools/explorer/REPRODUCE.md').read_text(encoding='utf-8').replace('EXPECTED_BUNDLE_SHA256', sha(bundle)).encode()
    payloads = {'README.md':guide, 'sslp_reproduce.py':(ROOT/'tools/sslp_reproduce.py').read_bytes(),
                'class36-verification.zip':bundle}
    payloads['SHA256SUMS'] = ''.join(f'{sha(data)}  {name}\n' for name,data in sorted(payloads.items())).encode()
    output = io.BytesIO()
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in sorted(payloads.items()):
            info = zipfile.ZipInfo(name, date_time=(2026,9,26,0,0,0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    kit = output.getvalue()
    exported = {'class36-reviewer-kit.zip':kit,'reproduction-guide.md':guide,
                'reviewer-integrity.json':(json.dumps({'schema':'sslp.reviewer-kit.v1',
                    'kit_sha256':sha(kit),'bundle_sha256':sha(bundle),'launcher_sha256':sha(payloads['sslp_reproduce.py']),
                    'files_sha256':{name:sha(data) for name,data in payloads.items()},
                    'scope':'reproduction utilities plus unchanged single-instance evidence; not a new kernel run'},indent=2)+'\n').encode()}
    for name, data in exported.items():
        path = folder/name
        if args.check:
            assert path.read_bytes() == data, 'stale reviewer asset: '+name
        else:
            path.write_bytes(data)
    print(json.dumps({'status':'checked' if args.check else 'exported','kit_sha256':sha(kit),'bundle_unchanged':True}))


if __name__ == '__main__':
    main()
