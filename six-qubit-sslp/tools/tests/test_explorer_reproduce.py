"""Portable bundle preparation, diagnostic boundaries and rejected-proof reports."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import stat
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import uuid
import warnings
import zipfile

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
from explorer import class36
import sslp_explorer
import sslp_reproduce as reproduce
import sslp_worker


class Workspace(unittest.TestCase):
    def setUp(self):
        self.base = (TOOLS.parent/'tmp/reproduce-tests').resolve()
        self.root = self.base/uuid.uuid4().hex
        self.root.mkdir(parents=True)
        self.addCleanup(self.cleanup)
    def cleanup(self):
        assert self.root.resolve().is_relative_to(self.base)
        shutil.rmtree(self.root)


class BundleTests(Workspace):
    def setUp(self):
        super().setUp()
        run = self.root/'run'
        sslp_explorer.verify_case(class36.example(), run)
        self.archive = sslp_explorer.export_bundle(run, self.root/'source')

    def rewrite(self, edit):
        with zipfile.ZipFile(self.archive) as z:
            files = [(i, z.read(i)) for i in z.infolist()]
        edit(files)
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', UserWarning)
            with zipfile.ZipFile(self.archive, 'w') as z:
                for name, payload in files:
                    z.writestr(name, payload)

    def test_fresh_extraction_preserves_every_file_without_imported_caches(self):
        destination = self.root/'prepared'
        result = reproduce.prepare(self.archive, destination, reproduce.digest(self.archive))
        self.assertEqual(result['zip_sha256'], reproduce.digest(self.archive))
        self.assertTrue(sslp_explorer.check_bundle(destination)['hashes_match'])
        self.assertFalse((destination/'.lake').exists())
        with self.assertRaisesRegex(ValueError, 'new directory'):
            reproduce.prepare(self.archive, destination, reproduce.digest(self.archive))

    def test_wrong_zip_hash_does_not_create_destination(self):
        with self.assertRaisesRegex(ValueError, 'ZIP SHA'):
            reproduce.prepare(self.archive, self.root/'prepared', '0'*64)
        self.assertFalse((self.root/'prepared').exists())

    def test_traversal_and_unlisted_members_rejected_before_writes(self):
        self.rewrite(lambda files: files.append(('../outside', b'no')))
        with self.assertRaisesRegex(ValueError, 'unsafe ZIP'):
            reproduce.prepare(self.archive, self.root/'prepared', reproduce.digest(self.archive))
        self.assertFalse((self.root/'prepared').exists())
        self.assertFalse((self.root/'outside').exists())

    def test_symlink_rejected(self):
        info = zipfile.ZipInfo('link')
        info.create_system = 3
        info.external_attr = (stat.S_IFLNK | 0o777) << 16
        self.rewrite(lambda files: files.append((info, b'../outside')))
        with self.assertRaisesRegex(ValueError, 'unsafe ZIP'):
            reproduce.prepare(self.archive, self.root/'prepared', reproduce.digest(self.archive))

    def test_case_collision_rejected_on_every_platform(self):
        self.rewrite(lambda files: files.append(('CASE.json', b'{}')))
        with self.assertRaisesRegex(ValueError, 'case-colliding'):
            reproduce.prepare(self.archive, self.root/'prepared', reproduce.digest(self.archive))

    def test_modified_payload_with_old_manifest_is_rejected(self):
        def edit(files):
            files[:] = [(name, content+b' ' if name.filename == 'case.json' else content) for name,content in files]
        self.rewrite(edit)
        with self.assertRaisesRegex(ValueError, 'member hash mismatch'):
            reproduce.prepare(self.archive, self.root/'prepared', reproduce.digest(self.archive))

    def test_unsafe_package_url_or_revision_is_not_executed(self):
        directory = self.root/'source'
        original = json.loads((directory/'lake-manifest.json').read_text())
        for change in ({'url':'file:///private'}, {'rev':'main'}, {'name':'../outside'}, {'subDir':'other'}):
            data = copy.deepcopy(original)
            data['packages'][0].update(change)
            reproduce.write_json(directory/'lake-manifest.json', data)
            with patch.object(reproduce, 'command') as command, self.assertRaises(ValueError):
                reproduce.fetch_dependencies(directory)
            command.assert_not_called()

    def test_failed_readiness_does_not_start_proof_or_create_success_report(self):
        directory = self.root/'source'
        with patch.object(reproduce, 'doctor', return_value={'ready':False}), patch.object(reproduce, 'command') as command:
            with self.assertRaisesRegex(ValueError, 'not ready'):
                reproduce.run_verifier(directory, 'fresh-run')
            command.assert_not_called()
        self.assertFalse((directory/'fresh-run-reproduction.json').exists())

    def test_manifest_release_tag_is_fetched_and_bound_to_pinned_commit(self):
        directory = self.root/'source'
        rev = 'a'*40
        package = {'name':'proofwidgets','type':'git','subDir':None,'url':'https://github.com/leanprover-community/ProofWidgets4',
                   'rev':rev,'inputRev':'v0.0.85'}
        reproduce.write_json(directory/'lake-manifest.json', {'packagesDir':'.lake/packages','packages':[package]})
        fetched = []
        def command(args, *rest, **kwargs):
            fetched.append(args)
        def lookup(args, **kwargs):
            if 'refs/tags/v0.0.85^{commit}' in args:
                found = any('refs/tags/v0.0.85:refs/tags/v0.0.85' in c for c in fetched)
                return SimpleNamespace(returncode=0 if found else 1, stdout=rev if found else '')
            self.fail('unexpected Git lookup')
        with patch.object(reproduce, 'command', side_effect=command), patch.object(reproduce.subprocess, 'run', side_effect=lookup), patch.object(reproduce.platform, 'platform', return_value='test fixture'):
            reproduce.fetch_dependencies(directory)
        tag_fetch = next(c for c in fetched if 'refs/tags/v0.0.85:refs/tags/v0.0.85' in c)
        self.assertIn('--no-tags',tag_fetch)
        self.assertEqual(fetched[-1],['lake','exe','cache','get'])


class FailedProofTests(Workspace):
    def test_failed_and_timed_out_lean_preserve_report_without_success_bundle(self):
        for status in ('failed', 'timeout'):
            with self.subTest(status=status):
                directory = self.root/status
                directory.mkdir()
                data = class36.example()
                reproduce.write_json(directory/'request.json', {'kind':'lean','input':data})
                def verify(supplied, output, **kwargs):
                    output.mkdir()
                    exact = class36.exact_checks(supplied)
                    evidence = {'passed_requested_checks':False,'kernel':{'status':status,'error':'test fixture'}}
                    reproduce.write_json(output/'exact.json', exact)
                    reproduce.write_json(output/'evidence.json', evidence)
                    return evidence
                with patch('sslp_explorer.verify_case', side_effect=verify), patch('sslp_explorer.export_bundle') as package:
                    self.assertEqual(sslp_worker.run_job(directory, TOOLS/'explorer/models.example.json'),0)
                    package.assert_not_called()
                result=json.loads((directory/'output/report.json').read_text())
                self.assertEqual(result['verification'][0]['kernel']['status'], status)
                self.assertEqual(result['input_sha256'], class36.digest(data))
                self.assertFalse((directory/'output/verification-bundle.zip').exists())


if __name__ == '__main__':
    unittest.main()
